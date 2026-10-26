import V185TrunkScan23Chunk0575

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_3405873 : List Nat := [1, 2, 2, 3, 1, 3, 2, 1, 2, 1, 5]
def baseStart_3405873 : Nat := 118140960795 + 3405873 * 2 ^ 59
def prefixEnd_3405873 : Nat := 4983230072969 + 3 ^ 40 * 3405873 * 2
def baseEnd_3405873 : Nat := 1748849897170658239924181

theorem tailTrace_3405873 : CollatzResearch.WordTrace tailWord_3405873 prefixEnd_3405873 1748849897170658239924181 := by
  unfold tailWord_3405873
  simp only [CollatzResearch.WordTrace]
  refine ⟨124222393590111272643854273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82814929060074181762569515 124222393590111272643854273)
  ·
    refine ⟨93166795192583454482890705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124222393590111272643854273 93166795192583454482890705)
    ·
      refine ⟨69875096394437590862168029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93166795192583454482890705 69875096394437590862168029)
      ·
        refine ⟨26203161147914096573313011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69875096394437590862168029 26203161147914096573313011)
        ·
          refine ⟨39304741721871144859969517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26203161147914096573313011 39304741721871144859969517)
          ·
            refine ⟨14739278145701679322488569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39304741721871144859969517 14739278145701679322488569)
            ·
              refine ⟨11054458609276259491866427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14739278145701679322488569 11054458609276259491866427)
              ·
                refine ⟨16581687913914389237799641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11054458609276259491866427 16581687913914389237799641)
                ·
                  refine ⟨12436265935435791928349731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16581687913914389237799641 12436265935435791928349731)
                  ·
                    refine ⟨18654398903153687892524597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12436265935435791928349731 18654398903153687892524597)
                    ·
                      refine ⟨1748849897170658239924181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18654398903153687892524597 1748849897170658239924181)
                      ·
                        rfl

theorem cell23_3405873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 2, 1, 2, 1, 5].length) (baseStart_3405873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3405873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3405873 prefixEnd_3405873 := by exact prefixLift 3405873
  have htrace : WordTrace (prefixWord ++ tailWord_3405873) baseStart_3405873 baseEnd_3405873 := by
    simpa [prefixWord, tailWord_3405873, baseEnd_3405873] using wordTrace_append hprefix tailTrace_3405873
  have hstable : (prefixWord ++ tailWord_3405873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3405873).length < 2 ^ (prefixWord ++ tailWord_3405873).sum := by decide
  have hdescent : baseEnd_3405873 < baseStart_3405873 := by decide
  rcases family_descends (prefixWord ++ tailWord_3405873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3405874 : List Nat := [3, 2, 1, 1, 2, 4, 3, 1, 1, 3, 2]
def baseStart_3405874 : Nat := 118140960795 + 3405874 * 2 ^ 59
def prefixEnd_3405874 : Nat := 4983230072969 + 3 ^ 40 * 3405874 * 2
def baseEnd_3405874 : Nat := 1748850410651312736011677

theorem tailTrace_3405874 : CollatzResearch.WordTrace tailWord_3405874 prefixEnd_3405874 1748850410651312736011677 := by
  unfold tailWord_3405874
  simp only [CollatzResearch.WordTrace]
  refine ⟨31055607515776912453660169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82814953375405099876427117 31055607515776912453660169)
  ·
    refine ⟨23291705636832684340245127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31055607515776912453660169 23291705636832684340245127)
    ·
      refine ⟨34937558455249026510367691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23291705636832684340245127 34937558455249026510367691)
      ·
        refine ⟨52406337682873539765551537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34937558455249026510367691 52406337682873539765551537)
        ·
          refine ⟨39304753262155154824163653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52406337682873539765551537 39304753262155154824163653)
          ·
            refine ⟨7369641236654091529530685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39304753262155154824163653 7369641236654091529530685)
            ·
              refine ⟨2763615463745284323574007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7369641236654091529530685 2763615463745284323574007)
              ·
                refine ⟨4145423195617926485361011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2763615463745284323574007 4145423195617926485361011)
                ·
                  refine ⟨6218134793426889728041517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4145423195617926485361011 6218134793426889728041517)
                  ·
                    refine ⟨2331800547535083648015569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6218134793426889728041517 2331800547535083648015569)
                    ·
                      refine ⟨1748850410651312736011677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2331800547535083648015569 1748850410651312736011677)
                      ·
                        rfl

theorem cell23_3405874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 3, 1, 1, 3, 2].length) (baseStart_3405874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3405874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3405874 prefixEnd_3405874 := by exact prefixLift 3405874
  have htrace : WordTrace (prefixWord ++ tailWord_3405874) baseStart_3405874 baseEnd_3405874 := by
    simpa [prefixWord, tailWord_3405874, baseEnd_3405874] using wordTrace_append hprefix tailTrace_3405874
  have hstable : (prefixWord ++ tailWord_3405874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3405874).length < 2 ^ (prefixWord ++ tailWord_3405874).sum := by decide
  have hdescent : baseEnd_3405874 < baseStart_3405874 := by decide
  rcases family_descends (prefixWord ++ tailWord_3405874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3405887 : List Nat := [1, 1, 2, 2, 3, 1, 3, 4, 2, 2, 2]
def baseStart_3405887 : Nat := 118140960795 + 3405887 * 2 ^ 59
def prefixEnd_3405887 : Nat := 4983230072969 + 3 ^ 40 * 3405887 * 2
def baseEnd_3405887 : Nat := 1748857085899821185149117

theorem tailTrace_3405887 : CollatzResearch.WordTrace tailWord_3405887 prefixEnd_3405887 1748857085899821185149117 := by
  unfold tailWord_3405887
  simp only [CollatzResearch.WordTrace]
  refine ⟨124222904212060553034863915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82815269474707035356575943 124222904212060553034863915)
  ·
    refine ⟨186334356318090829552295873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124222904212060553034863915 186334356318090829552295873)
    ·
      refine ⟨139750767238568122164221905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 186334356318090829552295873 139750767238568122164221905)
      ·
        refine ⟨104813075428926091623166429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 139750767238568122164221905 104813075428926091623166429)
        ·
          refine ⟨39304903285847284358687411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 104813075428926091623166429 39304903285847284358687411)
          ·
            refine ⟨58957354928770926538031117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39304903285847284358687411 58957354928770926538031117)
            ·
              refine ⟨22109008098289097451761669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58957354928770926538031117 22109008098289097451761669)
              ·
                refine ⟨4145439018429205772205313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22109008098289097451761669 4145439018429205772205313)
                ·
                  refine ⟨3109079263821904329153985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4145439018429205772205313 3109079263821904329153985)
                  ·
                    refine ⟨2331809447866428246865489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3109079263821904329153985 2331809447866428246865489)
                    ·
                      refine ⟨1748857085899821185149117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2331809447866428246865489 1748857085899821185149117)
                      ·
                        rfl

theorem cell23_3405887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 3, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 3, 4, 2, 2, 2].length) (baseStart_3405887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3405887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3405887 prefixEnd_3405887 := by exact prefixLift 3405887
  have htrace : WordTrace (prefixWord ++ tailWord_3405887) baseStart_3405887 baseEnd_3405887 := by
    simpa [prefixWord, tailWord_3405887, baseEnd_3405887] using wordTrace_append hprefix tailTrace_3405887
  have hstable : (prefixWord ++ tailWord_3405887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3405887).length < 2 ^ (prefixWord ++ tailWord_3405887).sum := by decide
  have hdescent : baseEnd_3405887 < baseStart_3405887 := by decide
  rcases family_descends (prefixWord ++ tailWord_3405887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3405903 : List Nat := [1, 1, 2, 1, 1, 2, 2, 5, 2, 3, 3]
def baseStart_3405903 : Nat := 118140960795 + 3405903 * 2 ^ 59
def prefixEnd_3405903 : Nat := 4983230072969 + 3 ^ 40 * 3405903 * 2
def baseEnd_3405903 : Nat := 1748865301590293122549043

theorem tailTrace_3405903 : CollatzResearch.WordTrace tailWord_3405903 prefixEnd_3405903 1748865301590293122549043 := by
  unfold tailWord_3405903
  simp only [CollatzResearch.WordTrace]
  refine ⟨124223487780002587767446363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82815658520001725178297575 124223487780002587767446363)
  ·
    refine ⟨186335231670003881651169545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124223487780002587767446363 186335231670003881651169545)
    ·
      refine ⟨139751423752502911238377159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 186335231670003881651169545 139751423752502911238377159)
      ·
        refine ⟨209627135628754366857565739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139751423752502911238377159 209627135628754366857565739)
        ·
          refine ⟨314440703443131550286348609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 209627135628754366857565739 314440703443131550286348609)
          ·
            refine ⟨235830527582348662714761457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 314440703443131550286348609 235830527582348662714761457)
            ·
              refine ⟨176872895686761497036071093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 235830527582348662714761457 176872895686761497036071093)
              ·
                refine ⟨16581833970633890347131665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 176872895686761497036071093 16581833970633890347131665)
                ·
                  refine ⟨12436375477975417760348749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16581833970633890347131665 12436375477975417760348749)
                  ·
                    refine ⟨4663640804240781660130781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12436375477975417760348749 4663640804240781660130781)
                    ·
                      refine ⟨1748865301590293122549043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4663640804240781660130781 1748865301590293122549043)
                      ·
                        rfl

theorem cell23_3405903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 5, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 5, 2, 3, 3].length) (baseStart_3405903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3405903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3405903 prefixEnd_3405903 := by exact prefixLift 3405903
  have htrace : WordTrace (prefixWord ++ tailWord_3405903) baseStart_3405903 baseEnd_3405903 := by
    simpa [prefixWord, tailWord_3405903, baseEnd_3405903] using wordTrace_append hprefix tailTrace_3405903
  have hstable : (prefixWord ++ tailWord_3405903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3405903).length < 2 ^ (prefixWord ++ tailWord_3405903).sum := by decide
  have hdescent : baseEnd_3405903 < baseStart_3405903 := by decide
  rcases family_descends (prefixWord ++ tailWord_3405903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3405960 : List Nat := [2, 1, 3, 4, 1, 1, 1, 2, 1, 3, 4]
def baseStart_3405960 : Nat := 118140960795 + 3405960 * 2 ^ 59
def prefixEnd_3405960 : Nat := 4983230072969 + 3 ^ 40 * 3405960 * 2
def baseEnd_3405960 : Nat := 1748894569987599399536281

theorem tailTrace_3405960 : CollatzResearch.WordTrace tailWord_3405960 prefixEnd_3405960 1748894569987599399536281 := by
  unfold tailWord_3405960
  simp only [CollatzResearch.WordTrace]
  refine ⟨62112783370398043251135667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82817044493864057668180889 62112783370398043251135667)
  ·
    refine ⟨93169175055597064876703501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62112783370398043251135667 93169175055597064876703501)
    ·
      refine ⟨34938440645848899328763813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93169175055597064876703501 34938440645848899328763813)
      ·
        refine ⟨6550957621096668624143215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34938440645848899328763813 6550957621096668624143215)
        ·
          refine ⟨9826436431645002936214823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6550957621096668624143215 9826436431645002936214823)
          ·
            refine ⟨14739654647467504404322235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9826436431645002936214823 14739654647467504404322235)
            ·
              refine ⟨22109481971201256606483353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14739654647467504404322235 22109481971201256606483353)
              ·
                refine ⟨16582111478400942454862515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22109481971201256606483353 16582111478400942454862515)
                ·
                  refine ⟨24873167217601413682293773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16582111478400942454862515 24873167217601413682293773)
                  ·
                    refine ⟨9327437706600530130860165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24873167217601413682293773 9327437706600530130860165)
                    ·
                      refine ⟨1748894569987599399536281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9327437706600530130860165 1748894569987599399536281)
                      ·
                        rfl

theorem cell23_3405960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 1, 2, 1, 3, 4].length) (baseStart_3405960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3405960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3405960 prefixEnd_3405960 := by exact prefixLift 3405960
  have htrace : WordTrace (prefixWord ++ tailWord_3405960) baseStart_3405960 baseEnd_3405960 := by
    simpa [prefixWord, tailWord_3405960, baseEnd_3405960] using wordTrace_append hprefix tailTrace_3405960
  have hstable : (prefixWord ++ tailWord_3405960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3405960).length < 2 ^ (prefixWord ++ tailWord_3405960).sum := by decide
  have hdescent : baseEnd_3405960 < baseStart_3405960 := by decide
  rcases family_descends (prefixWord ++ tailWord_3405960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3405973 : List Nat := [1, 3, 2, 1, 1, 1, 3, 1, 2, 4, 4]
def baseStart_3405973 : Nat := 118140960795 + 3405973 * 2 ^ 59
def prefixEnd_3405973 : Nat := 4983230072969 + 3 ^ 40 * 3405973 * 2
def baseEnd_3405973 : Nat := 1748901245236107848673721

theorem tailTrace_3405973 : CollatzResearch.WordTrace tailWord_3405973 prefixEnd_3405973 1748901245236107848673721 := by
  unfold tailWord_3405973
  simp only [CollatzResearch.WordTrace]
  refine ⟨124226040889748989722494573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82817360593165993148329715 124226040889748989722494573)
  ·
    refine ⟨46584765333655871145935465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 124226040889748989722494573 46584765333655871145935465)
    ·
      refine ⟨34938574000241903359451599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46584765333655871145935465 34938574000241903359451599)
      ·
        refine ⟨52407861000362855039177399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34938574000241903359451599 52407861000362855039177399)
        ·
          refine ⟨78611791500544282558766099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52407861000362855039177399 78611791500544282558766099)
          ·
            refine ⟨117917687250816423838149149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78611791500544282558766099 117917687250816423838149149)
            ·
              refine ⟨44219132719056158939305931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 117917687250816423838149149 44219132719056158939305931)
              ·
                refine ⟨66328699078584238408958897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44219132719056158939305931 66328699078584238408958897)
                ·
                  refine ⟨49746524308938178806719173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 66328699078584238408958897 49746524308938178806719173)
                  ·
                    refine ⟨9327473307925908526259845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 49746524308938178806719173 9327473307925908526259845)
                    ·
                      refine ⟨1748901245236107848673721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9327473307925908526259845 1748901245236107848673721)
                      ·
                        rfl

theorem cell23_3405973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 1, 2, 4, 4].length) (baseStart_3405973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3405973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3405973 prefixEnd_3405973 := by exact prefixLift 3405973
  have htrace : WordTrace (prefixWord ++ tailWord_3405973) baseStart_3405973 baseEnd_3405973 := by
    simpa [prefixWord, tailWord_3405973, baseEnd_3405973] using wordTrace_append hprefix tailTrace_3405973
  have hstable : (prefixWord ++ tailWord_3405973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3405973).length < 2 ^ (prefixWord ++ tailWord_3405973).sum := by decide
  have hdescent : baseEnd_3405973 < baseStart_3405973 := by decide
  rcases family_descends (prefixWord ++ tailWord_3405973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3405980 : List Nat := [2, 2, 3, 2, 1, 1, 1, 3, 1, 4, 3]
def baseStart_3405980 : Nat := 118140960795 + 3405980 * 2 ^ 59
def prefixEnd_3405980 : Nat := 4983230072969 + 3 ^ 40 * 3405980 * 2
def baseEnd_3405980 : Nat := 1748904839600689321286189

theorem tailTrace_3405980 : CollatzResearch.WordTrace tailWord_3405980 prefixEnd_3405980 1748904839600689321286189 := by
  unfold tailWord_3405980
  simp only [CollatzResearch.WordTrace]
  refine ⟨62113148100361814958999697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82817530800482419945332929 62113148100361814958999697)
  ·
    refine ⟨46584861075271361219249773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62113148100361814958999697 46584861075271361219249773)
    ·
      refine ⟨17469322903226760457218665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46584861075271361219249773 17469322903226760457218665)
      ·
        refine ⟨13101992177420070342913999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17469322903226760457218665 13101992177420070342913999)
        ·
          refine ⟨19652988266130105514370999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13101992177420070342913999 19652988266130105514370999)
          ·
            refine ⟨29479482399195158271556499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19652988266130105514370999 29479482399195158271556499)
            ·
              refine ⟨44219223598792737407334749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29479482399195158271556499 44219223598792737407334749)
              ·
                refine ⟨16582208849547276527750531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44219223598792737407334749 16582208849547276527750531)
                ·
                  refine ⟨24873313274320914791625797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16582208849547276527750531 24873313274320914791625797)
                  ·
                    refine ⟨4663746238935171523429837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24873313274320914791625797 4663746238935171523429837)
                    ·
                      refine ⟨1748904839600689321286189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4663746238935171523429837 1748904839600689321286189)
                      ·
                        rfl

theorem cell23_3405980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 3, 1, 4, 3].length) (baseStart_3405980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3405980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3405980 prefixEnd_3405980 := by exact prefixLift 3405980
  have htrace : WordTrace (prefixWord ++ tailWord_3405980) baseStart_3405980 baseEnd_3405980 := by
    simpa [prefixWord, tailWord_3405980, baseEnd_3405980] using wordTrace_append hprefix tailTrace_3405980
  have hstable : (prefixWord ++ tailWord_3405980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3405980).length < 2 ^ (prefixWord ++ tailWord_3405980).sum := by decide
  have hdescent : baseEnd_3405980 < baseStart_3405980 := by decide
  rcases family_descends (prefixWord ++ tailWord_3405980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3405994 : List Nat := [3, 1, 5, 1, 2, 1, 1, 2, 2, 1, 4]
def baseStart_3405994 : Nat := 118140960795 + 3405994 * 2 ^ 59
def prefixEnd_3405994 : Nat := 4983230072969 + 3 ^ 40 * 3405994 * 2
def baseEnd_3405994 : Nat := 1748912028329852266511125

theorem tailTrace_3405994 : CollatzResearch.WordTrace tailWord_3405994 prefixEnd_3405994 1748912028329852266511125 := by
  unfold tailWord_3405994
  simp only [CollatzResearch.WordTrace]
  refine ⟨31056701705668227577252259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82817871215115273539339357 31056701705668227577252259)
  ·
    refine ⟨46585052558502341365878389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31056701705668227577252259 46585052558502341365878389)
    ·
      refine ⟨4367348677359594503051099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 46585052558502341365878389 4367348677359594503051099)
      ·
        refine ⟨6551023016039391754576649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4367348677359594503051099 6551023016039391754576649)
        ·
          refine ⟨4913267262029543815932487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6551023016039391754576649 4913267262029543815932487)
          ·
            refine ⟨7369900893044315723898731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4913267262029543815932487 7369900893044315723898731)
            ·
              refine ⟨11054851339566473585848097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7369900893044315723898731 11054851339566473585848097)
              ·
                refine ⟨8291138504674855189386073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11054851339566473585848097 8291138504674855189386073)
                ·
                  refine ⟨6218353878506141392039555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8291138504674855189386073 6218353878506141392039555)
                  ·
                    refine ⟨9327530817759212088059333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6218353878506141392039555 9327530817759212088059333)
                    ·
                      refine ⟨1748912028329852266511125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9327530817759212088059333 1748912028329852266511125)
                      ·
                        rfl

theorem cell23_3405994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 1, 2, 2, 1, 4].length) (baseStart_3405994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3405994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3405994 prefixEnd_3405994 := by exact prefixLift 3405994
  have htrace : WordTrace (prefixWord ++ tailWord_3405994) baseStart_3405994 baseEnd_3405994 := by
    simpa [prefixWord, tailWord_3405994, baseEnd_3405994] using wordTrace_append hprefix tailTrace_3405994
  have hstable : (prefixWord ++ tailWord_3405994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3405994).length < 2 ^ (prefixWord ++ tailWord_3405994).sum := by decide
  have hdescent : baseEnd_3405994 < baseStart_3405994 := by decide
  rcases family_descends (prefixWord ++ tailWord_3405994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3405997 : List Nat := [1, 5, 2, 1, 2, 1, 1, 1, 4, 2, 3]
def baseStart_3405997 : Nat := 118140960795 + 3405997 * 2 ^ 59
def prefixEnd_3405997 : Nat := 4983230072969 + 3 ^ 40 * 3405997 * 2
def baseEnd_3405997 : Nat := 1748913568771815754773611

theorem tailTrace_3405997 : CollatzResearch.WordTrace tailWord_3405997 prefixEnd_3405997 1748913568771815754773611 := by
  unfold tailWord_3405997
  simp only [CollatzResearch.WordTrace]
  refine ⟨124226916241662041821368245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82817944161108027880912163 124226916241662041821368245)
  ·
    refine ⟨11646273397655816420753273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 124226916241662041821368245 11646273397655816420753273)
    ·
      refine ⟨8734705048241862315564955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11646273397655816420753273 8734705048241862315564955)
      ·
        refine ⟨13102057572362793473347433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8734705048241862315564955 13102057572362793473347433)
        ·
          refine ⟨9826543179272095105010575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13102057572362793473347433 9826543179272095105010575)
          ·
            refine ⟨14739814768908142657515863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9826543179272095105010575 14739814768908142657515863)
            ·
              refine ⟨22109722153362213986273795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14739814768908142657515863 22109722153362213986273795)
              ·
                refine ⟨33164583230043320979410693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22109722153362213986273795 33164583230043320979410693)
                ·
                  refine ⟨6218359355633122683639505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33164583230043320979410693 6218359355633122683639505)
                  ·
                    refine ⟨4663769516724842012729629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6218359355633122683639505 4663769516724842012729629)
                    ·
                      refine ⟨1748913568771815754773611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4663769516724842012729629 1748913568771815754773611)
                      ·
                        rfl

theorem cell23_3405997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 1, 1, 4, 2, 3].length) (baseStart_3405997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3405997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3405997 prefixEnd_3405997 := by exact prefixLift 3405997
  have htrace : WordTrace (prefixWord ++ tailWord_3405997) baseStart_3405997 baseEnd_3405997 := by
    simpa [prefixWord, tailWord_3405997, baseEnd_3405997] using wordTrace_append hprefix tailTrace_3405997
  have hstable : (prefixWord ++ tailWord_3405997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3405997).length < 2 ^ (prefixWord ++ tailWord_3405997).sum := by decide
  have hdescent : baseEnd_3405997 < baseStart_3405997 := by decide
  rcases family_descends (prefixWord ++ tailWord_3405997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3406013 : List Nat := [1, 4, 1, 2, 1, 1, 1, 1, 2, 9]
def baseStart_3406013 : Nat := 118140960795 + 3406013 * 2 ^ 59
def prefixEnd_3406013 : Nat := 4983230072969 + 3 ^ 40 * 3406013 * 2
def baseEnd_3406013 : Nat := 582973928154095897391179

theorem tailTrace_3406013 : CollatzResearch.WordTrace tailWord_3406013 prefixEnd_3406013 582973928154095897391179 := by
  unfold tailWord_3406013
  simp only [CollatzResearch.WordTrace]
  refine ⟨124227499809604076553950693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82818333206402717702633795 124227499809604076553950693)
  ·
    refine ⟨23292656214300764353865755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 124227499809604076553950693 23292656214300764353865755)
    ·
      refine ⟨34938984321451146530798633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23292656214300764353865755 34938984321451146530798633)
      ·
        refine ⟨26204238241088359898098975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34938984321451146530798633 26204238241088359898098975)
        ·
          refine ⟨39306357361632539847148463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26204238241088359898098975 39306357361632539847148463)
          ·
            refine ⟨58959536042448809770722695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39306357361632539847148463 58959536042448809770722695)
            ·
              refine ⟨88439304063673214656084043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58959536042448809770722695 88439304063673214656084043)
              ·
                refine ⟨132658956095509821984126065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 88439304063673214656084043 132658956095509821984126065)
                ·
                  refine ⟨99494217071632366488094549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 132658956095509821984126065 99494217071632366488094549)
                  ·
                    refine ⟨582973928154095897391179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 99494217071632366488094549 582973928154095897391179)
                    ·
                      rfl

theorem cell23_3406013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 1, 2, 9].length) (baseStart_3406013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3406013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3406013 prefixEnd_3406013 := by exact prefixLift 3406013
  have htrace : WordTrace (prefixWord ++ tailWord_3406013) baseStart_3406013 baseEnd_3406013 := by
    simpa [prefixWord, tailWord_3406013, baseEnd_3406013] using wordTrace_append hprefix tailTrace_3406013
  have hstable : (prefixWord ++ tailWord_3406013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3406013).length < 2 ^ (prefixWord ++ tailWord_3406013).sum := by decide
  have hdescent : baseEnd_3406013 < baseStart_3406013 := by decide
  rcases family_descends (prefixWord ++ tailWord_3406013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3406043 : List Nat := [1, 1, 1, 1, 1, 1, 1, 7, 3, 6]
def baseStart_3406043 : Nat := 118140960795 + 3406043 * 2 ^ 59
def prefixEnd_3406043 : Nat := 4983230072969 + 3 ^ 40 * 3406043 * 2
def baseEnd_3406043 : Nat := 582979062960640858266133

theorem tailTrace_3406043 : CollatzResearch.WordTrace tailWord_3406043 prefixEnd_3406043 582979062960640858266133 := by
  unfold tailWord_3406043
  simp only [CollatzResearch.WordTrace]
  refine ⟨124228593999495391677542783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82819062666330261118361855 124228593999495391677542783)
  ·
    refine ⟨186342890999243087516314175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124228593999495391677542783 186342890999243087516314175)
    ·
      refine ⟨279514336498864631274471263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186342890999243087516314175 279514336498864631274471263)
      ·
        refine ⟨419271504748296946911706895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 279514336498864631274471263 419271504748296946911706895)
        ·
          refine ⟨628907257122445420367560343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 419271504748296946911706895 628907257122445420367560343)
          ·
            refine ⟨943360885683668130551340515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 628907257122445420367560343 943360885683668130551340515)
            ·
              refine ⟨1415041328525502195827010773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 943360885683668130551340515 1415041328525502195827010773)
              ·
                refine ⟨33165031137316457714695565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1415041328525502195827010773 33165031137316457714695565)
                ·
                  refine ⟨12436886676493671643010837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33165031137316457714695565 12436886676493671643010837)
                  ·
                    refine ⟨582979062960640858266133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12436886676493671643010837 582979062960640858266133)
                    ·
                      rfl

theorem cell23_3406043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 7, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 7, 3, 6].length) (baseStart_3406043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3406043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3406043 prefixEnd_3406043 := by exact prefixLift 3406043
  have htrace : WordTrace (prefixWord ++ tailWord_3406043) baseStart_3406043 baseEnd_3406043 := by
    simpa [prefixWord, tailWord_3406043, baseEnd_3406043] using wordTrace_append hprefix tailTrace_3406043
  have hstable : (prefixWord ++ tailWord_3406043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3406043).length < 2 ^ (prefixWord ++ tailWord_3406043).sum := by decide
  have hdescent : baseEnd_3406043 < baseStart_3406043 := by decide
  rcases family_descends (prefixWord ++ tailWord_3406043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3406073 : List Nat := [1, 2, 1, 3, 1, 1, 2, 12]
def baseStart_3406073 : Nat := 118140960795 + 3406073 * 2 ^ 59
def prefixEnd_3406073 : Nat := 4983230072969 + 3 ^ 40 * 3406073 * 2
def baseEnd_3406073 : Nat := 64776021974131757682343

theorem tailTrace_3406073 : CollatzResearch.WordTrace tailWord_3406073 prefixEnd_3406073 64776021974131757682343 := by
  unfold tailWord_3406073
  simp only [CollatzResearch.WordTrace]
  refine ⟨124229688189386706801134873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82819792126257804534089915 124229688189386706801134873)
  ·
    refine ⟨93172266142040030100851155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124229688189386706801134873 93172266142040030100851155)
    ·
      refine ⟨139758399213060045151276733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93172266142040030100851155 139758399213060045151276733)
      ·
        refine ⟨52409399704897516931728775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 139758399213060045151276733 52409399704897516931728775)
        ·
          refine ⟨78614099557346275397593163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52409399704897516931728775 78614099557346275397593163)
          ·
            refine ⟨117921149336019413096389745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78614099557346275397593163 117921149336019413096389745)
            ·
              refine ⟨88440862002014559822292309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 117921149336019413096389745 88440862002014559822292309)
              ·
                refine ⟨64776021974131757682343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 88440862002014559822292309 64776021974131757682343)
                ·
                  rfl

theorem cell23_3406073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 12].length) (baseStart_3406073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3406073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3406073 prefixEnd_3406073 := by exact prefixLift 3406073
  have htrace : WordTrace (prefixWord ++ tailWord_3406073) baseStart_3406073 baseEnd_3406073 := by
    simpa [prefixWord, tailWord_3406073, baseEnd_3406073] using wordTrace_append hprefix tailTrace_3406073
  have hstable : (prefixWord ++ tailWord_3406073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3406073).length < 2 ^ (prefixWord ++ tailWord_3406073).sum := by decide
  have hdescent : baseEnd_3406073 < baseStart_3406073 := by decide
  rcases family_descends (prefixWord ++ tailWord_3406073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3406080 : List Nat := [2, 1, 1, 2, 1, 1, 5, 3, 1, 2, 4]
def baseStart_3406080 : Nat := 118140960795 + 3406080 * 2 ^ 59
def prefixEnd_3406080 : Nat := 4983230072969 + 3 ^ 40 * 3406080 * 2
def baseEnd_3406080 : Nat := 1748956187666138930035729

theorem tailTrace_3406080 : CollatzResearch.WordTrace tailWord_3406080 prefixEnd_3406080 1748956187666138930035729 := by
  unfold tailWord_3406080
  simp only [CollatzResearch.WordTrace]
  refine ⟨62114971750180673498319847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82819962333574231331093129 62114971750180673498319847)
  ·
    refine ⟨93172457625271010247479771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62114971750180673498319847 93172457625271010247479771)
    ·
      refine ⟨139758686437906515371219657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93172457625271010247479771 139758686437906515371219657)
      ·
        refine ⟨104819014828429886528414743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 139758686437906515371219657 104819014828429886528414743)
        ·
          refine ⟨157228522242644829792622115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104819014828429886528414743 157228522242644829792622115)
          ·
            refine ⟨235842783363967244688933173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 157228522242644829792622115 235842783363967244688933173)
            ·
              refine ⟨22110260940371929189587485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 235842783363967244688933173 22110260940371929189587485)
              ·
                refine ⟨8291347852639473446095307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22110260940371929189587485 8291347852639473446095307)
                ·
                  refine ⟨12437021778959210169142961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8291347852639473446095307 12437021778959210169142961)
                  ·
                    refine ⟨9327766334219407626857221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12437021778959210169142961 9327766334219407626857221)
                    ·
                      refine ⟨1748956187666138930035729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9327766334219407626857221 1748956187666138930035729)
                      ·
                        rfl

theorem cell23_3406080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 5, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 5, 3, 1, 2, 4].length) (baseStart_3406080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3406080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3406080 prefixEnd_3406080 := by exact prefixLift 3406080
  have htrace : WordTrace (prefixWord ++ tailWord_3406080) baseStart_3406080 baseEnd_3406080 := by
    simpa [prefixWord, tailWord_3406080, baseEnd_3406080] using wordTrace_append hprefix tailTrace_3406080
  have hstable : (prefixWord ++ tailWord_3406080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3406080).length < 2 ^ (prefixWord ++ tailWord_3406080).sum := by decide
  have hdescent : baseEnd_3406080 < baseStart_3406080 := by decide
  rcases family_descends (prefixWord ++ tailWord_3406080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3406101 : List Nat := [1, 3, 2, 1, 2, 1, 3, 5, 1, 2, 2]
def baseStart_3406101 : Nat := 118140960795 + 3406101 * 2 ^ 59
def prefixEnd_3406101 : Nat := 4983230072969 + 3 ^ 40 * 3406101 * 2
def baseEnd_3406101 : Nat := 1748966970759883347873133

theorem tailTrace_3406101 : CollatzResearch.WordTrace tailWord_3406101 prefixEnd_3406101 1748966970759883347873133 := by
  unfold tailWord_3406101
  simp only [CollatzResearch.WordTrace]
  refine ⟨124230709433285267583154157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82820472955523511722102771 124230709433285267583154157)
  ·
    refine ⟨46586516037481975343682809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 124230709433285267583154157 46586516037481975343682809)
    ·
      refine ⟨34939887028111481507762107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46586516037481975343682809 34939887028111481507762107)
      ·
        refine ⟨52409830542167222261643161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34939887028111481507762107 52409830542167222261643161)
        ·
          refine ⟨39307372906625416696232371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52409830542167222261643161 39307372906625416696232371)
          ·
            refine ⟨58961059359938125044348557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39307372906625416696232371 58961059359938125044348557)
            ·
              refine ⟨22110397259976796891630709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58961059359938125044348557 22110397259976796891630709)
              ·
                refine ⟨2072849743122824708590379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 22110397259976796891630709 2072849743122824708590379)
                ·
                  refine ⟨3109274614684237062885569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2072849743122824708590379 3109274614684237062885569)
                  ·
                    refine ⟨2331955961013177797164177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3109274614684237062885569 2331955961013177797164177)
                    ·
                      refine ⟨1748966970759883347873133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2331955961013177797164177 1748966970759883347873133)
                      ·
                        rfl

theorem cell23_3406101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 3, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 3, 5, 1, 2, 2].length) (baseStart_3406101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3406101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3406101 prefixEnd_3406101 := by exact prefixLift 3406101
  have htrace : WordTrace (prefixWord ++ tailWord_3406101) baseStart_3406101 baseEnd_3406101 := by
    simpa [prefixWord, tailWord_3406101, baseEnd_3406101] using wordTrace_append hprefix tailTrace_3406101
  have hstable : (prefixWord ++ tailWord_3406101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3406101).length < 2 ^ (prefixWord ++ tailWord_3406101).sum := by decide
  have hdescent : baseEnd_3406101 < baseStart_3406101 := by decide
  rcases family_descends (prefixWord ++ tailWord_3406101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3406127 : List Nat := [1, 1, 2, 1, 2, 1, 4, 1, 5, 3, 2]
def baseStart_3406127 : Nat := 118140960795 + 3406127 * 2 ^ 59
def prefixEnd_3406127 : Nat := 4983230072969 + 3 ^ 40 * 3406127 * 2
def baseEnd_3406127 : Nat := 1748980321256900246148013

theorem tailTrace_3406127 : CollatzResearch.WordTrace tailWord_3406127 prefixEnd_3406127 1748980321256900246148013 := by
  unfold tailWord_3406127
  simp only [CollatzResearch.WordTrace]
  refine ⟨124231657731191074023600635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82821105154127382682400423 124231657731191074023600635)
  ·
    refine ⟨186347486596786611035400953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124231657731191074023600635 186347486596786611035400953)
    ·
      refine ⟨139760614947589958276550715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 186347486596786611035400953 139760614947589958276550715)
      ·
        refine ⟨209640922421384937414826073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139760614947589958276550715 209640922421384937414826073)
        ·
          refine ⟨157230691816038703061119555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 209640922421384937414826073 157230691816038703061119555)
          ·
            refine ⟨235846037724058054591679333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 157230691816038703061119555 235846037724058054591679333)
            ·
              refine ⟨44221132073260885235939875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 235846037724058054591679333 44221132073260885235939875)
              ·
                refine ⟨66331698109891327853909813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44221132073260885235939875 66331698109891327853909813)
                ·
                  refine ⟨6218596697802311986304045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 66331698109891327853909813 6218596697802311986304045)
                  ·
                    refine ⟨2331973761675866994864017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6218596697802311986304045 2331973761675866994864017)
                    ·
                      refine ⟨1748980321256900246148013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2331973761675866994864017 1748980321256900246148013)
                      ·
                        rfl

theorem cell23_3406127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 1, 5, 3, 2].length) (baseStart_3406127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3406127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3406127 prefixEnd_3406127 := by exact prefixLift 3406127
  have htrace : WordTrace (prefixWord ++ tailWord_3406127) baseStart_3406127 baseEnd_3406127 := by
    simpa [prefixWord, tailWord_3406127, baseEnd_3406127] using wordTrace_append hprefix tailTrace_3406127
  have hstable : (prefixWord ++ tailWord_3406127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3406127).length < 2 ^ (prefixWord ++ tailWord_3406127).sum := by decide
  have hdescent : baseEnd_3406127 < baseStart_3406127 := by decide
  rcases family_descends (prefixWord ++ tailWord_3406127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3406160 : List Nat := [2, 1, 1, 1, 1, 6, 1, 1, 1, 3, 5]
def baseStart_3406160 : Nat := 118140960795 + 3406160 * 2 ^ 59
def prefixEnd_3406160 : Nat := 4983230072969 + 3 ^ 40 * 3406160 * 2
def baseEnd_3406160 : Nat := 1748997266118498617035361

theorem tailTrace_3406160 : CollatzResearch.WordTrace tailWord_3406160 prefixEnd_3406160 1748997266118498617035361 := by
  unfold tailWord_3406160
  simp only [CollatzResearch.WordTrace]
  refine ⟨62116430670035760329775967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82821907560047680439701289 62116430670035760329775967)
  ·
    refine ⟨93174646005053640494663951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62116430670035760329775967 93174646005053640494663951)
    ·
      refine ⟨139761969007580460741995927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93174646005053640494663951 139761969007580460741995927)
      ·
        refine ⟨209642953511370691112993891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139761969007580460741995927 209642953511370691112993891)
        ·
          refine ⟨314464430267056036669490837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 209642953511370691112993891 314464430267056036669490837)
          ·
            refine ⟨14740520168768251718882383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 314464430267056036669490837 14740520168768251718882383)
            ·
              refine ⟨22110780253152377578323575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14740520168768251718882383 22110780253152377578323575)
              ·
                refine ⟨33166170379728566367485363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22110780253152377578323575 33166170379728566367485363)
                ·
                  refine ⟨49749255569592849551228045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33166170379728566367485363 49749255569592849551228045)
                  ·
                    refine ⟨18655970838597318581710517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 49749255569592849551228045 18655970838597318581710517)
                    ·
                      refine ⟨1748997266118498617035361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18655970838597318581710517 1748997266118498617035361)
                      ·
                        rfl

theorem cell23_3406160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 1, 1, 1, 3, 5].length) (baseStart_3406160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3406160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3406160 prefixEnd_3406160 := by exact prefixLift 3406160
  have htrace : WordTrace (prefixWord ++ tailWord_3406160) baseStart_3406160 baseEnd_3406160 := by
    simpa [prefixWord, tailWord_3406160, baseEnd_3406160] using wordTrace_append hprefix tailTrace_3406160
  have hstable : (prefixWord ++ tailWord_3406160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3406160).length < 2 ^ (prefixWord ++ tailWord_3406160).sum := by decide
  have hdescent : baseEnd_3406160 < baseStart_3406160 := by decide
  rcases family_descends (prefixWord ++ tailWord_3406160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3406234 : List Nat := [3, 1, 1, 4, 1, 2, 1, 1, 2, 5, 2]
def baseStart_3406234 : Nat := 118140960795 + 3406234 * 2 ^ 59
def prefixEnd_3406234 : Nat := 4983230072969 + 3 ^ 40 * 3406234 * 2
def baseEnd_3406234 : Nat := 1749035263686931327510021

theorem tailTrace_3406234 : CollatzResearch.WordTrace tailWord_3406234 prefixEnd_3406234 1749035263686931327510021 := by
  unfold tailWord_3406234
  simp only [CollatzResearch.WordTrace]
  refine ⟨31058890085450857824436439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82823706894535620865163837 31058890085450857824436439)
  ·
    refine ⟨46588335128176286736654659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31058890085450857824436439 46588335128176286736654659)
    ·
      refine ⟨69882502692264430104981989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46588335128176286736654659 69882502692264430104981989)
      ·
        refine ⟨13102969254799580644684123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 69882502692264430104981989 13102969254799580644684123)
        ·
          refine ⟨19654453882199370967026185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13102969254799580644684123 19654453882199370967026185)
          ·
            refine ⟨14740840411649528225269639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19654453882199370967026185 14740840411649528225269639)
            ·
              refine ⟨22111260617474292337904459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14740840411649528225269639 22111260617474292337904459)
              ·
                refine ⟨33166890926211438506856689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22111260617474292337904459 33166890926211438506856689)
                ·
                  refine ⟨24875168194658578880142517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33166890926211438506856689 24875168194658578880142517)
                  ·
                    refine ⟨2332047018249241770013361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 24875168194658578880142517 2332047018249241770013361)
                    ·
                      refine ⟨1749035263686931327510021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2332047018249241770013361 1749035263686931327510021)
                      ·
                        rfl

theorem cell23_3406234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 1, 1, 2, 5, 2].length) (baseStart_3406234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3406234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3406234 prefixEnd_3406234 := by exact prefixLift 3406234
  have htrace : WordTrace (prefixWord ++ tailWord_3406234) baseStart_3406234 baseEnd_3406234 := by
    simpa [prefixWord, tailWord_3406234, baseEnd_3406234] using wordTrace_append hprefix tailTrace_3406234
  have hstable : (prefixWord ++ tailWord_3406234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3406234).length < 2 ^ (prefixWord ++ tailWord_3406234).sum := by decide
  have hdescent : baseEnd_3406234 < baseStart_3406234 := by decide
  rcases family_descends (prefixWord ++ tailWord_3406234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3406241 : List Nat := [1, 2, 3, 5, 1, 1, 1, 1, 2, 3, 3]
def baseStart_3406241 : Nat := 118140960795 + 3406241 * 2 ^ 59
def prefixEnd_3406241 : Nat := 4983230072969 + 3 ^ 40 * 3406241 * 2
def baseEnd_3406241 : Nat := 1749038858051512800122489

theorem tailTrace_3406241 : CollatzResearch.WordTrace tailWord_3406241 prefixEnd_3406241 1749038858051512800122489 := by
  unfold tailWord_3406241
  simp only [CollatzResearch.WordTrace]
  refine ⟨124235815652778071493250577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82823877101852047662167051 124235815652778071493250577)
  ·
    refine ⟨93176861739583553619937933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124235815652778071493250577 93176861739583553619937933)
    ·
      refine ⟨34941323152343832607476725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93176861739583553619937933 34941323152343832607476725)
      ·
        refine ⟨3275749045532234306950943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 34941323152343832607476725 3275749045532234306950943)
        ·
          refine ⟨4913623568298351460426415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3275749045532234306950943 4913623568298351460426415)
          ·
            refine ⟨7370435352447527190639623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4913623568298351460426415 7370435352447527190639623)
            ·
              refine ⟨11055653028671290785959435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7370435352447527190639623 11055653028671290785959435)
              ·
                refine ⟨16583479543006936178939153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11055653028671290785959435 16583479543006936178939153)
                ·
                  refine ⟨12437609657255202134204365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16583479543006936178939153 12437609657255202134204365)
                  ·
                    refine ⟨4664103621470700800326637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12437609657255202134204365 4664103621470700800326637)
                    ·
                      refine ⟨1749038858051512800122489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4664103621470700800326637 1749038858051512800122489)
                      ·
                        rfl

theorem cell23_3406241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 1, 1, 2, 3, 3].length) (baseStart_3406241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3406241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3406241 prefixEnd_3406241 := by exact prefixLift 3406241
  have htrace : WordTrace (prefixWord ++ tailWord_3406241) baseStart_3406241 baseEnd_3406241 := by
    simpa [prefixWord, tailWord_3406241, baseEnd_3406241] using wordTrace_append hprefix tailTrace_3406241
  have hstable : (prefixWord ++ tailWord_3406241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3406241).length < 2 ^ (prefixWord ++ tailWord_3406241).sum := by decide
  have hdescent : baseEnd_3406241 < baseStart_3406241 := by decide
  rcases family_descends (prefixWord ++ tailWord_3406241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3406261 : List Nat := [1, 3, 3, 2, 3, 2, 1, 1, 2, 5]
def baseStart_3406261 : Nat := 118140960795 + 3406261 * 2 ^ 59
def prefixEnd_3406261 : Nat := 4983230072969 + 3 ^ 40 * 3406261 * 2
def baseEnd_3406261 : Nat := 583016375888200907290799

theorem tailTrace_3406261 : CollatzResearch.WordTrace tailWord_3406261 prefixEnd_3406261 583016375888200907290799 := by
  unfold tailWord_3406261
  simp only [CollatzResearch.WordTrace]
  refine ⟨124236545112705614908978637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82824363408470409939319091 124236545112705614908978637)
  ·
    refine ⟨46588704417264605590866989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 124236545112705614908978637 46588704417264605590866989)
    ·
      refine ⟨17470764156474227096575121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46588704417264605590866989 17470764156474227096575121)
      ·
        refine ⟨13103073117355670322431341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17470764156474227096575121 13103073117355670322431341)
        ·
          refine ⟨4913652419008376370911753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13103073117355670322431341 4913652419008376370911753)
          ·
            refine ⟨3685239314256282278183815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4913652419008376370911753 3685239314256282278183815)
            ·
              refine ⟨5527858971384423417275723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3685239314256282278183815 5527858971384423417275723)
              ·
                refine ⟨8291788457076635125913585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5527858971384423417275723 8291788457076635125913585)
                ·
                  refine ⟨6218841342807476344435189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8291788457076635125913585 6218841342807476344435189)
                  ·
                    refine ⟨583016375888200907290799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6218841342807476344435189 583016375888200907290799)
                    ·
                      rfl

theorem cell23_3406261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 2, 1, 1, 2, 5].length) (baseStart_3406261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3406261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3406261 prefixEnd_3406261 := by exact prefixLift 3406261
  have htrace : WordTrace (prefixWord ++ tailWord_3406261) baseStart_3406261 baseEnd_3406261 := by
    simpa [prefixWord, tailWord_3406261, baseEnd_3406261] using wordTrace_append hprefix tailTrace_3406261
  have hstable : (prefixWord ++ tailWord_3406261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3406261).length < 2 ^ (prefixWord ++ tailWord_3406261).sum := by decide
  have hdescent : baseEnd_3406261 < baseStart_3406261 := by decide
  rcases family_descends (prefixWord ++ tailWord_3406261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3406267 : List Nat := [1, 1, 1, 1, 1, 2, 2, 1, 8, 2, 3]
def baseStart_3406267 : Nat := 118140960795 + 3406267 * 2 ^ 59
def prefixEnd_3406267 : Nat := 4983230072969 + 3 ^ 40 * 3406267 * 2
def baseEnd_3406267 : Nat := 1749052208548529698397369

theorem tailTrace_3406267 : CollatzResearch.WordTrace tailWord_3406267 prefixEnd_3406267 1749052208548529698397369 := by
  unfold tailWord_3406267
  simp only [CollatzResearch.WordTrace]
  refine ⟨124236763950683877933697055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82824509300455918622464703 124236763950683877933697055)
  ·
    refine ⟨186355145926025816900545583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124236763950683877933697055 186355145926025816900545583)
    ·
      refine ⟨279532718889038725350818375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186355145926025816900545583 279532718889038725350818375)
      ·
        refine ⟨419299078333558088026227563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 279532718889038725350818375 419299078333558088026227563)
        ·
          refine ⟨628948617500337132039341345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 419299078333558088026227563 628948617500337132039341345)
          ·
            refine ⟨471711463125252849029506009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 628948617500337132039341345 471711463125252849029506009)
            ·
              refine ⟨353783597343939636772129507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 471711463125252849029506009 353783597343939636772129507)
              ·
                refine ⟨530675396015909455158194261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 353783597343939636772129507 530675396015909455158194261)
                ·
                  refine ⟨6218852297061438927635089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 530675396015909455158194261 6218852297061438927635089)
                  ·
                    refine ⟨4664139222796079195726317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6218852297061438927635089 4664139222796079195726317)
                    ·
                      refine ⟨1749052208548529698397369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4664139222796079195726317 1749052208548529698397369)
                      ·
                        rfl

theorem cell23_3406267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 1, 8, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 1, 8, 2, 3].length) (baseStart_3406267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3406267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3406267 prefixEnd_3406267 := by exact prefixLift 3406267
  have htrace : WordTrace (prefixWord ++ tailWord_3406267) baseStart_3406267 baseEnd_3406267 := by
    simpa [prefixWord, tailWord_3406267, baseEnd_3406267] using wordTrace_append hprefix tailTrace_3406267
  have hstable : (prefixWord ++ tailWord_3406267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3406267).length < 2 ^ (prefixWord ++ tailWord_3406267).sum := by decide
  have hdescent : baseEnd_3406267 < baseStart_3406267 := by decide
  rcases family_descends (prefixWord ++ tailWord_3406267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3406294 : List Nat := [5, 2, 1, 1, 1, 1, 1, 2, 2, 1, 6]
def baseStart_3406294 : Nat := 118140960795 + 3406294 * 2 ^ 59
def prefixEnd_3406294 : Nat := 4983230072969 + 3 ^ 40 * 3406294 * 2
def baseEnd_3406294 : Nat := 1749066072526201092759745

theorem tailTrace_3406294 : CollatzResearch.WordTrace tailWord_3406294 prefixEnd_3406294 1749066072526201092759745 := by
  unfold tailWord_3406294
  simp only [CollatzResearch.WordTrace]
  refine ⟨7764859295099128846558121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 82825165814390707696619957 7764859295099128846558121)
  ·
    refine ⟨5823644471324346634918591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7764859295099128846558121 5823644471324346634918591)
    ·
      refine ⟨8735466706986519952377887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5823644471324346634918591 8735466706986519952377887)
      ·
        refine ⟨13103200060479779928566831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8735466706986519952377887 13103200060479779928566831)
        ·
          refine ⟨19654800090719669892850247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13103200060479779928566831 19654800090719669892850247)
          ·
            refine ⟨29482200136079504839275371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19654800090719669892850247 29482200136079504839275371)
            ·
              refine ⟨44223300204119257258913057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29482200136079504839275371 44223300204119257258913057)
              ·
                refine ⟨33167475153089442944184793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44223300204119257258913057 33167475153089442944184793)
                ·
                  refine ⟨24875606364817082208138595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33167475153089442944184793 24875606364817082208138595)
                  ·
                    refine ⟨37313409547225623312207893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24875606364817082208138595 37313409547225623312207893)
                    ·
                      refine ⟨1749066072526201092759745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 37313409547225623312207893 1749066072526201092759745)
                      ·
                        rfl

theorem cell23_3406294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 2, 2, 1, 6].length) (baseStart_3406294 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3406294 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3406294 prefixEnd_3406294 := by exact prefixLift 3406294
  have htrace : WordTrace (prefixWord ++ tailWord_3406294) baseStart_3406294 baseEnd_3406294 := by
    simpa [prefixWord, tailWord_3406294, baseEnd_3406294] using wordTrace_append hprefix tailTrace_3406294
  have hstable : (prefixWord ++ tailWord_3406294).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3406294).length < 2 ^ (prefixWord ++ tailWord_3406294).sum := by decide
  have hdescent : baseEnd_3406294 < baseStart_3406294 := by decide
  rcases family_descends (prefixWord ++ tailWord_3406294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3406304 : List Nat := [2, 1, 1, 3, 1, 1, 7, 1, 6]
def baseStart_3406304 : Nat := 118140960795 + 3406304 * 2 ^ 59
def prefixEnd_3406304 : Nat := 4983230072969 + 3 ^ 40 * 3406304 * 2
def baseEnd_3406304 : Nat := 194341245259194005959411

theorem tailTrace_3406304 : CollatzResearch.WordTrace tailWord_3406304 prefixEnd_3406304 194341245259194005959411 := by
  unfold tailWord_3406304
  simp only [CollatzResearch.WordTrace]
  refine ⟨62119056725774916626396983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82825408967699888835195977 62119056725774916626396983)
  ·
    refine ⟨93178585088662374939595475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62119056725774916626396983 93178585088662374939595475)
    ·
      refine ⟨139767877632993562409393213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93178585088662374939595475 139767877632993562409393213)
      ·
        refine ⟨52412954112372585903522455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 139767877632993562409393213 52412954112372585903522455)
        ·
          refine ⟨78619431168558878855283683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52412954112372585903522455 78619431168558878855283683)
          ·
            refine ⟨117929146752838318282925525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78619431168558878855283683 117929146752838318282925525)
            ·
              refine ⟨2763964377019648084756067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 117929146752838318282925525 2763964377019648084756067)
              ·
                refine ⟨4145946565529472127134101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2763964377019648084756067 4145946565529472127134101)
                ·
                  refine ⟨194341245259194005959411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4145946565529472127134101 194341245259194005959411)
                  ·
                    rfl

theorem cell23_3406304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 7, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 7, 1, 6].length) (baseStart_3406304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3406304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3406304 prefixEnd_3406304 := by exact prefixLift 3406304
  have htrace : WordTrace (prefixWord ++ tailWord_3406304) baseStart_3406304 baseEnd_3406304 := by
    simpa [prefixWord, tailWord_3406304, baseEnd_3406304] using wordTrace_append hprefix tailTrace_3406304
  have hstable : (prefixWord ++ tailWord_3406304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3406304).length < 2 ^ (prefixWord ++ tailWord_3406304).sum := by decide
  have hdescent : baseEnd_3406304 < baseStart_3406304 := by decide
  rcases family_descends (prefixWord ++ tailWord_3406304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3406342 : List Nat := [6, 2, 1, 1, 1, 3, 1, 1, 3, 4]
def baseStart_3406342 : Nat := 118140960795 + 3406342 * 2 ^ 59
def prefixEnd_3406342 : Nat := 4983230072969 + 3 ^ 40 * 3406342 * 2
def baseEnd_3406342 : Nat := 583030239865872301653175

theorem tailTrace_3406342 : CollatzResearch.WordTrace tailWord_3406342 prefixEnd_3406342 583030239865872301653175 := by
  unfold tailWord_3406342
  simp only [CollatzResearch.WordTrace]
  refine ⟨3882484357044130179458665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 82826332950274777161784853 3882484357044130179458665)
  ·
    refine ⟨2911863267783097634593999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3882484357044130179458665 2911863267783097634593999)
    ·
      refine ⟨4367794901674646451890999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2911863267783097634593999 4367794901674646451890999)
      ·
        refine ⟨6551692352511969677836499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4367794901674646451890999 6551692352511969677836499)
        ·
          refine ⟨9827538528767954516754749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6551692352511969677836499 9827538528767954516754749)
          ·
            refine ⟨3685326948287982943783031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9827538528767954516754749 3685326948287982943783031)
            ·
              refine ⟨5527990422431974415674547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3685326948287982943783031 5527990422431974415674547)
              ·
                refine ⟨8291985633647961623511821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5527990422431974415674547 8291985633647961623511821)
                ·
                  refine ⟨3109494612617985608816933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8291985633647961623511821 3109494612617985608816933)
                  ·
                    refine ⟨583030239865872301653175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3109494612617985608816933 583030239865872301653175)
                    ·
                      rfl

theorem cell23_3406342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 3, 1, 1, 3, 4].length) (baseStart_3406342 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3406342 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3406342 prefixEnd_3406342 := by exact prefixLift 3406342
  have htrace : WordTrace (prefixWord ++ tailWord_3406342) baseStart_3406342 baseEnd_3406342 := by
    simpa [prefixWord, tailWord_3406342, baseEnd_3406342] using wordTrace_append hprefix tailTrace_3406342
  have hstable : (prefixWord ++ tailWord_3406342).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3406342).length < 2 ^ (prefixWord ++ tailWord_3406342).sum := by decide
  have hdescent : baseEnd_3406342 < baseStart_3406342 := by decide
  rcases family_descends (prefixWord ++ tailWord_3406342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3406348 : List Nat := [2, 2, 1, 2, 4, 3, 1, 1, 3, 1, 3]
def baseStart_3406348 : Nat := 118140960795 + 3406348 * 2 ^ 59
def prefixEnd_3406348 : Nat := 4983230072969 + 3 ^ 40 * 3406348 * 2
def baseEnd_3406348 : Nat := 1749093800481543881484497

theorem tailTrace_3406348 : CollatzResearch.WordTrace tailWord_3406348 prefixEnd_3406348 1749093800481543881484497 := by
  unfold tailWord_3406348
  simp only [CollatzResearch.WordTrace]
  refine ⟨62119859131695214383697849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82826478842260285844930465 62119859131695214383697849)
  ·
    refine ⟨46589894348771410787773387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62119859131695214383697849 46589894348771410787773387)
    ·
      refine ⟨69884841523157116181660081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46589894348771410787773387 69884841523157116181660081)
      ·
        refine ⟨52413631142367837136245061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69884841523157116181660081 52413631142367837136245061)
        ·
          refine ⟨9827555839193969463045949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 52413631142367837136245061 9827555839193969463045949)
          ·
            refine ⟨3685333439697738548642231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9827555839193969463045949 3685333439697738548642231)
            ·
              refine ⟨5528000159546607822963347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3685333439697738548642231 5528000159546607822963347)
              ·
                refine ⟨8292000239319911734445021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5528000159546607822963347 8292000239319911734445021)
                ·
                  refine ⟨3109500089744966900416883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8292000239319911734445021 3109500089744966900416883)
                  ·
                    refine ⟨4664250134617450350625325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3109500089744966900416883 4664250134617450350625325)
                    ·
                      refine ⟨1749093800481543881484497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4664250134617450350625325 1749093800481543881484497)
                      ·
                        rfl

theorem cell23_3406348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 3, 1, 1, 3, 1, 3].length) (baseStart_3406348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3406348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3406348 prefixEnd_3406348 := by exact prefixLift 3406348
  have htrace : WordTrace (prefixWord ++ tailWord_3406348) baseStart_3406348 baseEnd_3406348 := by
    simpa [prefixWord, tailWord_3406348, baseEnd_3406348] using wordTrace_append hprefix tailTrace_3406348
  have hstable : (prefixWord ++ tailWord_3406348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3406348).length < 2 ^ (prefixWord ++ tailWord_3406348).sum := by decide
  have hdescent : baseEnd_3406348 < baseStart_3406348 := by decide
  rcases family_descends (prefixWord ++ tailWord_3406348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3406368 : List Nat := [2, 1, 1, 6, 2, 2, 1, 2, 1, 5]
def baseStart_3406368 : Nat := 118140960795 + 3406368 * 2 ^ 59
def prefixEnd_3406368 : Nat := 4983230072969 + 3 ^ 40 * 3406368 * 2
def baseEnd_3406368 : Nat := 583034690031544601078135

theorem tailTrace_3406368 : CollatzResearch.WordTrace tailWord_3406368 prefixEnd_3406368 583034690031544601078135 := by
  unfold tailWord_3406368
  simp only [CollatzResearch.WordTrace]
  refine ⟨62120223861658986091561879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82826965148878648122082505 62120223861658986091561879)
  ·
    refine ⟨93180335792488479137342819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62120223861658986091561879 93180335792488479137342819)
    ·
      refine ⟨139770503688732718706014229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93180335792488479137342819 139770503688732718706014229)
      ·
        refine ⟨6551742360409346189344417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 139770503688732718706014229 6551742360409346189344417)
        ·
          refine ⟨4913806770307009642008313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6551742360409346189344417 4913806770307009642008313)
          ·
            refine ⟨3685355077730257231506235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4913806770307009642008313 3685355077730257231506235)
            ·
              refine ⟨5528032616595385847259353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3685355077730257231506235 5528032616595385847259353)
              ·
                refine ⟨4146024462446539385444515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5528032616595385847259353 4146024462446539385444515)
                ·
                  refine ⟨6219036693669809078166773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4146024462446539385444515 6219036693669809078166773)
                  ·
                    refine ⟨583034690031544601078135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6219036693669809078166773 583034690031544601078135)
                    ·
                      rfl

theorem cell23_3406368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 2, 1, 2, 1, 5].length) (baseStart_3406368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3406368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3406368 prefixEnd_3406368 := by exact prefixLift 3406368
  have htrace : WordTrace (prefixWord ++ tailWord_3406368) baseStart_3406368 baseEnd_3406368 := by
    simpa [prefixWord, tailWord_3406368, baseEnd_3406368] using wordTrace_append hprefix tailTrace_3406368
  have hstable : (prefixWord ++ tailWord_3406368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3406368).length < 2 ^ (prefixWord ++ tailWord_3406368).sum := by decide
  have hdescent : baseEnd_3406368 < baseStart_3406368 := by decide
  rcases family_descends (prefixWord ++ tailWord_3406368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3406371 : List Nat := [1, 1, 1, 4, 4, 1, 3, 2, 1, 1, 4]
def baseStart_3406371 : Nat := 118140960795 + 3406371 * 2 ^ 59
def prefixEnd_3406371 : Nat := 4983230072969 + 3 ^ 40 * 3406371 * 2
def baseEnd_3406371 : Nat := 1749105610536597291496891

theorem tailTrace_3406371 : CollatzResearch.WordTrace tailWord_3406371 prefixEnd_3406371 1749105610536597291496891 := by
  unfold tailWord_3406371
  simp only [CollatzResearch.WordTrace]
  refine ⟨124240557142307103695482967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82827038094871402463655311 124240557142307103695482967)
  ·
    refine ⟨186360835713460655543224451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124240557142307103695482967 186360835713460655543224451)
    ·
      refine ⟨279541253570190983314836677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186360835713460655543224451 279541253570190983314836677)
      ·
        refine ⟨52413985044410809371531877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 279541253570190983314836677 52413985044410809371531877)
        ·
          refine ⟨9827622195827026757162227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 52413985044410809371531877 9827622195827026757162227)
          ·
            refine ⟨14741433293740540135743341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9827622195827026757162227 14741433293740540135743341)
            ·
              refine ⟨5528037485152702550903753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14741433293740540135743341 5528037485152702550903753)
              ·
                refine ⟨4146028113864526913177815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5528037485152702550903753 4146028113864526913177815)
                ·
                  refine ⟨6219042170796790369766723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4146028113864526913177815 6219042170796790369766723)
                  ·
                    refine ⟨9328563256195185554650085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6219042170796790369766723 9328563256195185554650085)
                    ·
                      refine ⟨1749105610536597291496891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9328563256195185554650085 1749105610536597291496891)
                      ·
                        rfl

theorem cell23_3406371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 3, 2, 1, 1, 4].length) (baseStart_3406371 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3406371 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3406371 prefixEnd_3406371 := by exact prefixLift 3406371
  have htrace : WordTrace (prefixWord ++ tailWord_3406371) baseStart_3406371 baseEnd_3406371 := by
    simpa [prefixWord, tailWord_3406371, baseEnd_3406371] using wordTrace_append hprefix tailTrace_3406371
  have hstable : (prefixWord ++ tailWord_3406371).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3406371).length < 2 ^ (prefixWord ++ tailWord_3406371).sum := by decide
  have hdescent : baseEnd_3406371 < baseStart_3406371 := by decide
  rcases family_descends (prefixWord ++ tailWord_3406371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3406405 : List Nat := [1, 3, 1, 1, 1, 6, 1, 4, 1, 2, 2]
def baseStart_3406405 : Nat := 118140960795 + 3406405 * 2 ^ 59
def prefixEnd_3406405 : Nat := 4983230072969 + 3 ^ 40 * 3406405 * 2
def baseEnd_3406405 : Nat := 1749123068878850158471735

theorem tailTrace_3406405 : CollatzResearch.WordTrace tailWord_3406405 prefixEnd_3406405 1749123068878850158471735 := by
  unfold tailWord_3406405
  simp only [CollatzResearch.WordTrace]
  refine ⟨124241797224183927502220669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82827864816122618334813779 124241797224183927502220669)
  ·
    refine ⟨46590673959068972813332751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 124241797224183927502220669 46590673959068972813332751)
    ·
      refine ⟨69886010938603459219999127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46590673959068972813332751 69886010938603459219999127)
      ·
        refine ⟨104829016407905188829998691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69886010938603459219999127 104829016407905188829998691)
        ·
          refine ⟨157243524611857783244998037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104829016407905188829998691 157243524611857783244998037)
          ·
            refine ⟨7370790216180833589609283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 157243524611857783244998037 7370790216180833589609283)
            ·
              refine ⟨11056185324271250384413925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7370790216180833589609283 11056185324271250384413925)
              ·
                refine ⟨2073034748300859447077611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11056185324271250384413925 2073034748300859447077611)
                ·
                  refine ⟨3109552122451289170616417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2073034748300859447077611 3109552122451289170616417)
                  ·
                    refine ⟨2332164091838466877962313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3109552122451289170616417 2332164091838466877962313)
                    ·
                      refine ⟨1749123068878850158471735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2332164091838466877962313 1749123068878850158471735)
                      ·
                        rfl

theorem cell23_3406405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 1, 4, 1, 2, 2].length) (baseStart_3406405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3406405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3406405 prefixEnd_3406405 := by exact prefixLift 3406405
  have htrace : WordTrace (prefixWord ++ tailWord_3406405) baseStart_3406405 baseEnd_3406405 := by
    simpa [prefixWord, tailWord_3406405, baseEnd_3406405] using wordTrace_append hprefix tailTrace_3406405
  have hstable : (prefixWord ++ tailWord_3406405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3406405).length < 2 ^ (prefixWord ++ tailWord_3406405).sum := by decide
  have hdescent : baseEnd_3406405 < baseStart_3406405 := by decide
  rcases family_descends (prefixWord ++ tailWord_3406405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3406521 : List Nat := [1, 2, 1, 4, 1, 1, 1, 3, 2, 5, 2]
def baseStart_3406521 : Nat := 118140960795 + 3406521 * 2 ^ 59
def prefixEnd_3406521 : Nat := 4983230072969 + 3 ^ 40 * 3406521 * 2
def baseEnd_3406521 : Nat := 1749182632634771704621201

theorem tailTrace_3406521 : CollatzResearch.WordTrace tailWord_3406521 prefixEnd_3406521 1749182632634771704621201 := by
  unfold tailWord_3406521
  simp only [CollatzResearch.WordTrace]
  refine ⟨124246028091763679313443417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82830685394509119542295611 124246028091763679313443417)
  ·
    refine ⟨93184521068822759485082563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124246028091763679313443417 93184521068822759485082563)
    ·
      refine ⟨139776781603234139227623845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93184521068822759485082563 139776781603234139227623845)
      ·
        refine ⟨26208146550606401105179471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 139776781603234139227623845 26208146550606401105179471)
        ·
          refine ⟨39312219825909601657769207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26208146550606401105179471 39312219825909601657769207)
          ·
            refine ⟨58968329738864402486653811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39312219825909601657769207 58968329738864402486653811)
            ·
              refine ⟨88452494608296603729980717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58968329738864402486653811 88452494608296603729980717)
              ·
                refine ⟨33169685478111226398742769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 88452494608296603729980717 33169685478111226398742769)
                ·
                  refine ⟨24877264108583419799057077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33169685478111226398742769 24877264108583419799057077)
                  ·
                    refine ⟨2332243510179695606161601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 24877264108583419799057077 2332243510179695606161601)
                    ·
                      refine ⟨1749182632634771704621201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2332243510179695606161601 1749182632634771704621201)
                      ·
                        rfl

theorem cell23_3406521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 3, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 3, 2, 5, 2].length) (baseStart_3406521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3406521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3406521 prefixEnd_3406521 := by exact prefixLift 3406521
  have htrace : WordTrace (prefixWord ++ tailWord_3406521) baseStart_3406521 baseEnd_3406521 := by
    simpa [prefixWord, tailWord_3406521, baseEnd_3406521] using wordTrace_append hprefix tailTrace_3406521
  have hstable : (prefixWord ++ tailWord_3406521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3406521).length < 2 ^ (prefixWord ++ tailWord_3406521).sum := by decide
  have hdescent : baseEnd_3406521 < baseStart_3406521 := by decide
  rcases family_descends (prefixWord ++ tailWord_3406521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3406529 : List Nat := [1, 2, 6, 2, 1, 1, 1, 3, 2, 2, 2]
def baseStart_3406529 : Nat := 118140960795 + 3406529 * 2 ^ 59
def prefixEnd_3406529 : Nat := 4983230072969 + 3 ^ 40 * 3406529 * 2
def baseEnd_3406529 : Nat := 1749186740480007673321165

theorem tailTrace_3406529 : CollatzResearch.WordTrace tailWord_3406529 prefixEnd_3406529 1749186740480007673321165 := by
  unfold tailWord_3406529
  simp only [CollatzResearch.WordTrace]
  refine ⟨124246319875734696679734641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82830879917156464453156427 124246319875734696679734641)
  ·
    refine ⟨93184739906801022509800981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124246319875734696679734641 93184739906801022509800981)
    ·
      refine ⟨4368034683131297930146921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 93184739906801022509800981 4368034683131297930146921)
      ·
        refine ⟨3276026012348473447610191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4368034683131297930146921 3276026012348473447610191)
        ·
          refine ⟨4914039018522710171415287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3276026012348473447610191 4914039018522710171415287)
          ·
            refine ⟨7371058527784065257122931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4914039018522710171415287 7371058527784065257122931)
            ·
              refine ⟨11056587791676097885684397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7371058527784065257122931 11056587791676097885684397)
              ·
                refine ⟨4146220421878536707131649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11056587791676097885684397 4146220421878536707131649)
                ·
                  refine ⟨3109665316408902530348737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4146220421878536707131649 3109665316408902530348737)
                  ·
                    refine ⟨2332248987306676897761553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3109665316408902530348737 2332248987306676897761553)
                    ·
                      refine ⟨1749186740480007673321165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2332248987306676897761553 1749186740480007673321165)
                      ·
                        rfl

theorem cell23_3406529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 1, 3, 2, 2, 2].length) (baseStart_3406529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3406529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3406529 prefixEnd_3406529 := by exact prefixLift 3406529
  have htrace : WordTrace (prefixWord ++ tailWord_3406529) baseStart_3406529 baseEnd_3406529 := by
    simpa [prefixWord, tailWord_3406529, baseEnd_3406529] using wordTrace_append hprefix tailTrace_3406529
  have hstable : (prefixWord ++ tailWord_3406529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3406529).length < 2 ^ (prefixWord ++ tailWord_3406529).sum := by decide
  have hdescent : baseEnd_3406529 < baseStart_3406529 := by decide
  rcases family_descends (prefixWord ++ tailWord_3406529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3406551 : List Nat := [1, 1, 3, 2, 1, 4, 1, 3, 2, 1, 4]
def baseStart_3406551 : Nat := 118140960795 + 3406551 * 2 ^ 59
def prefixEnd_3406551 : Nat := 4983230072969 + 3 ^ 40 * 3406551 * 2
def baseEnd_3406551 : Nat := 1749198037054406587246063

theorem tailTrace_3406551 : CollatzResearch.WordTrace tailWord_3406551 prefixEnd_3406551 1749198037054406587246063 := by
  unfold tailWord_3406551
  simp only [CollatzResearch.WordTrace]
  refine ⟨124247122281654994437035507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82831414854436662958023671 124247122281654994437035507)
  ·
    refine ⟨186370683422482491655553261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124247122281654994437035507 186370683422482491655553261)
    ·
      refine ⟨69889006283430934370832473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 186370683422482491655553261 69889006283430934370832473)
      ·
        refine ⟨52416754712573200778124355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69889006283430934370832473 52416754712573200778124355)
        ·
          refine ⟨78625132068859801167186533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52416754712573200778124355 78625132068859801167186533)
          ·
            refine ⟨14742212262911212718847475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 78625132068859801167186533 14742212262911212718847475)
            ·
              refine ⟨22113318394366819078271213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14742212262911212718847475 22113318394366819078271213)
              ·
                refine ⟨8292494397887557154351705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22113318394366819078271213 8292494397887557154351705)
                ·
                  refine ⟨6219370798415667865763779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8292494397887557154351705 6219370798415667865763779)
                  ·
                    refine ⟨9329056197623501798645669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6219370798415667865763779 9329056197623501798645669)
                    ·
                      refine ⟨1749198037054406587246063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9329056197623501798645669 1749198037054406587246063)
                      ·
                        rfl

theorem cell23_3406551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 1, 3, 2, 1, 4].length) (baseStart_3406551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3406551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3406551 prefixEnd_3406551 := by exact prefixLift 3406551
  have htrace : WordTrace (prefixWord ++ tailWord_3406551) baseStart_3406551 baseEnd_3406551 := by
    simpa [prefixWord, tailWord_3406551, baseEnd_3406551] using wordTrace_append hprefix tailTrace_3406551
  have hstable : (prefixWord ++ tailWord_3406551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3406551).length < 2 ^ (prefixWord ++ tailWord_3406551).sum := by decide
  have hdescent : baseEnd_3406551 < baseStart_3406551 := by decide
  rcases family_descends (prefixWord ++ tailWord_3406551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3406618 : List Nat := [3, 1, 1, 3, 2, 1, 1, 2, 5, 1, 3]
def baseStart_3406618 : Nat := 118140960795 + 3406618 * 2 ^ 59
def prefixEnd_3406618 : Nat := 4983230072969 + 3 ^ 40 * 3406618 * 2
def baseEnd_3406618 : Nat := 1749232440258257825108255

theorem tailTrace_3406618 : CollatzResearch.WordTrace tailWord_3406618 prefixEnd_3406618 1749232440258257825108255 := by
  unfold tailWord_3406618
  simp only [CollatzResearch.WordTrace]
  refine ⟨31062391493103066219931127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82833043981608176586483005 31062391493103066219931127)
  ·
    refine ⟨46593587239654599329896691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31062391493103066219931127 46593587239654599329896691)
    ·
      refine ⟨69890380859481898994845037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46593587239654599329896691 69890380859481898994845037)
      ·
        refine ⟨26208892822305712123066889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69890380859481898994845037 26208892822305712123066889)
        ·
          refine ⟨19656669616729284092300167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26208892822305712123066889 19656669616729284092300167)
          ·
            refine ⟨29485004425093926138450251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19656669616729284092300167 29485004425093926138450251)
            ·
              refine ⟨44227506637640889207675377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29485004425093926138450251 44227506637640889207675377)
              ·
                refine ⟨33170629978230666905756533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44227506637640889207675377 33170629978230666905756533)
                ·
                  refine ⟨3109746560459125022414675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 33170629978230666905756533 3109746560459125022414675)
                  ·
                    refine ⟨4664619840688687533622013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3109746560459125022414675 4664619840688687533622013)
                    ·
                      refine ⟨1749232440258257825108255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4664619840688687533622013 1749232440258257825108255)
                      ·
                        rfl

theorem cell23_3406618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 2, 5, 1, 3].length) (baseStart_3406618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3406618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3406618 prefixEnd_3406618 := by exact prefixLift 3406618
  have htrace : WordTrace (prefixWord ++ tailWord_3406618) baseStart_3406618 baseEnd_3406618 := by
    simpa [prefixWord, tailWord_3406618, baseEnd_3406618] using wordTrace_append hprefix tailTrace_3406618
  have hstable : (prefixWord ++ tailWord_3406618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3406618).length < 2 ^ (prefixWord ++ tailWord_3406618).sum := by decide
  have hdescent : baseEnd_3406618 < baseStart_3406618 := by decide
  rcases family_descends (prefixWord ++ tailWord_3406618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3406668 : List Nat := [2, 2, 1, 3, 3, 1, 1, 2, 4, 4]
def baseStart_3406668 : Nat := 118140960795 + 3406668 * 2 ^ 59
def prefixEnd_3406668 : Nat := 4983230072969 + 3 ^ 40 * 3406668 * 2
def baseEnd_3406668 : Nat := 583086038096994209827675

theorem tailTrace_3406668 : CollatzResearch.WordTrace tailWord_3406668 prefixEnd_3406668 583086038096994209827675 := by
  unfold tailWord_3406668
  simp only [CollatzResearch.WordTrace]
  refine ⟨62125694811115561709522329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82834259748154082279363105 62125694811115561709522329)
  ·
    refine ⟨46594271108336671282141747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62125694811115561709522329 46594271108336671282141747)
    ·
      refine ⟨69891406662505006923212621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46594271108336671282141747 69891406662505006923212621)
      ·
        refine ⟨26209277498439377596204733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69891406662505006923212621 26209277498439377596204733)
        ·
          refine ⟨9828479061914766598576775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26209277498439377596204733 9828479061914766598576775)
          ·
            refine ⟨14742718592872149897865163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9828479061914766598576775 14742718592872149897865163)
            ·
              refine ⟨22114077889308224846797745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14742718592872149897865163 22114077889308224846797745)
              ·
                refine ⟨16585558416981168635098309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22114077889308224846797745 16585558416981168635098309)
                ·
                  refine ⟨3109792203183969119080933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16585558416981168635098309 3109792203183969119080933)
                  ·
                    refine ⟨583086038096994209827675, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3109792203183969119080933 583086038096994209827675)
                    ·
                      rfl

theorem cell23_3406668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 1, 2, 4, 4].length) (baseStart_3406668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3406668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3406668 prefixEnd_3406668 := by exact prefixLift 3406668
  have htrace : WordTrace (prefixWord ++ tailWord_3406668) baseStart_3406668 baseEnd_3406668 := by
    simpa [prefixWord, tailWord_3406668, baseEnd_3406668] using wordTrace_append hprefix tailTrace_3406668
  have hstable : (prefixWord ++ tailWord_3406668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3406668).length < 2 ^ (prefixWord ++ tailWord_3406668).sum := by decide
  have hdescent : baseEnd_3406668 < baseStart_3406668 := by decide
  rcases family_descends (prefixWord ++ tailWord_3406668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3406681 : List Nat := [1, 2, 1, 2, 2, 6, 9]
def baseStart_3406681 : Nat := 118140960795 + 3406681 * 2 ^ 59
def prefixEnd_3406681 : Nat := 4983230072969 + 3 ^ 40 * 3406681 * 2
def baseEnd_3406681 : Nat := 21595861599252976279265

theorem tailTrace_3406681 : CollatzResearch.WordTrace tailWord_3406681 prefixEnd_3406681 21595861599252976279265 := by
  unfold tailWord_3406681
  simp only [CollatzResearch.WordTrace]
  refine ⟨124251863771184026639267897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82834575847456017759511931 124251863771184026639267897)
  ·
    refine ⟨93188897828388019979450923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124251863771184026639267897 93188897828388019979450923)
    ·
      refine ⟨139783346742582029969176385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93188897828388019979450923 139783346742582029969176385)
      ·
        refine ⟨104837510056936522476882289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 139783346742582029969176385 104837510056936522476882289)
        ·
          refine ⟨78628132542702391857661717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104837510056936522476882289 78628132542702391857661717)
          ·
            refine ⟨3685693712939174618327893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 78628132542702391857661717 3685693712939174618327893)
            ·
              refine ⟨21595861599252976279265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3685693712939174618327893 21595861599252976279265)
              ·
                rfl

theorem cell23_3406681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 6, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 6, 9].length) (baseStart_3406681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3406681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3406681 prefixEnd_3406681 := by exact prefixLift 3406681
  have htrace : WordTrace (prefixWord ++ tailWord_3406681) baseStart_3406681 baseEnd_3406681 := by
    simpa [prefixWord, tailWord_3406681, baseEnd_3406681] using wordTrace_append hprefix tailTrace_3406681
  have hstable : (prefixWord ++ tailWord_3406681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3406681).length < 2 ^ (prefixWord ++ tailWord_3406681).sum := by decide
  have hdescent : baseEnd_3406681 < baseStart_3406681 := by decide
  rcases family_descends (prefixWord ++ tailWord_3406681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3406692 : List Nat := [2, 3, 1, 1, 4, 1, 3, 1, 3, 2, 2]
def baseStart_3406692 : Nat := 118140960795 + 3406692 * 2 ^ 59
def prefixEnd_3406692 : Nat := 4983230072969 + 3 ^ 40 * 3406692 * 2
def baseEnd_3406692 : Nat := 1749270437826690535582915

theorem tailTrace_3406692 : CollatzResearch.WordTrace tailWord_3406692 prefixEnd_3406692 1749270437826690535582915 := by
  unfold tailWord_3406692
  simp only [CollatzResearch.WordTrace]
  refine ⟨62126132487072087758959165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82834843316096117011945553 62126132487072087758959165)
  ·
    refine ⟨23297299682652032909609687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62126132487072087758959165 23297299682652032909609687)
    ·
      refine ⟨34945949523978049364414531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23297299682652032909609687 34945949523978049364414531)
      ·
        refine ⟨52418924285967074046621797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34945949523978049364414531 52418924285967074046621797)
        ·
          refine ⟨9828548303618826383741587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 52418924285967074046621797 9828548303618826383741587)
          ·
            refine ⟨14742822455428239575612381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9828548303618826383741587 14742822455428239575612381)
            ·
              refine ⟨5528558420785589840854643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14742822455428239575612381 5528558420785589840854643)
              ·
                refine ⟨8292837631178384761281965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5528558420785589840854643 8292837631178384761281965)
                ·
                  refine ⟨3109814111691894285480737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8292837631178384761281965 3109814111691894285480737)
                  ·
                    refine ⟨2332360583768920714110553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3109814111691894285480737 2332360583768920714110553)
                    ·
                      refine ⟨1749270437826690535582915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2332360583768920714110553 1749270437826690535582915)
                      ·
                        rfl

theorem cell23_3406692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 3, 1, 3, 2, 2].length) (baseStart_3406692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3406692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3406692 prefixEnd_3406692 := by exact prefixLift 3406692
  have htrace : WordTrace (prefixWord ++ tailWord_3406692) baseStart_3406692 baseEnd_3406692 := by
    simpa [prefixWord, tailWord_3406692, baseEnd_3406692] using wordTrace_append hprefix tailTrace_3406692
  have hstable : (prefixWord ++ tailWord_3406692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3406692).length < 2 ^ (prefixWord ++ tailWord_3406692).sum := by decide
  have hdescent : baseEnd_3406692 < baseStart_3406692 := by decide
  rcases family_descends (prefixWord ++ tailWord_3406692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3406701 : List Nat := [1, 5, 1, 1, 1, 1, 1, 1, 1, 4, 6]
def baseStart_3406701 : Nat := 118140960795 + 3406701 * 2 ^ 59
def prefixEnd_3406701 : Nat := 4983230072969 + 3 ^ 40 * 3406701 * 2
def baseEnd_3406701 : Nat := 1749275059152581000370373

theorem tailTrace_3406701 : CollatzResearch.WordTrace tailWord_3406701 prefixEnd_3406701 1749275059152581000370373 := by
  unfold tailWord_3406701
  simp only [CollatzResearch.WordTrace]
  refine ⟨124252593231111570054995957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82835062154074380036663971 124252593231111570054995957)
  ·
    refine ⟨11648680615416709692655871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 124252593231111570054995957 11648680615416709692655871)
    ·
      refine ⟨17473020923125064538983807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11648680615416709692655871 17473020923125064538983807)
      ·
        refine ⟨26209531384687596808475711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17473020923125064538983807 26209531384687596808475711)
        ·
          refine ⟨39314297077031395212713567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26209531384687596808475711 39314297077031395212713567)
          ·
            refine ⟨58971445615547092819070351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39314297077031395212713567 58971445615547092819070351)
            ·
              refine ⟨88457168423320639228605527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58971445615547092819070351 88457168423320639228605527)
              ·
                refine ⟨132685752634980958842908291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 88457168423320639228605527 132685752634980958842908291)
                ·
                  refine ⟨199028628952471438264362437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 132685752634980958842908291 199028628952471438264362437)
                  ·
                    refine ⟨37317867928588394674567957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 199028628952471438264362437 37317867928588394674567957)
                    ·
                      refine ⟨1749275059152581000370373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 37317867928588394674567957 1749275059152581000370373)
                      ·
                        rfl

theorem cell23_3406701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 1, 1, 4, 6].length) (baseStart_3406701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3406701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3406701 prefixEnd_3406701 := by exact prefixLift 3406701
  have htrace : WordTrace (prefixWord ++ tailWord_3406701) baseStart_3406701 baseEnd_3406701 := by
    simpa [prefixWord, tailWord_3406701, baseEnd_3406701] using wordTrace_append hprefix tailTrace_3406701
  have hstable : (prefixWord ++ tailWord_3406701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3406701).length < 2 ^ (prefixWord ++ tailWord_3406701).sum := by decide
  have hdescent : baseEnd_3406701 < baseStart_3406701 := by decide
  rcases family_descends (prefixWord ++ tailWord_3406701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3406702 : List Nat := [4, 1, 2, 3, 2, 1, 1, 3, 2, 4]
def baseStart_3406702 : Nat := 118140960795 + 3406702 * 2 ^ 59
def prefixEnd_3406702 : Nat := 4983230072969 + 3 ^ 40 * 3406702 * 2
def baseEnd_3406702 : Nat := 583091857544411832152623

theorem tailTrace_3406702 : CollatzResearch.WordTrace tailWord_3406702 prefixEnd_3406702 583091857544411832152623 := by
  unfold tailWord_3406702
  simp only [CollatzResearch.WordTrace]
  refine ⟨15531578713013493403222795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 82835086469405298150521573 15531578713013493403222795)
  ·
    refine ⟨23297368069520240104834193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15531578713013493403222795 23297368069520240104834193)
    ·
      refine ⟨17473026052140180078625645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23297368069520240104834193 17473026052140180078625645)
      ·
        refine ⟨6552384769552567529484617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17473026052140180078625645 6552384769552567529484617)
        ·
          refine ⟨4914288577164425647113463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6552384769552567529484617 4914288577164425647113463)
          ·
            refine ⟨7371432865746638470670195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4914288577164425647113463 7371432865746638470670195)
            ·
              refine ⟨11057149298619957706005293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7371432865746638470670195 11057149298619957706005293)
              ·
                refine ⟨4146430986982484139751985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11057149298619957706005293 4146430986982484139751985)
                ·
                  refine ⟨3109823240236863104813989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4146430986982484139751985 3109823240236863104813989)
                  ·
                    refine ⟨583091857544411832152623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3109823240236863104813989 583091857544411832152623)
                    ·
                      rfl

theorem cell23_3406702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 1, 3, 2, 4].length) (baseStart_3406702 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3406702 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3406702 prefixEnd_3406702 := by exact prefixLift 3406702
  have htrace : WordTrace (prefixWord ++ tailWord_3406702) baseStart_3406702 baseEnd_3406702 := by
    simpa [prefixWord, tailWord_3406702, baseEnd_3406702] using wordTrace_append hprefix tailTrace_3406702
  have hstable : (prefixWord ++ tailWord_3406702).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3406702).length < 2 ^ (prefixWord ++ tailWord_3406702).sum := by decide
  have hdescent : baseEnd_3406702 < baseStart_3406702 := by decide
  rcases family_descends (prefixWord ++ tailWord_3406702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3406782 : List Nat := [4, 2, 1, 1, 1, 2, 2, 2, 4, 2, 2]
def baseStart_3406782 : Nat := 118140960795 + 3406782 * 2 ^ 59
def prefixEnd_3406782 : Nat := 4983230072969 + 3 ^ 40 * 3406782 * 2
def baseEnd_3406782 : Nat := 1749316651085595183457501

theorem tailTrace_3406782 : CollatzResearch.WordTrace tailWord_3406782 prefixEnd_3406782 1749316651085595183457501 := by
  unfold tailWord_3406782
  simp only [CollatzResearch.WordTrace]
  refine ⟨15531943442977265111086825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 82837031695878747259129733 15531943442977265111086825)
  ·
    refine ⟨11648957582232948833315119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15531943442977265111086825 11648957582232948833315119)
    ·
      refine ⟨17473436373349423249972679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11648957582232948833315119 17473436373349423249972679)
      ·
        refine ⟨26210154560024134874959019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17473436373349423249972679 26210154560024134874959019)
        ·
          refine ⟨39315231840036202312438529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26210154560024134874959019 39315231840036202312438529)
          ·
            refine ⟨29486423880027151734328897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39315231840036202312438529 29486423880027151734328897)
            ·
              refine ⟨22114817910020363800746673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29486423880027151734328897 22114817910020363800746673)
              ·
                refine ⟨16586113432515272850560005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22114817910020363800746673 16586113432515272850560005)
                ·
                  refine ⟨3109896268596613659480001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16586113432515272850560005 3109896268596613659480001)
                  ·
                    refine ⟨2332422201447460244610001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3109896268596613659480001 2332422201447460244610001)
                    ·
                      refine ⟨1749316651085595183457501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2332422201447460244610001 1749316651085595183457501)
                      ·
                        rfl

theorem cell23_3406782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 2, 2, 4, 2, 2].length) (baseStart_3406782 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3406782 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3406782 prefixEnd_3406782 := by exact prefixLift 3406782
  have htrace : WordTrace (prefixWord ++ tailWord_3406782) baseStart_3406782 baseEnd_3406782 := by
    simpa [prefixWord, tailWord_3406782, baseEnd_3406782] using wordTrace_append hprefix tailTrace_3406782
  have hstable : (prefixWord ++ tailWord_3406782).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3406782).length < 2 ^ (prefixWord ++ tailWord_3406782).sum := by decide
  have hdescent : baseEnd_3406782 < baseStart_3406782 := by decide
  rcases family_descends (prefixWord ++ tailWord_3406782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3406799 : List Nat := [1, 1, 2, 1, 1, 8, 1, 2, 2, 2, 2]
def baseStart_3406799 : Nat := 118140960795 + 3406799 * 2 ^ 59
def prefixEnd_3406799 : Nat := 4983230072969 + 3 ^ 40 * 3406799 * 2
def baseEnd_3406799 : Nat := 1749325380256721616944923

theorem tailTrace_3406799 : CollatzResearch.WordTrace tailWord_3406799 prefixEnd_3406799 1749325380256721616944923 := by
  unfold tailWord_3406799
  simp only [CollatzResearch.WordTrace]
  refine ⟨124256167584756532792063451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82837445056504355194708967 124256167584756532792063451)
  ·
    refine ⟨186384251377134799188095177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124256167584756532792063451 186384251377134799188095177)
    ·
      refine ⟨139788188532851099391071383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 186384251377134799188095177 139788188532851099391071383)
      ·
        refine ⟨209682282799276649086607075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139788188532851099391071383 209682282799276649086607075)
        ·
          refine ⟨314523424198914973629910613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 209682282799276649086607075 314523424198914973629910613)
          ·
            refine ⟨3685821377331034847225515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 314523424198914973629910613 3685821377331034847225515)
            ·
              refine ⟨5528732065996552270838273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3685821377331034847225515 5528732065996552270838273)
              ·
                refine ⟨4146549049497414203128705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5528732065996552270838273 4146549049497414203128705)
                ·
                  refine ⟨3109911787123060652346529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4146549049497414203128705 3109911787123060652346529)
                  ·
                    refine ⟨2332433840342295489259897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3109911787123060652346529 2332433840342295489259897)
                    ·
                      refine ⟨1749325380256721616944923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2332433840342295489259897 1749325380256721616944923)
                      ·
                        rfl

theorem cell23_3406799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 8, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 8, 1, 2, 2, 2, 2].length) (baseStart_3406799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3406799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3406799 prefixEnd_3406799 := by exact prefixLift 3406799
  have htrace : WordTrace (prefixWord ++ tailWord_3406799) baseStart_3406799 baseEnd_3406799 := by
    simpa [prefixWord, tailWord_3406799, baseEnd_3406799] using wordTrace_append hprefix tailTrace_3406799
  have hstable : (prefixWord ++ tailWord_3406799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3406799).length < 2 ^ (prefixWord ++ tailWord_3406799).sum := by decide
  have hdescent : baseEnd_3406799 < baseStart_3406799 := by decide
  rcases family_descends (prefixWord ++ tailWord_3406799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3406805 : List Nat := [1, 3, 2, 3, 3, 1, 2, 1, 7]
def baseStart_3406805 : Nat := 118140960795 + 3406805 * 2 ^ 59
def prefixEnd_3406805 : Nat := 4983230072969 + 3 ^ 40 * 3406805 * 2
def baseEnd_3406805 : Nat := 194369829015627621496655

theorem tailTrace_3406805 : CollatzResearch.WordTrace tailWord_3406805 prefixEnd_3406805 194369829015627621496655 := by
  unfold tailWord_3406805
  simp only [CollatzResearch.WordTrace]
  refine ⟨124256386422734795816781869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82837590948489863877854579 124256386422734795816781869)
  ·
    refine ⟨46596144908525548431293201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 124256386422734795816781869 46596144908525548431293201)
    ·
      refine ⟨34947108681394161323469901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46596144908525548431293201 34947108681394161323469901)
      ·
        refine ⟨13105165755522810496301213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34947108681394161323469901 13105165755522810496301213)
        ·
          refine ⟨4914437158321053936112955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13105165755522810496301213 4914437158321053936112955)
          ·
            refine ⟨7371655737481580904169433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4914437158321053936112955 7371655737481580904169433)
            ·
              refine ⟨5528741803111185678127075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7371655737481580904169433 5528741803111185678127075)
              ·
                refine ⟨8293112704666778517190613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5528741803111185678127075 8293112704666778517190613)
                ·
                  refine ⟨194369829015627621496655, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8293112704666778517190613 194369829015627621496655)
                  ·
                    rfl

theorem cell23_3406805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 2, 1, 7].length) (baseStart_3406805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3406805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3406805 prefixEnd_3406805 := by exact prefixLift 3406805
  have htrace : WordTrace (prefixWord ++ tailWord_3406805) baseStart_3406805 baseEnd_3406805 := by
    simpa [prefixWord, tailWord_3406805, baseEnd_3406805] using wordTrace_append hprefix tailTrace_3406805
  have hstable : (prefixWord ++ tailWord_3406805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3406805).length < 2 ^ (prefixWord ++ tailWord_3406805).sum := by decide
  have hdescent : baseEnd_3406805 < baseStart_3406805 := by decide
  rcases family_descends (prefixWord ++ tailWord_3406805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3406811 : List Nat := [1, 1, 1, 1, 1, 1, 1, 2, 1, 8, 5]
def baseStart_3406811 : Nat := 118140960795 + 3406811 * 2 ^ 59
def prefixEnd_3406811 : Nat := 4983230072969 + 3 ^ 40 * 3406811 * 2
def baseEnd_3406811 : Nat := 1749331542024575569994867

theorem tailTrace_3406811 : CollatzResearch.WordTrace tailWord_3406811 prefixEnd_3406811 1749331542024575569994867 := by
  unfold tailWord_3406811
  simp only [CollatzResearch.WordTrace]
  refine ⟨124256605260713058841500287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82837736840475372561000191 124256605260713058841500287)
  ·
    refine ⟨186384907891069588262250431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124256605260713058841500287 186384907891069588262250431)
    ·
      refine ⟨279577361836604382393375647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186384907891069588262250431 279577361836604382393375647)
      ·
        refine ⟨419366042754906573590063471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 279577361836604382393375647 419366042754906573590063471)
        ·
          refine ⟨629049064132359860385095207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 419366042754906573590063471 629049064132359860385095207)
          ·
            refine ⟨943573596198539790577642811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 629049064132359860385095207 943573596198539790577642811)
            ·
              refine ⟨1415360394297809685866464217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 943573596198539790577642811 1415360394297809685866464217)
              ·
                refine ⟨1061520295723357264399848163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1415360394297809685866464217 1061520295723357264399848163)
                ·
                  refine ⟨1592280443585035896599772245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1061520295723357264399848163 1592280443585035896599772245)
                  ·
                    refine ⟨18659536448262139413278581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 1592280443585035896599772245 18659536448262139413278581)
                    ·
                      refine ⟨1749331542024575569994867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18659536448262139413278581 1749331542024575569994867)
                      ·
                        rfl

theorem cell23_3406811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 8, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 8, 5].length) (baseStart_3406811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3406811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3406811 prefixEnd_3406811 := by exact prefixLift 3406811
  have htrace : WordTrace (prefixWord ++ tailWord_3406811) baseStart_3406811 baseEnd_3406811 := by
    simpa [prefixWord, tailWord_3406811, baseEnd_3406811] using wordTrace_append hprefix tailTrace_3406811
  have hstable : (prefixWord ++ tailWord_3406811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3406811).length < 2 ^ (prefixWord ++ tailWord_3406811).sum := by decide
  have hdescent : baseEnd_3406811 < baseStart_3406811 := by decide
  rcases family_descends (prefixWord ++ tailWord_3406811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3406836 : List Nat := [2, 6, 2, 1, 1, 1, 1, 1, 2, 1, 5]
def baseStart_3406836 : Nat := 118140960795 + 3406836 * 2 ^ 59
def prefixEnd_3406836 : Nat := 4983230072969 + 3 ^ 40 * 3406836 * 2
def baseEnd_3406836 : Nat := 1749344379040937972182253

theorem tailTrace_3406836 : CollatzResearch.WordTrace tailWord_3406836 prefixEnd_3406836 1749344379040937972182253 := by
  unfold tailWord_3406836
  simp only [CollatzResearch.WordTrace]
  refine ⟨62128758542811244055580181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82838344723748325407440241 62128758542811244055580181)
  ·
    refine ⟨2912285556694277065105321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 62128758542811244055580181 2912285556694277065105321)
    ·
      refine ⟨2184214167520707798828991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2912285556694277065105321 2184214167520707798828991)
      ·
        refine ⟨3276321251281061698243487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2184214167520707798828991 3276321251281061698243487)
        ·
          refine ⟨4914481876921592547365231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3276321251281061698243487 4914481876921592547365231)
          ·
            refine ⟨7371722815382388821047847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4914481876921592547365231 7371722815382388821047847)
            ·
              refine ⟨11057584223073583231571771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7371722815382388821047847 11057584223073583231571771)
              ·
                refine ⟨16586376334610374847357657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11057584223073583231571771 16586376334610374847357657)
                ·
                  refine ⟨12439782250957781135518243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16586376334610374847357657 12439782250957781135518243)
                  ·
                    refine ⟨18659673376436671703277365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12439782250957781135518243 18659673376436671703277365)
                    ·
                      refine ⟨1749344379040937972182253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18659673376436671703277365 1749344379040937972182253)
                      ·
                        rfl

theorem cell23_3406836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 1, 1, 2, 1, 5].length) (baseStart_3406836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3406836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3406836 prefixEnd_3406836 := by exact prefixLift 3406836
  have htrace : WordTrace (prefixWord ++ tailWord_3406836) baseStart_3406836 baseEnd_3406836 := by
    simpa [prefixWord, tailWord_3406836, baseEnd_3406836] using wordTrace_append hprefix tailTrace_3406836
  have hstable : (prefixWord ++ tailWord_3406836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3406836).length < 2 ^ (prefixWord ++ tailWord_3406836).sum := by decide
  have hdescent : baseEnd_3406836 < baseStart_3406836 := by decide
  rcases family_descends (prefixWord ++ tailWord_3406836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3406855 : List Nat := [1, 1, 4, 3, 1, 1, 3, 2, 2, 1, 4]
def baseStart_3406855 : Nat := 118140960795 + 3406855 * 2 ^ 59
def prefixEnd_3406855 : Nat := 4983230072969 + 3 ^ 40 * 3406855 * 2
def baseEnd_3406855 : Nat := 1749354135173373397844665

theorem tailTrace_3406855 : CollatzResearch.WordTrace tailWord_3406855 prefixEnd_3406855 1749354135173373397844665 := by
  unfold tailWord_3406855
  simp only [CollatzResearch.WordTrace]
  refine ⟨124258210072553654356102019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82838806715035769570734679 124258210072553654356102019)
  ·
    refine ⟨186387315108830481534153029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124258210072553654356102019 186387315108830481534153029)
    ·
      refine ⟨34947621582905715287653693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 186387315108830481534153029 34947621582905715287653693)
      ·
        refine ⟨13105358093589643232870135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34947621582905715287653693 13105358093589643232870135)
        ·
          refine ⟨19658037140384464849305203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13105358093589643232870135 19658037140384464849305203)
          ·
            refine ⟨29487055710576697273957805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19658037140384464849305203 29487055710576697273957805)
            ·
              refine ⟨11057645891466261477734177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29487055710576697273957805 11057645891466261477734177)
              ·
                refine ⟨8293234418599696108300633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11057645891466261477734177 8293234418599696108300633)
                ·
                  refine ⟨6219925813949772081225475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8293234418599696108300633 6219925813949772081225475)
                  ·
                    refine ⟨9329888720924658121838213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6219925813949772081225475 9329888720924658121838213)
                    ·
                      refine ⟨1749354135173373397844665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9329888720924658121838213 1749354135173373397844665)
                      ·
                        rfl

theorem cell23_3406855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 3, 2, 2, 1, 4].length) (baseStart_3406855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3406855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3406855 prefixEnd_3406855 := by exact prefixLift 3406855
  have htrace : WordTrace (prefixWord ++ tailWord_3406855) baseStart_3406855 baseEnd_3406855 := by
    simpa [prefixWord, tailWord_3406855, baseEnd_3406855] using wordTrace_append hprefix tailTrace_3406855
  have hstable : (prefixWord ++ tailWord_3406855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3406855).length < 2 ^ (prefixWord ++ tailWord_3406855).sum := by decide
  have hdescent : baseEnd_3406855 < baseStart_3406855 := by decide
  rcases family_descends (prefixWord ++ tailWord_3406855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3406932 : List Nat := [2, 4, 1, 1, 1, 1, 2, 2, 4, 3, 2]
def baseStart_3406932 : Nat := 118140960795 + 3406932 * 2 ^ 59
def prefixEnd_3406932 : Nat := 4983230072969 + 3 ^ 40 * 3406932 * 2
def baseEnd_3406932 : Nat := 1749393673183769596581811

theorem tailTrace_3406932 : CollatzResearch.WordTrace tailWord_3406932 prefixEnd_3406932 1749393673183769596581811 := by
  unfold tailWord_3406932
  simp only [CollatzResearch.WordTrace]
  refine ⟨62130509246637348253327525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82840678995516464337770033 62130509246637348253327525)
  ·
    refine ⟨11649470483744502797498911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 62130509246637348253327525 11649470483744502797498911)
    ·
      refine ⟨17474205725616754196248367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11649470483744502797498911 17474205725616754196248367)
      ·
        refine ⟨26211308588425131294372551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17474205725616754196248367 26211308588425131294372551)
        ·
          refine ⟨39316962882637696941558827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26211308588425131294372551 39316962882637696941558827)
          ·
            refine ⟨58975444323956545412338241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39316962882637696941558827 58975444323956545412338241)
            ·
              refine ⟨44231583242967409059253681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58975444323956545412338241 44231583242967409059253681)
              ·
                refine ⟨33173687432225556794440261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44231583242967409059253681 33173687432225556794440261)
                ·
                  refine ⟨6220066393542291898957549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33173687432225556794440261 6220066393542291898957549)
                  ·
                    refine ⟨2332524897578359462109081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6220066393542291898957549 2332524897578359462109081)
                    ·
                      refine ⟨1749393673183769596581811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2332524897578359462109081 1749393673183769596581811)
                      ·
                        rfl

theorem cell23_3406932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 2, 4, 3, 2].length) (baseStart_3406932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3406932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3406932 prefixEnd_3406932 := by exact prefixLift 3406932
  have htrace : WordTrace (prefixWord ++ tailWord_3406932) baseStart_3406932 baseEnd_3406932 := by
    simpa [prefixWord, tailWord_3406932, baseEnd_3406932] using wordTrace_append hprefix tailTrace_3406932
  have hstable : (prefixWord ++ tailWord_3406932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3406932).length < 2 ^ (prefixWord ++ tailWord_3406932).sum := by decide
  have hdescent : baseEnd_3406932 < baseStart_3406932 := by decide
  rcases family_descends (prefixWord ++ tailWord_3406932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3406945 : List Nat := [1, 2, 3, 1, 1, 2, 4, 1, 3, 1, 4]
def baseStart_3406945 : Nat := 118140960795 + 3406945 * 2 ^ 59
def prefixEnd_3406945 : Nat := 4983230072969 + 3 ^ 40 * 3406945 * 2
def baseEnd_3406945 : Nat := 1749400348432278045719251

theorem tailTrace_3406945 : CollatzResearch.WordTrace tailWord_3406945 prefixEnd_3406945 1749400348432278045719251 := by
  unfold tailWord_3406945
  simp only [CollatzResearch.WordTrace]
  refine ⟨124261492642227599726878289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82840995094818399817918859 124261492642227599726878289)
  ·
    refine ⟨93196119481670699795158717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124261492642227599726878289 93196119481670699795158717)
    ·
      refine ⟨34948544805626512423184519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93196119481670699795158717 34948544805626512423184519)
      ·
        refine ⟨52422817208439768634776779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34948544805626512423184519 52422817208439768634776779)
        ·
          refine ⟨78634225812659652952165169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52422817208439768634776779 78634225812659652952165169)
          ·
            refine ⟨58975669359494739714123877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78634225812659652952165169 58975669359494739714123877)
            ·
              refine ⟨11057938004905263696398227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 58975669359494739714123877 11057938004905263696398227)
              ·
                refine ⟨16586907007357895544597341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11057938004905263696398227 16586907007357895544597341)
                ·
                  refine ⟨6220090127759210829224003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16586907007357895544597341 6220090127759210829224003)
                  ·
                    refine ⟨9330135191638816243836005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6220090127759210829224003 9330135191638816243836005)
                    ·
                      refine ⟨1749400348432278045719251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9330135191638816243836005 1749400348432278045719251)
                      ·
                        rfl

theorem cell23_3406945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 4, 1, 3, 1, 4].length) (baseStart_3406945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3406945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3406945 prefixEnd_3406945 := by exact prefixLift 3406945
  have htrace : WordTrace (prefixWord ++ tailWord_3406945) baseStart_3406945 baseEnd_3406945 := by
    simpa [prefixWord, tailWord_3406945, baseEnd_3406945] using wordTrace_append hprefix tailTrace_3406945
  have hstable : (prefixWord ++ tailWord_3406945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3406945).length < 2 ^ (prefixWord ++ tailWord_3406945).sum := by decide
  have hdescent : baseEnd_3406945 < baseStart_3406945 := by decide
  rcases family_descends (prefixWord ++ tailWord_3406945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3406962 : List Nat := [3, 2, 1, 2, 2, 1, 3, 3, 1, 1, 4]
def baseStart_3406962 : Nat := 118140960795 + 3406962 * 2 ^ 59
def prefixEnd_3406962 : Nat := 4983230072969 + 3 ^ 40 * 3406962 * 2
def baseEnd_3406962 : Nat := 1749409077603404479206673

theorem tailTrace_3406962 : CollatzResearch.WordTrace tailWord_3406962 prefixEnd_3406962 1749409077603404479206673 := by
  unfold tailWord_3406962
  simp only [CollatzResearch.WordTrace]
  refine ⟨31065528170791502907561785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82841408455444007753498093 31065528170791502907561785)
  ·
    refine ⟨23299146128093627180671339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31065528170791502907561785 23299146128093627180671339)
    ·
      refine ⟨34948719192140440771007009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23299146128093627180671339 34948719192140440771007009)
      ·
        refine ⟨26211539394105330578255257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34948719192140440771007009 26211539394105330578255257)
        ·
          refine ⟨19658654545578997933691443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26211539394105330578255257 19658654545578997933691443)
          ·
            refine ⟨29487981818368496900537165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19658654545578997933691443 29487981818368496900537165)
            ·
              refine ⟨11057993181888186337701437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29487981818368496900537165 11057993181888186337701437)
              ·
                refine ⟨4146747443208069876638039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11057993181888186337701437 4146747443208069876638039)
                ·
                  refine ⟨6220121164812104814957059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4146747443208069876638039 6220121164812104814957059)
                  ·
                    refine ⟨9330181747218157222435589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6220121164812104814957059 9330181747218157222435589)
                    ·
                      refine ⟨1749409077603404479206673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9330181747218157222435589 1749409077603404479206673)
                      ·
                        rfl

theorem cell23_3406962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 3, 3, 1, 1, 4].length) (baseStart_3406962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3406962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3406962 prefixEnd_3406962 := by exact prefixLift 3406962
  have htrace : WordTrace (prefixWord ++ tailWord_3406962) baseStart_3406962 baseEnd_3406962 := by
    simpa [prefixWord, tailWord_3406962, baseEnd_3406962] using wordTrace_append hprefix tailTrace_3406962
  have hstable : (prefixWord ++ tailWord_3406962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3406962).length < 2 ^ (prefixWord ++ tailWord_3406962).sum := by decide
  have hdescent : baseEnd_3406962 < baseStart_3406962 := by decide
  rcases family_descends (prefixWord ++ tailWord_3406962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3406979 : List Nat := [1, 1, 1, 3, 3, 2, 4, 1, 3, 2, 2]
def baseStart_3406979 : Nat := 118140960795 + 3406979 * 2 ^ 59
def prefixEnd_3406979 : Nat := 4983230072969 + 3 ^ 40 * 3406979 * 2
def baseEnd_3406979 : Nat := 1749417806774530912694095

theorem tailTrace_3406979 : CollatzResearch.WordTrace tailWord_3406979 prefixEnd_3406979 1749417806774530912694095 := by
  unfold tailWord_3406979
  simp only [CollatzResearch.WordTrace]
  refine ⟨124262732724104423533615991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82841821816069615689077327 124262732724104423533615991)
  ·
    refine ⟨186394099086156635300423987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124262732724104423533615991 186394099086156635300423987)
    ·
      refine ⟨279591148629234952950635981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186394099086156635300423987 279591148629234952950635981)
      ·
        refine ⟨104846680735963107356488493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 279591148629234952950635981 104846680735963107356488493)
        ·
          refine ⟨39317505275986165258683185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 104846680735963107356488493 39317505275986165258683185)
          ·
            refine ⟨29488128956989623944012389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39317505275986165258683185 29488128956989623944012389)
            ·
              refine ⟨5529024179435554489502323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29488128956989623944012389 5529024179435554489502323)
              ·
                refine ⟨8293536269153331734253485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5529024179435554489502323 8293536269153331734253485)
                ·
                  refine ⟨3110076100932499400345057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8293536269153331734253485 3110076100932499400345057)
                  ·
                    refine ⟨2332557075699374550258793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3110076100932499400345057 2332557075699374550258793)
                    ·
                      refine ⟨1749417806774530912694095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2332557075699374550258793 1749417806774530912694095)
                      ·
                        rfl

theorem cell23_3406979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 4, 1, 3, 2, 2].length) (baseStart_3406979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3406979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3406979 prefixEnd_3406979 := by exact prefixLift 3406979
  have htrace : WordTrace (prefixWord ++ tailWord_3406979) baseStart_3406979 baseEnd_3406979 := by
    simpa [prefixWord, tailWord_3406979, baseEnd_3406979] using wordTrace_append hprefix tailTrace_3406979
  have hstable : (prefixWord ++ tailWord_3406979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3406979).length < 2 ^ (prefixWord ++ tailWord_3406979).sum := by decide
  have hdescent : baseEnd_3406979 < baseStart_3406979 := by decide
  rcases family_descends (prefixWord ++ tailWord_3406979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3406999 : List Nat := [1, 1, 3, 3, 3, 2, 2, 2, 1, 2, 3]
def baseStart_3406999 : Nat := 118140960795 + 3406999 * 2 ^ 59
def prefixEnd_3406999 : Nat := 4983230072969 + 3 ^ 40 * 3406999 * 2
def baseEnd_3406999 : Nat := 1749428076387620834444003

theorem tailTrace_3406999 : CollatzResearch.WordTrace tailWord_3406999 prefixEnd_3406999 1749428076387620834444003 := by
  unfold tailWord_3406999
  simp only [CollatzResearch.WordTrace]
  refine ⟨124263462184031966949344051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82842308122687977966229367 124263462184031966949344051)
  ·
    refine ⟨186395193276047950424016077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124263462184031966949344051 186395193276047950424016077)
    ·
      refine ⟨69898197478517981409006029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 186395193276047950424016077 69898197478517981409006029)
      ·
        refine ⟨26211824054444243028377261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69898197478517981409006029 26211824054444243028377261)
        ·
          refine ⟨9829434020416591135641473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26211824054444243028377261 9829434020416591135641473)
          ·
            refine ⟨7372075515312443351731105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9829434020416591135641473 7372075515312443351731105)
            ·
              refine ⟨5529056636484332513798329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7372075515312443351731105 5529056636484332513798329)
              ·
                refine ⟨4146792477363249385348747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5529056636484332513798329 4146792477363249385348747)
                ·
                  refine ⟨6220188716044874078023121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4146792477363249385348747 6220188716044874078023121)
                  ·
                    refine ⟨4665141537033655558517341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6220188716044874078023121 4665141537033655558517341)
                    ·
                      refine ⟨1749428076387620834444003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4665141537033655558517341 1749428076387620834444003)
                      ·
                        rfl

theorem cell23_3406999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 2, 2, 1, 2, 3].length) (baseStart_3406999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3406999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3406999 prefixEnd_3406999 := by exact prefixLift 3406999
  have htrace : WordTrace (prefixWord ++ tailWord_3406999) baseStart_3406999 baseEnd_3406999 := by
    simpa [prefixWord, tailWord_3406999, baseEnd_3406999] using wordTrace_append hprefix tailTrace_3406999
  have hstable : (prefixWord ++ tailWord_3406999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3406999).length < 2 ^ (prefixWord ++ tailWord_3406999).sum := by decide
  have hdescent : baseEnd_3406999 < baseStart_3406999 := by decide
  rcases family_descends (prefixWord ++ tailWord_3406999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3407002 : List Nat := [3, 1, 1, 5, 1, 1, 4, 7]
def baseStart_3407002 : Nat := 118140960795 + 3407002 * 2 ^ 59
def prefixEnd_3407002 : Nat := 4983230072969 + 3 ^ 40 * 3407002 * 2
def baseEnd_3407002 : Nat := 64793689512206826766907

theorem tailTrace_3407002 : CollatzResearch.WordTrace tailWord_3407002 prefixEnd_3407002 64793689512206826766907 := by
  unfold tailWord_3407002
  simp only [CollatzResearch.WordTrace]
  refine ⟨31065892900755274615425815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82842381068680732307802173 31065892900755274615425815)
  ·
    refine ⟨46598839351132911923138723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31065892900755274615425815 46598839351132911923138723)
    ·
      refine ⟨69898259026699367884708085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46598839351132911923138723 69898259026699367884708085)
      ·
        refine ⟨6552961783753065739191383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 69898259026699367884708085 6552961783753065739191383)
        ·
          refine ⟨9829442675629598608787075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6552961783753065739191383 9829442675629598608787075)
          ·
            refine ⟨14744164013444397913180613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9829442675629598608787075 14744164013444397913180613)
            ·
              refine ⟨2764530752520824608721365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14744164013444397913180613 2764530752520824608721365)
              ·
                refine ⟨64793689512206826766907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2764530752520824608721365 64793689512206826766907)
                ·
                  rfl

theorem cell23_3407002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 4, 7].length) (baseStart_3407002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3407002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3407002 prefixEnd_3407002 := by exact prefixLift 3407002
  have htrace : WordTrace (prefixWord ++ tailWord_3407002) baseStart_3407002 baseEnd_3407002 := by
    simpa [prefixWord, tailWord_3407002, baseEnd_3407002] using wordTrace_append hprefix tailTrace_3407002
  have hstable : (prefixWord ++ tailWord_3407002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3407002).length < 2 ^ (prefixWord ++ tailWord_3407002).sum := by decide
  have hdescent : baseEnd_3407002 < baseStart_3407002 := by decide
  rcases family_descends (prefixWord ++ tailWord_3407002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3407013 : List Nat := [1, 3, 1, 2, 1, 6, 1, 3, 1, 2, 2]
def baseStart_3407013 : Nat := 118140960795 + 3407013 * 2 ^ 59
def prefixEnd_3407013 : Nat := 4983230072969 + 3 ^ 40 * 3407013 * 2
def baseEnd_3407013 : Nat := 1749435265116783779668939

theorem tailTrace_3407013 : CollatzResearch.WordTrace tailWord_3407013 prefixEnd_3407013 1749435265116783779668939 := by
  unfold tailWord_3407013
  simp only [CollatzResearch.WordTrace]
  refine ⟨124263972805981247340353693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82842648537320831560235795 124263972805981247340353693)
  ·
    refine ⟨46598989802242967752632635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 124263972805981247340353693 46598989802242967752632635)
    ·
      refine ⟨69898484703364451628948953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46598989802242967752632635 69898484703364451628948953)
      ·
        refine ⟨52423863527523338721711715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69898484703364451628948953 52423863527523338721711715)
        ·
          refine ⟨78635795291285008082567573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52423863527523338721711715 78635795291285008082567573)
          ·
            refine ⟨3686052904278984753870355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 78635795291285008082567573 3686052904278984753870355)
            ·
              refine ⟨5529079356418477130805533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3686052904278984753870355 5529079356418477130805533)
              ·
                refine ⟨2073404758656928924052075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5529079356418477130805533 2073404758656928924052075)
                ·
                  refine ⟨3110107137985393386078113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2073404758656928924052075 3110107137985393386078113)
                  ·
                    refine ⟨2332580353489045039558585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3110107137985393386078113 2332580353489045039558585)
                    ·
                      refine ⟨1749435265116783779668939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2332580353489045039558585 1749435265116783779668939)
                      ·
                        rfl

theorem cell23_3407013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 6, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 6, 1, 3, 1, 2, 2].length) (baseStart_3407013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3407013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3407013 prefixEnd_3407013 := by exact prefixLift 3407013
  have htrace : WordTrace (prefixWord ++ tailWord_3407013) baseStart_3407013 baseEnd_3407013 := by
    simpa [prefixWord, tailWord_3407013, baseEnd_3407013] using wordTrace_append hprefix tailTrace_3407013
  have hstable : (prefixWord ++ tailWord_3407013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3407013).length < 2 ^ (prefixWord ++ tailWord_3407013).sum := by decide
  have hdescent : baseEnd_3407013 < baseStart_3407013 := by decide
  rcases family_descends (prefixWord ++ tailWord_3407013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3407055 : List Nat := [1, 1, 2, 1, 1, 3, 2, 1, 4, 4, 3]
def baseStart_3407055 : Nat := 118140960795 + 3407055 * 2 ^ 59
def prefixEnd_3407055 : Nat := 4983230072969 + 3 ^ 40 * 3407055 * 2
def baseEnd_3407055 : Nat := 1749456831304272615343745

theorem tailTrace_3407055 : CollatzResearch.WordTrace tailWord_3407055 prefixEnd_3407055 1749456831304272615343745 := by
  unfold tailWord_3407055
  simp only [CollatzResearch.WordTrace]
  refine ⟨124265504671829088513382619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82843669781219392342255079 124265504671829088513382619)
  ·
    refine ⟨186398257007743632770073929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124265504671829088513382619 186398257007743632770073929)
    ·
      refine ⟨139798692755807724577555447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 186398257007743632770073929 139798692755807724577555447)
      ·
        refine ⟨209698039133711586866333171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139798692755807724577555447 209698039133711586866333171)
        ·
          refine ⟨314547058700567380299499757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 209698039133711586866333171 314547058700567380299499757)
          ·
            refine ⟨117955147012712767612312409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 314547058700567380299499757 117955147012712767612312409)
            ·
              refine ⟨88466360259534575709234307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 117955147012712767612312409 88466360259534575709234307)
              ·
                refine ⟨132699540389301863563851461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 88466360259534575709234307 132699540389301863563851461)
                ·
                  refine ⟨24881163822994099418222149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 132699540389301863563851461 24881163822994099418222149)
                  ·
                    refine ⟨4665218216811393640916653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24881163822994099418222149 4665218216811393640916653)
                    ·
                      refine ⟨1749456831304272615343745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4665218216811393640916653 1749456831304272615343745)
                      ·
                        rfl

theorem cell23_3407055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 1, 4, 4, 3].length) (baseStart_3407055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3407055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3407055 prefixEnd_3407055 := by exact prefixLift 3407055
  have htrace : WordTrace (prefixWord ++ tailWord_3407055) baseStart_3407055 baseEnd_3407055 := by
    simpa [prefixWord, tailWord_3407055, baseEnd_3407055] using wordTrace_append hprefix tailTrace_3407055
  have hstable : (prefixWord ++ tailWord_3407055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3407055).length < 2 ^ (prefixWord ++ tailWord_3407055).sum := by decide
  have hdescent : baseEnd_3407055 < baseStart_3407055 := by decide
  rcases family_descends (prefixWord ++ tailWord_3407055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3407065 : List Nat := [1, 2, 1, 2, 3, 1, 1, 2, 4, 2, 4]
def baseStart_3407065 : Nat := 118140960795 + 3407065 * 2 ^ 59
def prefixEnd_3407065 : Nat := 4983230072969 + 3 ^ 40 * 3407065 * 2
def baseEnd_3407065 : Nat := 1749461966110817576218699

theorem tailTrace_3407065 : CollatzResearch.WordTrace tailWord_3407065 prefixEnd_3407065 1749461966110817576218699 := by
  unfold tailWord_3407065
  simp only [CollatzResearch.WordTrace]
  refine ⟨124265869401792860221246649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82843912934528573480831099 124265869401792860221246649)
  ·
    refine ⟨93199402051344645165934987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124265869401792860221246649 93199402051344645165934987)
    ·
      refine ⟨139799103077016967748902481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93199402051344645165934987 139799103077016967748902481)
      ·
        refine ⟨104849327307762725811676861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 139799103077016967748902481 104849327307762725811676861)
        ·
          refine ⟨39318497740411022179378823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 104849327307762725811676861 39318497740411022179378823)
          ·
            refine ⟨58977746610616533269068235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39318497740411022179378823 58977746610616533269068235)
            ·
              refine ⟨88466619915924799903602353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58977746610616533269068235 88466619915924799903602353)
              ·
                refine ⟨66349964936943599927701765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 88466619915924799903602353 66349964936943599927701765)
                ·
                  refine ⟨12440618425676924986444081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 66349964936943599927701765 12440618425676924986444081)
                  ·
                    refine ⟨9330463819257693739833061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12440618425676924986444081 9330463819257693739833061)
                    ·
                      refine ⟨1749461966110817576218699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9330463819257693739833061 1749461966110817576218699)
                      ·
                        rfl

theorem cell23_3407065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 2, 4, 2, 4].length) (baseStart_3407065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3407065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3407065 prefixEnd_3407065 := by exact prefixLift 3407065
  have htrace : WordTrace (prefixWord ++ tailWord_3407065) baseStart_3407065 baseEnd_3407065 := by
    simpa [prefixWord, tailWord_3407065, baseEnd_3407065] using wordTrace_append hprefix tailTrace_3407065
  have hstable : (prefixWord ++ tailWord_3407065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3407065).length < 2 ^ (prefixWord ++ tailWord_3407065).sum := by decide
  have hdescent : baseEnd_3407065 < baseStart_3407065 := by decide
  rcases family_descends (prefixWord ++ tailWord_3407065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3407086 : List Nat := [4, 1, 2, 1, 1, 1, 3, 4, 2, 2, 2]
def baseStart_3407086 : Nat := 118140960795 + 3407086 * 2 ^ 59
def prefixEnd_3407086 : Nat := 4983230072969 + 3 ^ 40 * 3407086 * 2
def baseEnd_3407086 : Nat := 1749472749204561994056103

theorem tailTrace_3407086 : CollatzResearch.WordTrace tailWord_3407086 prefixEnd_3407086 1749472749204561994056103 := by
  unfold tailWord_3407086
  simp only [CollatzResearch.WordTrace]
  refine ⟨15533329416839597600970139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 82844423556477853871840741 15533329416839597600970139)
  ·
    refine ⟨23299994125259396401455209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15533329416839597600970139 23299994125259396401455209)
    ·
      refine ⟨17474995593944547301091407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23299994125259396401455209 17474995593944547301091407)
      ·
        refine ⟨26212493390916820951637111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17474995593944547301091407 26212493390916820951637111)
        ·
          refine ⟨39318740086375231427455667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26212493390916820951637111 39318740086375231427455667)
          ·
            refine ⟨58978110129562847141183501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39318740086375231427455667 58978110129562847141183501)
            ·
              refine ⟨22116791298586067677943813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58978110129562847141183501 22116791298586067677943813)
              ·
                refine ⟨4146898368484887689614465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22116791298586067677943813 4146898368484887689614465)
                ·
                  refine ⟨3110173776363665767210849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4146898368484887689614465 3110173776363665767210849)
                  ·
                    refine ⟨2332630332272749325408137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3110173776363665767210849 2332630332272749325408137)
                    ·
                      refine ⟨1749472749204561994056103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2332630332272749325408137 1749472749204561994056103)
                      ·
                        rfl

theorem cell23_3407086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 3, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 3, 4, 2, 2, 2].length) (baseStart_3407086 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3407086 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3407086 prefixEnd_3407086 := by exact prefixLift 3407086
  have htrace : WordTrace (prefixWord ++ tailWord_3407086) baseStart_3407086 baseEnd_3407086 := by
    simpa [prefixWord, tailWord_3407086, baseEnd_3407086] using wordTrace_append hprefix tailTrace_3407086
  have hstable : (prefixWord ++ tailWord_3407086).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3407086).length < 2 ^ (prefixWord ++ tailWord_3407086).sum := by decide
  have hdescent : baseEnd_3407086 < baseStart_3407086 := by decide
  rcases family_descends (prefixWord ++ tailWord_3407086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3407162 : List Nat := [3, 1, 1, 1, 4, 1, 1, 1, 3, 4, 3]
def baseStart_3407162 : Nat := 118140960795 + 3407162 * 2 ^ 59
def prefixEnd_3407162 : Nat := 4983230072969 + 3 ^ 40 * 3407162 * 2
def baseEnd_3407162 : Nat := 1749511773734303696705753

theorem tailTrace_3407162 : CollatzResearch.WordTrace tailWord_3407162 prefixEnd_3407162 1749511773734303696705753 := by
  unfold tailWord_3407162
  simp only [CollatzResearch.WordTrace]
  refine ⟨31067351820610361446881935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82846271521627630525018493 31067351820610361446881935)
  ·
    refine ⟨46601027730915542170322903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31067351820610361446881935 46601027730915542170322903)
    ·
      refine ⟨69901541596373313255484355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46601027730915542170322903 69901541596373313255484355)
      ·
        refine ⟨104852312394559969883226533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69901541596373313255484355 104852312394559969883226533)
        ·
          refine ⟨19659808573979994353104975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 104852312394559969883226533 19659808573979994353104975)
          ·
            refine ⟨29489712860969991529657463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19659808573979994353104975 29489712860969991529657463)
            ·
              refine ⟨44234569291454987294486195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29489712860969991529657463 44234569291454987294486195)
              ·
                refine ⟨66351853937182480941729293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44234569291454987294486195 66351853937182480941729293)
                ·
                  refine ⟨24881945226443430353148485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 66351853937182480941729293 24881945226443430353148485)
                  ·
                    refine ⟨4665364729958143191215341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24881945226443430353148485 4665364729958143191215341)
                    ·
                      refine ⟨1749511773734303696705753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4665364729958143191215341 1749511773734303696705753)
                      ·
                        rfl

theorem cell23_3407162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 1, 3, 4, 3].length) (baseStart_3407162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3407162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3407162 prefixEnd_3407162 := by exact prefixLift 3407162
  have htrace : WordTrace (prefixWord ++ tailWord_3407162) baseStart_3407162 baseEnd_3407162 := by
    simpa [prefixWord, tailWord_3407162, baseEnd_3407162] using wordTrace_append hprefix tailTrace_3407162
  have hstable : (prefixWord ++ tailWord_3407162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3407162).length < 2 ^ (prefixWord ++ tailWord_3407162).sum := by decide
  have hdescent : baseEnd_3407162 < baseStart_3407162 := by decide
  rcases family_descends (prefixWord ++ tailWord_3407162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3407190 : List Nat := [5, 2, 3, 1, 1, 1, 1, 2, 2, 5]
def baseStart_3407190 : Nat := 118140960795 + 3407190 * 2 ^ 59
def prefixEnd_3407190 : Nat := 4983230072969 + 3 ^ 40 * 3407190 * 2
def baseEnd_3407190 : Nat := 583175383730876529051875

theorem tailTrace_3407190 : CollatzResearch.WordTrace tailWord_3407190 prefixEnd_3407190 583175383730876529051875 := by
  unfold tailWord_3407190
  simp only [CollatzResearch.WordTrace]
  refine ⟨7766901782896250410596689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 82846952350893337713031349 7766901782896250410596689)
  ·
    refine ⟨5825176337172187807947517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7766901782896250410596689 5825176337172187807947517)
    ·
      refine ⟨2184441126439570427980319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5825176337172187807947517 2184441126439570427980319)
      ·
        refine ⟨3276661689659355641970479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2184441126439570427980319 3276661689659355641970479)
        ·
          refine ⟨4914992534489033462955719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3276661689659355641970479 4914992534489033462955719)
          ·
            refine ⟨7372488801733550194433579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4914992534489033462955719 7372488801733550194433579)
            ·
              refine ⟨11058733202600325291650369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7372488801733550194433579 11058733202600325291650369)
              ·
                refine ⟨8294049901950243968737777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11058733202600325291650369 8294049901950243968737777)
                ·
                  refine ⟨6220537426462682976553333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8294049901950243968737777 6220537426462682976553333)
                  ·
                    refine ⟨583175383730876529051875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6220537426462682976553333 583175383730876529051875)
                    ·
                      rfl

theorem cell23_3407190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 1, 2, 2, 5].length) (baseStart_3407190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3407190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3407190 prefixEnd_3407190 := by exact prefixLift 3407190
  have htrace : WordTrace (prefixWord ++ tailWord_3407190) baseStart_3407190 baseEnd_3407190 := by
    simpa [prefixWord, tailWord_3407190, baseEnd_3407190] using wordTrace_append hprefix tailTrace_3407190
  have hstable : (prefixWord ++ tailWord_3407190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3407190).length < 2 ^ (prefixWord ++ tailWord_3407190).sum := by decide
  have hdescent : baseEnd_3407190 < baseStart_3407190 := by decide
  rcases family_descends (prefixWord ++ tailWord_3407190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3407203 : List Nat := [1, 1, 1, 5, 2, 3, 3, 2, 1, 4]
def baseStart_3407203 : Nat := 118140960795 + 3407203 * 2 ^ 59
def prefixEnd_3407203 : Nat := 4983230072969 + 3 ^ 40 * 3407203 * 2
def baseEnd_3407203 : Nat := 583177608813712678764355

theorem tailTrace_3407203 : CollatzResearch.WordTrace tailWord_3407203 prefixEnd_3407203 583177608813712678764355 := by
  unfold tailWord_3407203
  simp only [CollatzResearch.WordTrace]
  refine ⟨124270902675292909789770263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82847268450195273193180175 124270902675292909789770263)
  ·
    refine ⟨186406354012939364684655395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124270902675292909789770263 186406354012939364684655395)
    ·
      refine ⟨279609531019409047026983093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186406354012939364684655395 279609531019409047026983093)
      ·
        refine ⟨26213393533069598158779665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 279609531019409047026983093 26213393533069598158779665)
        ·
          refine ⟨19660045149802198619084749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26213393533069598158779665 19660045149802198619084749)
          ·
            refine ⟨7372516931175824482156781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19660045149802198619084749 7372516931175824482156781)
            ·
              refine ⟨2764693849190934180808793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7372516931175824482156781 2764693849190934180808793)
              ·
                refine ⟨2073520386893200635606595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2764693849190934180808793 2073520386893200635606595)
                ·
                  refine ⟨3110280580339800953409893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2073520386893200635606595 3110280580339800953409893)
                  ·
                    refine ⟨583177608813712678764355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3110280580339800953409893 583177608813712678764355)
                    ·
                      rfl

theorem cell23_3407203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 3, 2, 1, 4].length) (baseStart_3407203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3407203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3407203 prefixEnd_3407203 := by exact prefixLift 3407203
  have htrace : WordTrace (prefixWord ++ tailWord_3407203) baseStart_3407203 baseEnd_3407203 := by
    simpa [prefixWord, tailWord_3407203, baseEnd_3407203] using wordTrace_append hprefix tailTrace_3407203
  have hstable : (prefixWord ++ tailWord_3407203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3407203).length < 2 ^ (prefixWord ++ tailWord_3407203).sum := by decide
  have hdescent : baseEnd_3407203 < baseStart_3407203 := by decide
  rcases family_descends (prefixWord ++ tailWord_3407203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3407209 : List Nat := [1, 2, 1, 1, 1, 3, 2, 5, 3, 1, 3]
def baseStart_3407209 : Nat := 118140960795 + 3407209 * 2 ^ 59
def prefixEnd_3407209 : Nat := 4983230072969 + 3 ^ 40 * 3407209 * 2
def baseEnd_3407209 : Nat := 1749535907325065012818037

theorem tailTrace_3407209 : CollatzResearch.WordTrace tailWord_3407209 prefixEnd_3407209 1749535907325065012818037 := by
  unfold tailWord_3407209
  simp only [CollatzResearch.WordTrace]
  refine ⟨124271121513271172814488681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82847414342180781876325787 124271121513271172814488681)
  ·
    refine ⟨93203341134953379610866511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124271121513271172814488681 93203341134953379610866511)
    ·
      refine ⟨139805011702430069416299767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93203341134953379610866511 139805011702430069416299767)
      ·
        refine ⟨209707517553645104124449651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139805011702430069416299767 209707517553645104124449651)
        ·
          refine ⟨314561276330467656186674477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 209707517553645104124449651 314561276330467656186674477)
          ·
            refine ⟨117960478623925371070002929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 314561276330467656186674477 117960478623925371070002929)
            ·
              refine ⟨88470358967944028302502197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 117960478623925371070002929 88470358967944028302502197)
              ·
                refine ⟨8294096153244752653359581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 88470358967944028302502197 8294096153244752653359581)
                ·
                  refine ⟨3110286057466782245009843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8294096153244752653359581 3110286057466782245009843)
                  ·
                    refine ⟨4665429086200173367514765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3110286057466782245009843 4665429086200173367514765)
                    ·
                      refine ⟨1749535907325065012818037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4665429086200173367514765 1749535907325065012818037)
                      ·
                        rfl

theorem cell23_3407209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 5, 3, 1, 3].length) (baseStart_3407209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3407209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3407209 prefixEnd_3407209 := by exact prefixLift 3407209
  have htrace : WordTrace (prefixWord ++ tailWord_3407209) baseStart_3407209 baseEnd_3407209 := by
    simpa [prefixWord, tailWord_3407209, baseEnd_3407209] using wordTrace_append hprefix tailTrace_3407209
  have hstable : (prefixWord ++ tailWord_3407209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3407209).length < 2 ^ (prefixWord ++ tailWord_3407209).sum := by decide
  have hdescent : baseEnd_3407209 < baseStart_3407209 := by decide
  rcases family_descends (prefixWord ++ tailWord_3407209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3407230 : List Nat := [4, 2, 3, 2, 1, 1, 2, 1, 2, 2, 3]
def baseStart_3407230 : Nat := 118140960795 + 3407230 * 2 ^ 59
def prefixEnd_3407230 : Nat := 4983230072969 + 3 ^ 40 * 3407230 * 2
def baseEnd_3407230 : Nat := 1749546690418809430655441

theorem tailTrace_3407230 : CollatzResearch.WordTrace tailWord_3407230 prefixEnd_3407230 1749546690418809430655441 := by
  unfold tailWord_3407230
  simp only [CollatzResearch.WordTrace]
  refine ⟨15533985930774386675125393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 82847924964130062267335429 15533985930774386675125393)
  ·
    refine ⟨11650489448080790006344045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15533985930774386675125393 11650489448080790006344045)
    ·
      refine ⟨4368933543030296252379017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11650489448080790006344045 4368933543030296252379017)
      ·
        refine ⟨3276700157272722189284263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4368933543030296252379017 3276700157272722189284263)
        ·
          refine ⟨4915050235909083283926395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3276700157272722189284263 4915050235909083283926395)
          ·
            refine ⟨7372575353863624925889593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4915050235909083283926395 7372575353863624925889593)
            ·
              refine ⟨5529431515397718694417195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7372575353863624925889593 5529431515397718694417195)
              ·
                refine ⟨8294147273096578041625793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5529431515397718694417195 8294147273096578041625793)
                ·
                  refine ⟨6220610454822433531219345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8294147273096578041625793 6220610454822433531219345)
                  ·
                    refine ⟨4665457841116825148414509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6220610454822433531219345 4665457841116825148414509)
                    ·
                      refine ⟨1749546690418809430655441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4665457841116825148414509 1749546690418809430655441)
                      ·
                        rfl

theorem cell23_3407230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 2, 1, 2, 2, 3].length) (baseStart_3407230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3407230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3407230 prefixEnd_3407230 := by exact prefixLift 3407230
  have htrace : WordTrace (prefixWord ++ tailWord_3407230) baseStart_3407230 baseEnd_3407230 := by
    simpa [prefixWord, tailWord_3407230, baseEnd_3407230] using wordTrace_append hprefix tailTrace_3407230
  have hstable : (prefixWord ++ tailWord_3407230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3407230).length < 2 ^ (prefixWord ++ tailWord_3407230).sum := by decide
  have hdescent : baseEnd_3407230 < baseStart_3407230 := by decide
  rcases family_descends (prefixWord ++ tailWord_3407230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3407236 : List Nat := [2, 3, 2, 1, 1, 3, 1, 3, 2, 3, 2]
def baseStart_3407236 : Nat := 118140960795 + 3407236 * 2 ^ 59
def prefixEnd_3407236 : Nat := 4983230072969 + 3 ^ 40 * 3407236 * 2
def baseEnd_3407236 : Nat := 1749549771302736407180413

theorem tailTrace_3407236 : CollatzResearch.WordTrace tailWord_3407236 prefixEnd_3407236 1749549771302736407180413 := by
  unfold tailWord_3407236
  simp only [CollatzResearch.WordTrace]
  refine ⟨62136053142086678212860781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82848070856115570950481041 62136053142086678212860781)
  ·
    refine ⟨23301019928282504329822793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62136053142086678212860781 23301019928282504329822793)
    ·
      refine ⟨17475764946211878247367095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23301019928282504329822793 17475764946211878247367095)
      ·
        refine ⟨26213647419317817371050643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17475764946211878247367095 26213647419317817371050643)
        ·
          refine ⟨39320471128976726056575965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26213647419317817371050643 39320471128976726056575965)
          ·
            refine ⟨14745176673366272271215987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39320471128976726056575965 14745176673366272271215987)
            ·
              refine ⟨22117765010049408406823981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14745176673366272271215987 22117765010049408406823981)
              ·
                refine ⟨8294161878768528152558993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22117765010049408406823981 8294161878768528152558993)
                ·
                  refine ⟨6220621409076396114419245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8294161878768528152558993 6220621409076396114419245)
                  ·
                    refine ⟨2332733028403648542907217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6220621409076396114419245 2332733028403648542907217)
                    ·
                      refine ⟨1749549771302736407180413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2332733028403648542907217 1749549771302736407180413)
                      ·
                        rfl

theorem cell23_3407236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 1, 3, 2, 3, 2].length) (baseStart_3407236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3407236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3407236 prefixEnd_3407236 := by exact prefixLift 3407236
  have htrace : WordTrace (prefixWord ++ tailWord_3407236) baseStart_3407236 baseEnd_3407236 := by
    simpa [prefixWord, tailWord_3407236, baseEnd_3407236] using wordTrace_append hprefix tailTrace_3407236
  have hstable : (prefixWord ++ tailWord_3407236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3407236).length < 2 ^ (prefixWord ++ tailWord_3407236).sum := by decide
  have hdescent : baseEnd_3407236 < baseStart_3407236 := by decide
  rcases family_descends (prefixWord ++ tailWord_3407236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3407299 : List Nat := [1, 1, 1, 3, 1, 1, 6, 2, 1, 3, 3]
def baseStart_3407299 : Nat := 118140960795 + 3407299 * 2 ^ 59
def prefixEnd_3407299 : Nat := 4983230072969 + 3 ^ 40 * 3407299 * 2
def baseEnd_3407299 : Nat := 1749582120583969660692623

theorem tailTrace_3407299 : CollatzResearch.WordTrace tailWord_3407299 prefixEnd_3407299 1749582120583969660692623 := by
  unfold tailWord_3407299
  simp only [CollatzResearch.WordTrace]
  refine ⟨124274404082945118185264951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82849602721963412123509967 124274404082945118185264951)
  ·
    refine ⟨186411606124417677277897427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124274404082945118185264951 186411606124417677277897427)
    ·
      refine ⟨279617409186626515916846141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186411606124417677277897427 279617409186626515916846141)
      ·
        refine ⟨104856528444984943468817303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 279617409186626515916846141 104856528444984943468817303)
        ·
          refine ⟨157284792667477415203225955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104856528444984943468817303 157284792667477415203225955)
          ·
            refine ⟨235927189001216122804838933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 157284792667477415203225955 235927189001216122804838933)
            ·
              refine ⟨11059086984432005756476825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 235927189001216122804838933 11059086984432005756476825)
              ·
                refine ⟨8294315238324004317357619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11059086984432005756476825 8294315238324004317357619)
                ·
                  refine ⟨12441472857486006476036429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8294315238324004317357619 12441472857486006476036429)
                  ·
                    refine ⟨4665552321557252428513661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12441472857486006476036429 4665552321557252428513661)
                    ·
                      refine ⟨1749582120583969660692623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4665552321557252428513661 1749582120583969660692623)
                      ·
                        rfl

theorem cell23_3407299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 6, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 6, 2, 1, 3, 3].length) (baseStart_3407299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3407299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3407299 prefixEnd_3407299 := by exact prefixLift 3407299
  have htrace : WordTrace (prefixWord ++ tailWord_3407299) baseStart_3407299 baseEnd_3407299 := by
    simpa [prefixWord, tailWord_3407299, baseEnd_3407299] using wordTrace_append hprefix tailTrace_3407299
  have hstable : (prefixWord ++ tailWord_3407299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3407299).length < 2 ^ (prefixWord ++ tailWord_3407299).sum := by decide
  have hdescent : baseEnd_3407299 < baseStart_3407299 := by decide
  rcases family_descends (prefixWord ++ tailWord_3407299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3407300 : List Nat := [2, 3, 3, 2, 1, 3, 2, 1, 1, 1, 4]
def baseStart_3407300 : Nat := 118140960795 + 3407300 * 2 ^ 59
def prefixEnd_3407300 : Nat := 4983230072969 + 3 ^ 40 * 3407300 * 2
def baseEnd_3407300 : Nat := 1749582634064624156780119

theorem tailTrace_3407300 : CollatzResearch.WordTrace tailWord_3407300 prefixEnd_3407300 1749582634064624156780119 := by
  unfold tailWord_3407300
  simp only [CollatzResearch.WordTrace]
  refine ⟨62137220277970747678025677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82849627037294330237367569 62137220277970747678025677)
  ·
    refine ⟨23301457604239030379259629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62137220277970747678025677 23301457604239030379259629)
    ·
      refine ⟨8738046601589636392222361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23301457604239030379259629 8738046601589636392222361)
      ·
        refine ⟨6553534951192227294166771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8738046601589636392222361 6553534951192227294166771)
        ·
          refine ⟨9830302426788340941250157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6553534951192227294166771 9830302426788340941250157)
          ·
            refine ⟨3686363410045627852968809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9830302426788340941250157 3686363410045627852968809)
            ·
              refine ⟨2764772557534220889726607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3686363410045627852968809 2764772557534220889726607)
              ·
                refine ⟨4147158836301331334589911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2764772557534220889726607 4147158836301331334589911)
                ·
                  refine ⟨6220738254451997001884867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4147158836301331334589911 6220738254451997001884867)
                  ·
                    refine ⟨9331107381677995502827301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6220738254451997001884867 9331107381677995502827301)
                    ·
                      refine ⟨1749582634064624156780119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9331107381677995502827301 1749582634064624156780119)
                      ·
                        rfl

theorem cell23_3407300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 3, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 3, 2, 1, 1, 1, 4].length) (baseStart_3407300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3407300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3407300 prefixEnd_3407300 := by exact prefixLift 3407300
  have htrace : WordTrace (prefixWord ++ tailWord_3407300) baseStart_3407300 baseEnd_3407300 := by
    simpa [prefixWord, tailWord_3407300, baseEnd_3407300] using wordTrace_append hprefix tailTrace_3407300
  have hstable : (prefixWord ++ tailWord_3407300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3407300).length < 2 ^ (prefixWord ++ tailWord_3407300).sum := by decide
  have hdescent : baseEnd_3407300 < baseStart_3407300 := by decide
  rcases family_descends (prefixWord ++ tailWord_3407300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3407312 : List Nat := [2, 1, 1, 1, 1, 2, 2, 4, 2, 2, 5]
def baseStart_3407312 : Nat := 118140960795 + 3407312 * 2 ^ 59
def prefixEnd_3407312 : Nat := 4983230072969 + 3 ^ 40 * 3407312 * 2
def baseEnd_3407312 : Nat := 1749588795832478109830063

theorem tailTrace_3407312 : CollatzResearch.WordTrace tailWord_3407312 prefixEnd_3407312 1749588795832478109830063 := by
  unfold tailWord_3407312
  simp only [CollatzResearch.WordTrace]
  refine ⟨62137439115949010702744095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82849918821265347603658793 62137439115949010702744095)
  ·
    refine ⟨93206158673923516054116143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62137439115949010702744095 93206158673923516054116143)
    ·
      refine ⟨139809238010885274081174215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93206158673923516054116143 139809238010885274081174215)
      ·
        refine ⟨209713857016327911121761323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139809238010885274081174215 209713857016327911121761323)
        ·
          refine ⟨314570785524491866682641985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 209713857016327911121761323 314570785524491866682641985)
          ·
            refine ⟨235928089143368900011981489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 314570785524491866682641985 235928089143368900011981489)
            ·
              refine ⟨176946066857526675008986117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 235928089143368900011981489 176946066857526675008986117)
              ·
                refine ⟨33177387535786251564184897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 176946066857526675008986117 33177387535786251564184897)
                ·
                  refine ⟨24883040651839688673138673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33177387535786251564184897 24883040651839688673138673)
                  ·
                    refine ⟨18662280488879766504854005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24883040651839688673138673 18662280488879766504854005)
                    ·
                      refine ⟨1749588795832478109830063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18662280488879766504854005 1749588795832478109830063)
                      ·
                        rfl

theorem cell23_3407312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 4, 2, 2, 5].length) (baseStart_3407312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3407312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3407312 prefixEnd_3407312 := by exact prefixLift 3407312
  have htrace : WordTrace (prefixWord ++ tailWord_3407312) baseStart_3407312 baseEnd_3407312 := by
    simpa [prefixWord, tailWord_3407312, baseEnd_3407312] using wordTrace_append hprefix tailTrace_3407312
  have hstable : (prefixWord ++ tailWord_3407312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3407312).length < 2 ^ (prefixWord ++ tailWord_3407312).sum := by decide
  have hdescent : baseEnd_3407312 < baseStart_3407312 := by decide
  rcases family_descends (prefixWord ++ tailWord_3407312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3407333 : List Nat := [1, 3, 1, 5, 1, 3, 1, 1, 1, 3, 3]
def baseStart_3407333 : Nat := 118140960795 + 3407333 * 2 ^ 59
def prefixEnd_3407333 : Nat := 4983230072969 + 3 ^ 40 * 3407333 * 2
def baseEnd_3407333 : Nat := 1749599578926222527667467

theorem tailTrace_3407333 : CollatzResearch.WordTrace tailWord_3407333 prefixEnd_3407333 1749599578926222527667467 := by
  unfold tailWord_3407333
  simp only [CollatzResearch.WordTrace]
  refine ⟨124275644164821941992002653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82850429443214627994668435 124275644164821941992002653)
  ·
    refine ⟨46603366561808228247000995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 124275644164821941992002653 46603366561808228247000995)
    ·
      refine ⟨69905049842712342370501493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46603366561808228247000995 69905049842712342370501493)
      ·
        refine ⟨6553598422754282097234515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 69905049842712342370501493 6553598422754282097234515)
        ·
          refine ⟨9830397634131423145851773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6553598422754282097234515 9830397634131423145851773)
          ·
            refine ⟨3686399112799283679694415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9830397634131423145851773 3686399112799283679694415)
            ·
              refine ⟨5529598669198925519541623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3686399112799283679694415 5529598669198925519541623)
              ·
                refine ⟨8294398003798388279312435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5529598669198925519541623 8294398003798388279312435)
                ·
                  refine ⟨12441597005697582418968653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8294398003798388279312435 12441597005697582418968653)
                  ·
                    refine ⟨4665598877136593407113245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12441597005697582418968653 4665598877136593407113245)
                    ·
                      refine ⟨1749599578926222527667467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4665598877136593407113245 1749599578926222527667467)
                      ·
                        rfl

theorem cell23_3407333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 3, 1, 1, 1, 3, 3].length) (baseStart_3407333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3407333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3407333 prefixEnd_3407333 := by exact prefixLift 3407333
  have htrace : WordTrace (prefixWord ++ tailWord_3407333) baseStart_3407333 baseEnd_3407333 := by
    simpa [prefixWord, tailWord_3407333, baseEnd_3407333] using wordTrace_append hprefix tailTrace_3407333
  have hstable : (prefixWord ++ tailWord_3407333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3407333).length < 2 ^ (prefixWord ++ tailWord_3407333).sum := by decide
  have hdescent : baseEnd_3407333 < baseStart_3407333 := by decide
  rcases family_descends (prefixWord ++ tailWord_3407333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3407356 : List Nat := [2, 2, 2, 1, 2, 1, 2, 4, 1, 4, 2]
def baseStart_3407356 : Nat := 118140960795 + 3407356 * 2 ^ 59
def prefixEnd_3407356 : Nat := 4983230072969 + 3 ^ 40 * 3407356 * 2
def baseEnd_3407356 : Nat := 1749611388981275937679861

theorem tailTrace_3407356 : CollatzResearch.WordTrace tailWord_3407356 prefixEnd_3407356 1749611388981275937679861 := by
  unfold tailWord_3407356
  simp only [CollatzResearch.WordTrace]
  refine ⟨62138241521869308460044961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82850988695825744613393281 62138241521869308460044961)
  ·
    refine ⟨46603681141401981345033721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62138241521869308460044961 46603681141401981345033721)
    ·
      refine ⟨34952760856051486008775291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46603681141401981345033721 34952760856051486008775291)
      ·
        refine ⟨52429141284077229013162937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34952760856051486008775291 52429141284077229013162937)
        ·
          refine ⟨39321855963057921759872203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52429141284077229013162937 39321855963057921759872203)
          ·
            refine ⟨58982783944586882639808305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39321855963057921759872203 58982783944586882639808305)
            ·
              refine ⟨44237087958440161979856229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58982783944586882639808305 44237087958440161979856229)
              ·
                refine ⟨8294453992207530371223043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 44237087958440161979856229 8294453992207530371223043)
                ·
                  refine ⟨12441680988311295556834565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8294453992207530371223043 12441680988311295556834565)
                  ·
                    refine ⟨2332815185308367916906481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12441680988311295556834565 2332815185308367916906481)
                    ·
                      refine ⟨1749611388981275937679861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2332815185308367916906481 1749611388981275937679861)
                      ·
                        rfl

theorem cell23_3407356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 4, 1, 4, 2].length) (baseStart_3407356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3407356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3407356 prefixEnd_3407356 := by exact prefixLift 3407356
  have htrace : WordTrace (prefixWord ++ tailWord_3407356) baseStart_3407356 baseEnd_3407356 := by
    simpa [prefixWord, tailWord_3407356, baseEnd_3407356] using wordTrace_append hprefix tailTrace_3407356
  have hstable : (prefixWord ++ tailWord_3407356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3407356).length < 2 ^ (prefixWord ++ tailWord_3407356).sum := by decide
  have hdescent : baseEnd_3407356 < baseStart_3407356 := by decide
  rcases family_descends (prefixWord ++ tailWord_3407356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3407379 : List Nat := [1, 1, 1, 2, 1, 6, 3, 1, 7]
def baseStart_3407379 : Nat := 118140960795 + 3407379 * 2 ^ 59
def prefixEnd_3407379 : Nat := 4983230072969 + 3 ^ 40 * 3407379 * 2
def baseEnd_3407379 : Nat := 194402577670703260854695

theorem tailTrace_3407379 : CollatzResearch.WordTrace tailWord_3407379 prefixEnd_3407379 194402577670703260854695 := by
  unfold tailWord_3407379
  simp only [CollatzResearch.WordTrace]
  refine ⟨124277321922655291848177191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82851547948436861232118127 124277321922655291848177191)
  ·
    refine ⟨186415982883982937772265787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124277321922655291848177191 186415982883982937772265787)
    ·
      refine ⟨279623974325974406658398681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186415982883982937772265787 279623974325974406658398681)
      ·
        refine ⟨209717980744480804993799011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 279623974325974406658398681 209717980744480804993799011)
        ·
          refine ⟨314576971116721207490698517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 209717980744480804993799011 314576971116721207490698517)
          ·
            refine ⟨14745795521096306601126493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 314576971116721207490698517 14745795521096306601126493)
            ·
              refine ⟨5529673320411114975422435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14745795521096306601126493 5529673320411114975422435)
              ·
                refine ⟨8294509980616672463133653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5529673320411114975422435 8294509980616672463133653)
                ·
                  refine ⟨194402577670703260854695, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8294509980616672463133653 194402577670703260854695)
                  ·
                    rfl

theorem cell23_3407379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 3, 1, 7].length) (baseStart_3407379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3407379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3407379 prefixEnd_3407379 := by exact prefixLift 3407379
  have htrace : WordTrace (prefixWord ++ tailWord_3407379) baseStart_3407379 baseEnd_3407379 := by
    simpa [prefixWord, tailWord_3407379, baseEnd_3407379] using wordTrace_append hprefix tailTrace_3407379
  have hstable : (prefixWord ++ tailWord_3407379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3407379).length < 2 ^ (prefixWord ++ tailWord_3407379).sum := by decide
  have hdescent : baseEnd_3407379 < baseStart_3407379 := by decide
  rcases family_descends (prefixWord ++ tailWord_3407379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3407509 : List Nat := [1, 3, 2, 1, 1, 1, 1, 3, 2, 1, 7]
def baseStart_3407509 : Nat := 118140960795 + 3407509 * 2 ^ 59
def prefixEnd_3407509 : Nat := 4983230072969 + 3 ^ 40 * 3407509 * 2
def baseEnd_3407509 : Nat := 1749689951521413839066657

theorem tailTrace_3407509 : CollatzResearch.WordTrace tailWord_3407509 prefixEnd_3407509 1749689951521413839066657 := by
  unfold tailWord_3407509
  simp only [CollatzResearch.WordTrace]
  refine ⟨124282063412184324050409581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82854708941456216033606387 124282063412184324050409581)
  ·
    refine ⟨46605773779569121518903593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 124282063412184324050409581 46605773779569121518903593)
    ·
      refine ⟨34954330334676841139177695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46605773779569121518903593 34954330334676841139177695)
      ·
        refine ⟨52431495502015261708766543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34954330334676841139177695 52431495502015261708766543)
        ·
          refine ⟨78647243253022892563149815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52431495502015261708766543 78647243253022892563149815)
          ·
            refine ⟨117970864879534338844724723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78647243253022892563149815 117970864879534338844724723)
            ·
              refine ⟨176956297319301508267087085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 117970864879534338844724723 176956297319301508267087085)
              ·
                refine ⟨66358611494738065600157657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 176956297319301508267087085 66358611494738065600157657)
                ·
                  refine ⟨49768958621053549200118243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 66358611494738065600157657 49768958621053549200118243)
                  ·
                    refine ⟨74653437931580323800177365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 49768958621053549200118243 74653437931580323800177365)
                    ·
                      refine ⟨1749689951521413839066657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 74653437931580323800177365 1749689951521413839066657)
                      ·
                        rfl

theorem cell23_3407509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 3, 2, 1, 7].length) (baseStart_3407509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3407509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3407509 prefixEnd_3407509 := by exact prefixLift 3407509
  have htrace : WordTrace (prefixWord ++ tailWord_3407509) baseStart_3407509 baseEnd_3407509 := by
    simpa [prefixWord, tailWord_3407509, baseEnd_3407509] using wordTrace_append hprefix tailTrace_3407509
  have hstable : (prefixWord ++ tailWord_3407509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3407509).length < 2 ^ (prefixWord ++ tailWord_3407509).sum := by decide
  have hdescent : baseEnd_3407509 < baseStart_3407509 := by decide
  rcases family_descends (prefixWord ++ tailWord_3407509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3407523 : List Nat := [1, 1, 1, 4, 1, 1, 4, 3, 2, 3, 2]
def baseStart_3407523 : Nat := 118140960795 + 3407523 * 2 ^ 59
def prefixEnd_3407523 : Nat := 4983230072969 + 3 ^ 40 * 3407523 * 2
def baseEnd_3407523 : Nat := 1749697140250576784291593

theorem tailTrace_3407523 : CollatzResearch.WordTrace tailWord_3407523 prefixEnd_3407523 1749697140250576784291593 := by
  unfold tailWord_3407523
  simp only [CollatzResearch.WordTrace]
  refine ⟨124282574034133604441419223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82855049356089069627612815 124282574034133604441419223)
  ·
    refine ⟨186423861051200406662128835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124282574034133604441419223 186423861051200406662128835)
    ·
      refine ⟨279635791576800609993193253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186423861051200406662128835 279635791576800609993193253)
      ·
        refine ⟨52431710920650114373723735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 279635791576800609993193253 52431710920650114373723735)
        ·
          refine ⟨78647566380975171560585603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52431710920650114373723735 78647566380975171560585603)
          ·
            refine ⟨117971349571462757340878405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78647566380975171560585603 117971349571462757340878405)
            ·
              refine ⟨22119628044649267001414701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 117971349571462757340878405 22119628044649267001414701)
              ·
                refine ⟨8294860516743475125530513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22119628044649267001414701 8294860516743475125530513)
                ·
                  refine ⟨6221145387557606344147885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8294860516743475125530513 6221145387557606344147885)
                  ·
                    refine ⟨2332929520334102379055457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6221145387557606344147885 2332929520334102379055457)
                    ·
                      refine ⟨1749697140250576784291593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2332929520334102379055457 1749697140250576784291593)
                      ·
                        rfl

theorem cell23_3407523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 4, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 4, 3, 2, 3, 2].length) (baseStart_3407523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3407523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3407523 prefixEnd_3407523 := by exact prefixLift 3407523
  have htrace : WordTrace (prefixWord ++ tailWord_3407523) baseStart_3407523 baseEnd_3407523 := by
    simpa [prefixWord, tailWord_3407523, baseEnd_3407523] using wordTrace_append hprefix tailTrace_3407523
  have hstable : (prefixWord ++ tailWord_3407523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3407523).length < 2 ^ (prefixWord ++ tailWord_3407523).sum := by decide
  have hdescent : baseEnd_3407523 < baseStart_3407523 := by decide
  rcases family_descends (prefixWord ++ tailWord_3407523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3407533 : List Nat := [1, 5, 2, 1, 1, 1, 1, 5, 1, 5]
def baseStart_3407533 : Nat := 118140960795 + 3407533 * 2 ^ 59
def prefixEnd_3407533 : Nat := 4983230072969 + 3 ^ 40 * 3407533 * 2
def baseEnd_3407533 : Nat := 583234091685707248388849

theorem tailTrace_3407533 : CollatzResearch.WordTrace tailWord_3407533 prefixEnd_3407533 583234091685707248388849 := by
  unfold tailWord_3407533
  simp only [CollatzResearch.WordTrace]
  refine ⟨124282938764097376149283253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82855292509398250766188835 124282938764097376149283253)
  ·
    refine ⟨11651525509134129013995305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 124282938764097376149283253 11651525509134129013995305)
    ·
      refine ⟨8738644131850596760496479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11651525509134129013995305 8738644131850596760496479)
      ·
        refine ⟨13107966197775895140744719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8738644131850596760496479 13107966197775895140744719)
        ·
          refine ⟨19661949296663842711117079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13107966197775895140744719 19661949296663842711117079)
          ·
            refine ⟨29492923944995764066675619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19661949296663842711117079 29492923944995764066675619)
            ·
              refine ⟨44239385917493646100013429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29492923944995764066675619 44239385917493646100013429)
              ·
                refine ⟨4147442429765029321876259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 44239385917493646100013429 4147442429765029321876259)
                ·
                  refine ⟨6221163644647543982814389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4147442429765029321876259 6221163644647543982814389)
                  ·
                    refine ⟨583234091685707248388849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6221163644647543982814389 583234091685707248388849)
                    ·
                      rfl

theorem cell23_3407533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 5, 1, 5].length) (baseStart_3407533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3407533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3407533 prefixEnd_3407533 := by exact prefixLift 3407533
  have htrace : WordTrace (prefixWord ++ tailWord_3407533) baseStart_3407533 baseEnd_3407533 := by
    simpa [prefixWord, tailWord_3407533, baseEnd_3407533] using wordTrace_append hprefix tailTrace_3407533
  have hstable : (prefixWord ++ tailWord_3407533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3407533).length < 2 ^ (prefixWord ++ tailWord_3407533).sum := by decide
  have hdescent : baseEnd_3407533 < baseStart_3407533 := by decide
  rcases family_descends (prefixWord ++ tailWord_3407533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3407566 : List Nat := [4, 1, 1, 1, 3, 1, 1, 3, 1, 1, 6]
def baseStart_3407566 : Nat := 118140960795 + 3407566 * 2 ^ 59
def prefixEnd_3407566 : Nat := 4983230072969 + 3 ^ 40 * 3407566 * 2
def baseEnd_3407566 : Nat := 1749719219918720116053895

theorem tailTrace_3407566 : CollatzResearch.WordTrace tailWord_3407566 prefixEnd_3407566 1749719219918720116053895 := by
  unfold tailWord_3407566
  simp only [CollatzResearch.WordTrace]
  refine ⟨15535517796622227848154319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 82856094915318548523489701 15535517796622227848154319)
  ·
    refine ⟨23303276694933341772231479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15535517796622227848154319 23303276694933341772231479)
    ·
      refine ⟨34954915042400012658347219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23303276694933341772231479 34954915042400012658347219)
      ·
        refine ⟨52432372563600018987520829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34954915042400012658347219 52432372563600018987520829)
        ·
          refine ⟨19662139711350007120320311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52432372563600018987520829 19662139711350007120320311)
          ·
            refine ⟨29493209567025010680480467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19662139711350007120320311 29493209567025010680480467)
            ·
              refine ⟨44239814350537516020720701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29493209567025010680480467 44239814350537516020720701)
              ·
                refine ⟨16589930381451568507770263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44239814350537516020720701 16589930381451568507770263)
                ·
                  refine ⟨24884895572177352761655395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16589930381451568507770263 24884895572177352761655395)
                  ·
                    refine ⟨37327343358266029142483093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24884895572177352761655395 37327343358266029142483093)
                    ·
                      refine ⟨1749719219918720116053895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 37327343358266029142483093 1749719219918720116053895)
                      ·
                        rfl

theorem cell23_3407566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 3, 1, 1, 6].length) (baseStart_3407566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3407566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3407566 prefixEnd_3407566 := by exact prefixLift 3407566
  have htrace : WordTrace (prefixWord ++ tailWord_3407566) baseStart_3407566 baseEnd_3407566 := by
    simpa [prefixWord, tailWord_3407566, baseEnd_3407566] using wordTrace_append hprefix tailTrace_3407566
  have hstable : (prefixWord ++ tailWord_3407566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3407566).length < 2 ^ (prefixWord ++ tailWord_3407566).sum := by decide
  have hdescent : baseEnd_3407566 < baseStart_3407566 := by decide
  rcases family_descends (prefixWord ++ tailWord_3407566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3407570 : List Nat := [3, 2, 2, 2, 2, 1, 3, 2, 1, 1, 4]
def baseStart_3407570 : Nat := 118140960795 + 3407570 * 2 ^ 59
def prefixEnd_3407570 : Nat := 4983230072969 + 3 ^ 40 * 3407570 * 2
def baseEnd_3407570 : Nat := 1749721273841338100403877

theorem tailTrace_3407570 : CollatzResearch.WordTrace tailWord_3407570 prefixEnd_3407570 1749721273841338100403877 := by
  unfold tailWord_3407570
  simp only [CollatzResearch.WordTrace]
  refine ⟨31071072066240832867095041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82856192176642220978920109 31071072066240832867095041)
  ·
    refine ⟨23303304049680624650321281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31071072066240832867095041 23303304049680624650321281)
    ·
      refine ⟨17477478037260468487740961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23303304049680624650321281 17477478037260468487740961)
      ·
        refine ⟨13108108527945351365805721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17477478037260468487740961 13108108527945351365805721)
        ·
          refine ⟨9831081395959013524354291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13108108527945351365805721 9831081395959013524354291)
          ·
            refine ⟨14746622093938520286531437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9831081395959013524354291 14746622093938520286531437)
            ·
              refine ⟨5529983285226945107449289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14746622093938520286531437 5529983285226945107449289)
              ·
                refine ⟨4147487463920208830586967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5529983285226945107449289 4147487463920208830586967)
                ·
                  refine ⟨6221231195880313245880451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4147487463920208830586967 6221231195880313245880451)
                  ·
                    refine ⟨9331846793820469868820677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6221231195880313245880451 9331846793820469868820677)
                    ·
                      refine ⟨1749721273841338100403877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9331846793820469868820677 1749721273841338100403877)
                      ·
                        rfl

theorem cell23_3407570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 3, 2, 1, 1, 4].length) (baseStart_3407570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3407570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3407570 prefixEnd_3407570 := by exact prefixLift 3407570
  have htrace : WordTrace (prefixWord ++ tailWord_3407570) baseStart_3407570 baseEnd_3407570 := by
    simpa [prefixWord, tailWord_3407570, baseEnd_3407570] using wordTrace_append hprefix tailTrace_3407570
  have hstable : (prefixWord ++ tailWord_3407570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3407570).length < 2 ^ (prefixWord ++ tailWord_3407570).sum := by decide
  have hdescent : baseEnd_3407570 < baseStart_3407570 := by decide
  rcases family_descends (prefixWord ++ tailWord_3407570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3407580 : List Nat := [2, 2, 5, 1, 2, 1, 1, 2, 1, 6]
def baseStart_3407580 : Nat := 118140960795 + 3407580 * 2 ^ 59
def prefixEnd_3407580 : Nat := 4983230072969 + 3 ^ 40 * 3407580 * 2
def baseEnd_3407580 : Nat := 583242136215961020426277

theorem tailTrace_3407580 : CollatzResearch.WordTrace tailWord_3407580 prefixEnd_3407580 583242136215961020426277 := by
  unfold tailWord_3407580
  simp only [CollatzResearch.WordTrace]
  refine ⟨62142326497463551588122097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82856435329951402117496129 62142326497463551588122097)
  ·
    refine ⟨46606744873097663691091573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62142326497463551588122097 46606744873097663691091573)
    ·
      refine ⟨4369382331852905971039835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 46606744873097663691091573 4369382331852905971039835)
      ·
        refine ⟨6554073497779358956559753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4369382331852905971039835 6554073497779358956559753)
        ·
          refine ⟨4915555123334519217419815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6554073497779358956559753 4915555123334519217419815)
          ·
            refine ⟨7373332685001778826129723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4915555123334519217419815 7373332685001778826129723)
            ·
              refine ⟨11059999027502668239194585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7373332685001778826129723 11059999027502668239194585)
              ·
                refine ⟨8294999270627001179395939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11059999027502668239194585 8294999270627001179395939)
                ·
                  refine ⟨12442498905940501769093909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8294999270627001179395939 12442498905940501769093909)
                  ·
                    refine ⟨583242136215961020426277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12442498905940501769093909 583242136215961020426277)
                    ·
                      rfl

theorem cell23_3407580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 1, 2, 1, 6].length) (baseStart_3407580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3407580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3407580 prefixEnd_3407580 := by exact prefixLift 3407580
  have htrace : WordTrace (prefixWord ++ tailWord_3407580) baseStart_3407580 baseEnd_3407580 := by
    simpa [prefixWord, tailWord_3407580, baseEnd_3407580] using wordTrace_append hprefix tailTrace_3407580
  have hstable : (prefixWord ++ tailWord_3407580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3407580).length < 2 ^ (prefixWord ++ tailWord_3407580).sum := by decide
  have hdescent : baseEnd_3407580 < baseStart_3407580 := by decide
  rcases family_descends (prefixWord ++ tailWord_3407580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3407587 : List Nat := [1, 1, 1, 7, 2, 1, 3, 1, 1, 1, 4]
def baseStart_3407587 : Nat := 118140960795 + 3407587 * 2 ^ 59
def prefixEnd_3407587 : Nat := 4983230072969 + 3 ^ 40 * 3407587 * 2
def baseEnd_3407587 : Nat := 1749730003012464533891299

theorem tailTrace_3407587 : CollatzResearch.WordTrace tailWord_3407587 prefixEnd_3407587 1749730003012464533891299 := by
  unfold tailWord_3407587
  simp only [CollatzResearch.WordTrace]
  refine ⟨124284908305901743371749015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82856605537267828914499343 124284908305901743371749015)
  ·
    refine ⟨186427362458852615057623523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124284908305901743371749015 186427362458852615057623523)
    ·
      refine ⟨279641043688278922586435285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186427362458852615057623523 279641043688278922586435285)
      ·
        refine ⟨6554086961444037248119577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 279641043688278922586435285 6554086961444037248119577)
        ·
          refine ⟨4915565221083027936089683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6554086961444037248119577 4915565221083027936089683)
          ·
            refine ⟨7373347831624541904134525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4915565221083027936089683 7373347831624541904134525)
            ·
              refine ⟨2765005436859203214050447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7373347831624541904134525 2765005436859203214050447)
              ·
                refine ⟨4147508155288804821075671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2765005436859203214050447 4147508155288804821075671)
                ·
                  refine ⟨6221262232933207231613507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4147508155288804821075671 6221262232933207231613507)
                  ·
                    refine ⟨9331893349399810847420261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6221262232933207231613507 9331893349399810847420261)
                    ·
                      refine ⟨1749730003012464533891299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9331893349399810847420261 1749730003012464533891299)
                      ·
                        rfl

theorem cell23_3407587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 3, 1, 1, 1, 4].length) (baseStart_3407587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3407587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3407587 prefixEnd_3407587 := by exact prefixLift 3407587
  have htrace : WordTrace (prefixWord ++ tailWord_3407587) baseStart_3407587 baseEnd_3407587 := by
    simpa [prefixWord, tailWord_3407587, baseEnd_3407587] using wordTrace_append hprefix tailTrace_3407587
  have hstable : (prefixWord ++ tailWord_3407587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3407587).length < 2 ^ (prefixWord ++ tailWord_3407587).sum := by decide
  have hdescent : baseEnd_3407587 < baseStart_3407587 := by decide
  rcases family_descends (prefixWord ++ tailWord_3407587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3407603 : List Nat := [1, 1, 1, 2, 2, 3, 2, 3, 4, 1, 3]
def baseStart_3407603 : Nat := 118140960795 + 3407603 * 2 ^ 59
def prefixEnd_3407603 : Nat := 4983230072969 + 3 ^ 40 * 3407603 * 2
def baseEnd_3407603 : Nat := 1749738218702936471291225

theorem tailTrace_3407603 : CollatzResearch.WordTrace tailWord_3407603 prefixEnd_3407603 1749738218702936471291225 := by
  unfold tailWord_3407603
  simp only [CollatzResearch.WordTrace]
  refine ⟨124285491873843778104331463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82856994582562518736220975 124285491873843778104331463)
  ·
    refine ⟨186428237810765667156497195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124285491873843778104331463 186428237810765667156497195)
    ·
      refine ⟨279642356716148500734745793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186428237810765667156497195 279642356716148500734745793)
      ·
        refine ⟨209731767537111375551059345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 279642356716148500734745793 209731767537111375551059345)
        ·
          refine ⟨157298825652833531663294509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 209731767537111375551059345 157298825652833531663294509)
          ·
            refine ⟨58987059619812574373735441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 157298825652833531663294509 58987059619812574373735441)
            ·
              refine ⟨44240294714859430780301581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58987059619812574373735441 44240294714859430780301581)
              ·
                refine ⟨16590110518072286542613093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44240294714859430780301581 16590110518072286542613093)
                ·
                  refine ⟨3110645722138553726739955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16590110518072286542613093 3110645722138553726739955)
                  ·
                    refine ⟨4665968583207830590109933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3110645722138553726739955 4665968583207830590109933)
                    ·
                      refine ⟨1749738218702936471291225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4665968583207830590109933 1749738218702936471291225)
                      ·
                        rfl

theorem cell23_3407603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 3, 4, 1, 3].length) (baseStart_3407603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3407603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3407603 prefixEnd_3407603 := by exact prefixLift 3407603
  have htrace : WordTrace (prefixWord ++ tailWord_3407603) baseStart_3407603 baseEnd_3407603 := by
    simpa [prefixWord, tailWord_3407603, baseEnd_3407603] using wordTrace_append hprefix tailTrace_3407603
  have hstable : (prefixWord ++ tailWord_3407603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3407603).length < 2 ^ (prefixWord ++ tailWord_3407603).sum := by decide
  have hdescent : baseEnd_3407603 < baseStart_3407603 := by decide
  rcases family_descends (prefixWord ++ tailWord_3407603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3407620 : List Nat := [2, 3, 2, 2, 1, 3, 2, 1, 1, 3, 3]
def baseStart_3407620 : Nat := 118140960795 + 3407620 * 2 ^ 59
def prefixEnd_3407620 : Nat := 4983230072969 + 3 ^ 40 * 3407620 * 2
def baseEnd_3407620 : Nat := 1749746947874062904778647

theorem tailTrace_3407620 : CollatzResearch.WordTrace tailWord_3407620 prefixEnd_3407620 1749746947874062904778647 := by
  unfold tailWord_3407620
  simp only [CollatzResearch.WordTrace]
  refine ⟨62143055957391095003850157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82857407943188126671800209 62143055957391095003850157)
  ·
    refine ⟨23303645984021660626443809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62143055957391095003850157 23303645984021660626443809)
    ·
      refine ⟨17477734488016245469832857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23303645984021660626443809 17477734488016245469832857)
      ·
        refine ⟨13108300866012184102374643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17477734488016245469832857 13108300866012184102374643)
        ·
          refine ⟨19662451299018276153561965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13108300866012184102374643 19662451299018276153561965)
          ·
            refine ⟨7373419237131853557585737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19662451299018276153561965 7373419237131853557585737)
            ·
              refine ⟨5530064427848890168189303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7373419237131853557585737 5530064427848890168189303)
              ·
                refine ⟨8295096641773335252283955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5530064427848890168189303 8295096641773335252283955)
                ·
                  refine ⟨12442644962660002878425933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8295096641773335252283955 12442644962660002878425933)
                  ·
                    refine ⟨4665991860997501079409725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12442644962660002878425933 4665991860997501079409725)
                    ·
                      refine ⟨1749746947874062904778647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4665991860997501079409725 1749746947874062904778647)
                      ·
                        rfl

theorem cell23_3407620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 2, 1, 1, 3, 3].length) (baseStart_3407620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3407620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3407620 prefixEnd_3407620 := by exact prefixLift 3407620
  have htrace : WordTrace (prefixWord ++ tailWord_3407620) baseStart_3407620 baseEnd_3407620 := by
    simpa [prefixWord, tailWord_3407620, baseEnd_3407620] using wordTrace_append hprefix tailTrace_3407620
  have hstable : (prefixWord ++ tailWord_3407620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3407620).length < 2 ^ (prefixWord ++ tailWord_3407620).sum := by decide
  have hdescent : baseEnd_3407620 < baseStart_3407620 := by decide
  rcases family_descends (prefixWord ++ tailWord_3407620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3407630 : List Nat := [4, 1, 1, 2, 1, 1, 4, 1, 3, 3, 2]
def baseStart_3407630 : Nat := 118140960795 + 3407630 * 2 ^ 59
def prefixEnd_3407630 : Nat := 4983230072969 + 3 ^ 40 * 3407630 * 2
def baseEnd_3407630 : Nat := 1749752082680607865653601

theorem tailTrace_3407630 : CollatzResearch.WordTrace tailWord_3407630 prefixEnd_3407630 1749752082680607865653601 := by
  unfold tailWord_3407630
  simp only [CollatzResearch.WordTrace]
  refine ⟨15535809580593245214445543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 82857651096497307810376229 15535809580593245214445543)
  ·
    refine ⟨23303714370889867821668315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15535809580593245214445543 23303714370889867821668315)
    ·
      refine ⟨34955571556334801732502473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23303714370889867821668315 34955571556334801732502473)
      ·
        refine ⟨26216678667251101299376855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34955571556334801732502473 26216678667251101299376855)
        ·
          refine ⟨39325018000876651949065283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26216678667251101299376855 39325018000876651949065283)
          ·
            refine ⟨58987527001314977923597925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39325018000876651949065283 58987527001314977923597925)
            ·
              refine ⟨11060161312746558360674611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 58987527001314977923597925 11060161312746558360674611)
              ·
                refine ⟨16590241969119837541011917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11060161312746558360674611 16590241969119837541011917)
                ·
                  refine ⟨6221340738419939077879469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16590241969119837541011917 6221340738419939077879469)
                  ·
                    refine ⟨2333002776907477154204801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6221340738419939077879469 2333002776907477154204801)
                    ·
                      refine ⟨1749752082680607865653601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2333002776907477154204801 1749752082680607865653601)
                      ·
                        rfl

theorem cell23_3407630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 4, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 4, 1, 3, 3, 2].length) (baseStart_3407630 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3407630 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3407630 prefixEnd_3407630 := by exact prefixLift 3407630
  have htrace : WordTrace (prefixWord ++ tailWord_3407630) baseStart_3407630 baseEnd_3407630 := by
    simpa [prefixWord, tailWord_3407630, baseEnd_3407630] using wordTrace_append hprefix tailTrace_3407630
  have hstable : (prefixWord ++ tailWord_3407630).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3407630).length < 2 ^ (prefixWord ++ tailWord_3407630).sum := by decide
  have hdescent : baseEnd_3407630 < baseStart_3407630 := by decide
  rcases family_descends (prefixWord ++ tailWord_3407630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3407670 : List Nat := [5, 1, 2, 2, 1, 1, 2, 1, 2, 6]
def baseStart_3407670 : Nat := 118140960795 + 3407670 * 2 ^ 59
def prefixEnd_3407670 : Nat := 4983230072969 + 3 ^ 40 * 3407670 * 2
def baseEnd_3407670 : Nat := 583257540635595903051139

theorem tailTrace_3407670 : CollatzResearch.WordTrace tailWord_3407670 prefixEnd_3407670 583257540635595903051139 := by
  unfold tailWord_3407670
  simp only [CollatzResearch.WordTrace]
  refine ⟨7767995972787565534188779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 82858623709734032364680309 7767995972787565534188779)
  ·
    refine ⟨11651993959181348301283169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7767995972787565534188779 11651993959181348301283169)
    ·
      refine ⟨8738995469386011225962377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11651993959181348301283169 8738995469386011225962377)
      ·
        refine ⟨6554246602039508419471783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8738995469386011225962377 6554246602039508419471783)
        ·
          refine ⟨9831369903059262629207675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6554246602039508419471783 9831369903059262629207675)
          ·
            refine ⟨14747054854588893943811513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9831369903059262629207675 14747054854588893943811513)
            ·
              refine ⟨11060291140941670457858635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14747054854588893943811513 11060291140941670457858635)
              ·
                refine ⟨16590436711412505686787953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11060291140941670457858635 16590436711412505686787953)
                ·
                  refine ⟨12442827533559379265090965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16590436711412505686787953 12442827533559379265090965)
                  ·
                    refine ⟨583257540635595903051139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12442827533559379265090965 583257540635595903051139)
                    ·
                      rfl

theorem cell23_3407670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 2, 1, 2, 6].length) (baseStart_3407670 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3407670 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3407670 prefixEnd_3407670 := by exact prefixLift 3407670
  have htrace : WordTrace (prefixWord ++ tailWord_3407670) baseStart_3407670 baseEnd_3407670 := by
    simpa [prefixWord, tailWord_3407670, baseEnd_3407670] using wordTrace_append hprefix tailTrace_3407670
  have hstable : (prefixWord ++ tailWord_3407670).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3407670).length < 2 ^ (prefixWord ++ tailWord_3407670).sum := by decide
  have hdescent : baseEnd_3407670 < baseStart_3407670 := by decide
  rcases family_descends (prefixWord ++ tailWord_3407670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3407677 : List Nat := [1, 4, 1, 4, 1, 1, 3, 1, 1, 4, 2]
def baseStart_3407677 : Nat := 118140960795 + 3407677 * 2 ^ 59
def prefixEnd_3407677 : Nat := 4983230072969 + 3 ^ 40 * 3407677 * 2
def baseEnd_3407677 : Nat := 1749776216271369181765885

theorem tailTrace_3407677 : CollatzResearch.WordTrace tailWord_3407677 prefixEnd_3407677 1749776216271369181765885 := by
  unfold tailWord_3407677
  simp only [CollatzResearch.WordTrace]
  refine ⟨124288190875575688742525285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82858793917050459161683523 124288190875575688742525285)
  ·
    refine ⟨23304035789170441639223491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 124288190875575688742525285 23304035789170441639223491)
    ·
      refine ⟨34956053683755662458835237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23304035789170441639223491 34956053683755662458835237)
      ·
        refine ⟨6554260065704186711031607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34956053683755662458835237 6554260065704186711031607)
        ·
          refine ⟨9831390098556280066547411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6554260065704186711031607 9831390098556280066547411)
          ·
            refine ⟨14747085147834420099821117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9831390098556280066547411 14747085147834420099821117)
            ·
              refine ⟨5530156930437907537432919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14747085147834420099821117 5530156930437907537432919)
              ·
                refine ⟨8295235395656861306149379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5530156930437907537432919 8295235395656861306149379)
                ·
                  refine ⟨12442853093485291959224069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8295235395656861306149379 12442853093485291959224069)
                  ·
                    refine ⟨2333034955028492242354513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12442853093485291959224069 2333034955028492242354513)
                    ·
                      refine ⟨1749776216271369181765885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2333034955028492242354513 1749776216271369181765885)
                      ·
                        rfl

theorem cell23_3407677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 3, 1, 1, 4, 2].length) (baseStart_3407677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3407677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3407677 prefixEnd_3407677 := by exact prefixLift 3407677
  have htrace : WordTrace (prefixWord ++ tailWord_3407677) baseStart_3407677 baseEnd_3407677 := by
    simpa [prefixWord, tailWord_3407677, baseEnd_3407677] using wordTrace_append hprefix tailTrace_3407677
  have hstable : (prefixWord ++ tailWord_3407677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3407677).length < 2 ^ (prefixWord ++ tailWord_3407677).sum := by decide
  have hdescent : baseEnd_3407677 < baseStart_3407677 := by decide
  rcases family_descends (prefixWord ++ tailWord_3407677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3407713 : List Nat := [1, 2, 3, 1, 1, 1, 5, 2, 2, 5]
def baseStart_3407713 : Nat := 118140960795 + 3407713 * 2 ^ 59
def prefixEnd_3407713 : Nat := 4983230072969 + 3 ^ 40 * 3407713 * 2
def baseEnd_3407713 : Nat := 583264900524977013638573

theorem tailTrace_3407713 : CollatzResearch.WordTrace tailWord_3407713 prefixEnd_3407713 583264900524977013638573 := by
  unfold tailWord_3407713
  simp only [CollatzResearch.WordTrace]
  refine ⟨124289503903445266890835793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82859669268963511260557195 124289503903445266890835793)
  ·
    refine ⟨93217127927583950168126845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124289503903445266890835793 93217127927583950168126845)
    ·
      refine ⟨34956422972843981313047567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93217127927583950168126845 34956422972843981313047567)
      ·
        refine ⟨52434634459265971969571351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34956422972843981313047567 52434634459265971969571351)
        ·
          refine ⟨78651951688898957954357027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52434634459265971969571351 78651951688898957954357027)
          ·
            refine ⟨117977927533348436931535541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78651951688898957954357027 117977927533348436931535541)
            ·
              refine ⟨11060430706251415962331457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 117977927533348436931535541 11060430706251415962331457)
              ·
                refine ⟨8295323029688561971748593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11060430706251415962331457 8295323029688561971748593)
                ·
                  refine ⟨6221492272266421478811445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8295323029688561971748593 6221492272266421478811445)
                  ·
                    refine ⟨583264900524977013638573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6221492272266421478811445 583264900524977013638573)
                    ·
                      rfl

theorem cell23_3407713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 5, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 5, 2, 2, 5].length) (baseStart_3407713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3407713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3407713 prefixEnd_3407713 := by exact prefixLift 3407713
  have htrace : WordTrace (prefixWord ++ tailWord_3407713) baseStart_3407713 baseEnd_3407713 := by
    simpa [prefixWord, tailWord_3407713, baseEnd_3407713] using wordTrace_append hprefix tailTrace_3407713
  have hstable : (prefixWord ++ tailWord_3407713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3407713).length < 2 ^ (prefixWord ++ tailWord_3407713).sum := by decide
  have hdescent : baseEnd_3407713 < baseStart_3407713 := by decide
  rcases family_descends (prefixWord ++ tailWord_3407713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3407720 : List Nat := [2, 1, 4, 2, 1, 1, 2, 1, 2, 5, 2]
def baseStart_3407720 : Nat := 118140960795 + 3407720 * 2 ^ 59
def prefixEnd_3407720 : Nat := 4983230072969 + 3 ^ 40 * 3407720 * 2
def baseEnd_3407720 : Nat := 1749798295939512513528187

theorem tailTrace_3407720 : CollatzResearch.WordTrace tailWord_3407720 prefixEnd_3407720 1749798295939512513528187 := by
  unfold tailWord_3407720
  simp only [CollatzResearch.WordTrace]
  refine ⟨62144879607209953543170307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82859839476279938057560409 62144879607209953543170307)
  ·
    refine ⟨93217319410814930314755461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62144879607209953543170307 93217319410814930314755461)
    ·
      refine ⟨17478247389527799434016649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 93217319410814930314755461 17478247389527799434016649)
      ·
        refine ⟨13108685542145849575512487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17478247389527799434016649 13108685542145849575512487)
        ·
          refine ⟨19663028313218774363268731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13108685542145849575512487 19663028313218774363268731)
          ·
            refine ⟨29494542469828161544903097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19663028313218774363268731 29494542469828161544903097)
            ·
              refine ⟨22120906852371121158677323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29494542469828161544903097 22120906852371121158677323)
              ·
                refine ⟨33181360278556681738015985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22120906852371121158677323 33181360278556681738015985)
                ·
                  refine ⟨24886020208917511303511989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33181360278556681738015985 24886020208917511303511989)
                  ·
                    refine ⟨2333064394586016684704249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 24886020208917511303511989 2333064394586016684704249)
                    ·
                      refine ⟨1749798295939512513528187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2333064394586016684704249 1749798295939512513528187)
                      ·
                        rfl

theorem cell23_3407720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 2, 1, 2, 5, 2].length) (baseStart_3407720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3407720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3407720 prefixEnd_3407720 := by exact prefixLift 3407720
  have htrace : WordTrace (prefixWord ++ tailWord_3407720) baseStart_3407720 baseEnd_3407720 := by
    simpa [prefixWord, tailWord_3407720, baseEnd_3407720] using wordTrace_append hprefix tailTrace_3407720
  have hstable : (prefixWord ++ tailWord_3407720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3407720).length < 2 ^ (prefixWord ++ tailWord_3407720).sum := by decide
  have hdescent : baseEnd_3407720 < baseStart_3407720 := by decide
  rcases family_descends (prefixWord ++ tailWord_3407720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3407736 : List Nat := [2, 1, 2, 1, 1, 1, 1, 2, 1, 2, 9]
def baseStart_3407736 : Nat := 118140960795 + 3407736 * 2 ^ 59
def prefixEnd_3407736 : Nat := 4983230072969 + 3 ^ 40 * 3407736 * 2
def baseEnd_3407736 : Nat := 1749806511629984450928113

theorem tailTrace_3407736 : CollatzResearch.WordTrace tailWord_3407736 prefixEnd_3407736 1749806511629984450928113 := by
  unfold tailWord_3407736
  simp only [CollatzResearch.WordTrace]
  refine ⟨62145171391180970909461531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82860228521574627879282041 62145171391180970909461531)
  ·
    refine ⟨93217757086771456364192297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62145171391180970909461531 93217757086771456364192297)
    ·
      refine ⟨69913317815078592273144223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93217757086771456364192297 69913317815078592273144223)
      ·
        refine ⟨104869976722617888409716335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69913317815078592273144223 104869976722617888409716335)
        ·
          refine ⟨157304965083926832614574503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104869976722617888409716335 157304965083926832614574503)
          ·
            refine ⟨235957447625890248921861755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 157304965083926832614574503 235957447625890248921861755)
            ·
              refine ⟨353936171438835373382792633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 235957447625890248921861755 353936171438835373382792633)
              ·
                refine ⟨265452128579126530037094475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 353936171438835373382792633 265452128579126530037094475)
                ·
                  refine ⟨398178192868689795055641713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 265452128579126530037094475 398178192868689795055641713)
                  ·
                    refine ⟨298633644651517346291731285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 398178192868689795055641713 298633644651517346291731285)
                    ·
                      refine ⟨1749806511629984450928113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 298633644651517346291731285 1749806511629984450928113)
                      ·
                        rfl

theorem cell23_3407736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 2, 1, 2, 9].length) (baseStart_3407736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3407736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3407736 prefixEnd_3407736 := by exact prefixLift 3407736
  have htrace : WordTrace (prefixWord ++ tailWord_3407736) baseStart_3407736 baseEnd_3407736 := by
    simpa [prefixWord, tailWord_3407736, baseEnd_3407736] using wordTrace_append hprefix tailTrace_3407736
  have hstable : (prefixWord ++ tailWord_3407736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3407736).length < 2 ^ (prefixWord ++ tailWord_3407736).sum := by decide
  have hdescent : baseEnd_3407736 < baseStart_3407736 := by decide
  rcases family_descends (prefixWord ++ tailWord_3407736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3407743 : List Nat := [1, 1, 2, 2, 1, 1, 3, 3, 5, 4]
def baseStart_3407743 : Nat := 118140960795 + 3407743 * 2 ^ 59
def prefixEnd_3407743 : Nat := 4983230072969 + 3 ^ 40 * 3407743 * 2
def baseEnd_3407743 : Nat := 583270035331521974513527

theorem tailTrace_3407743 : CollatzResearch.WordTrace tailWord_3407743 prefixEnd_3407743 583270035331521974513527 := by
  unfold tailWord_3407743
  simp only [CollatzResearch.WordTrace]
  refine ⟨124290598093336582014427883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82860398728891054676285255 124290598093336582014427883)
  ·
    refine ⟨186435897140004873021641825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124290598093336582014427883 186435897140004873021641825)
    ·
      refine ⟨139826922855003654766231369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 186435897140004873021641825 139826922855003654766231369)
      ·
        refine ⟨104870192141252741074673527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 139826922855003654766231369 104870192141252741074673527)
        ·
          refine ⟨157305288211879111612010291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104870192141252741074673527 157305288211879111612010291)
          ·
            refine ⟨235957932317818667418015437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 157305288211879111612010291 235957932317818667418015437)
            ·
              refine ⟨88484224619182000281755789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 235957932317818667418015437 88484224619182000281755789)
              ·
                refine ⟨33181584232193250105658421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 88484224619182000281755789 33181584232193250105658421)
                ·
                  refine ⟨3110773521768117197405477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 33181584232193250105658421 3110773521768117197405477)
                  ·
                    refine ⟨583270035331521974513527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3110773521768117197405477 583270035331521974513527)
                    ·
                      rfl

theorem cell23_3407743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 3, 5, 4].length) (baseStart_3407743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3407743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3407743 prefixEnd_3407743 := by exact prefixLift 3407743
  have htrace : WordTrace (prefixWord ++ tailWord_3407743) baseStart_3407743 baseEnd_3407743 := by
    simpa [prefixWord, tailWord_3407743, baseEnd_3407743] using wordTrace_append hprefix tailTrace_3407743
  have hstable : (prefixWord ++ tailWord_3407743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3407743).length < 2 ^ (prefixWord ++ tailWord_3407743).sum := by decide
  have hdescent : baseEnd_3407743 < baseStart_3407743 := by decide
  rcases family_descends (prefixWord ++ tailWord_3407743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3407834 : List Nat := [3, 1, 1, 2, 5, 1, 2, 1, 3, 1, 3]
def baseStart_3407834 : Nat := 118140960795 + 3407834 * 2 ^ 59
def prefixEnd_3407834 : Nat := 4983230072969 + 3 ^ 40 * 3407834 * 2
def baseEnd_3407834 : Nat := 1749856832734125067502663

theorem tailTrace_3407834 : CollatzResearch.WordTrace tailWord_3407834 prefixEnd_3407834 1749856832734125067502663 := by
  unfold tailWord_3407834
  simp only [CollatzResearch.WordTrace]
  refine ⟨31073479284001726138997639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82862611424004603037327037 31073479284001726138997639)
  ·
    refine ⟨46610218926002589208496459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31073479284001726138997639 46610218926002589208496459)
    ·
      refine ⟨69915328389003883812744689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46610218926002589208496459 69915328389003883812744689)
      ·
        refine ⟨52436496291752912859558517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69915328389003883812744689 52436496291752912859558517)
        ·
          refine ⟨4915921527351835580583611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 52436496291752912859558517 4915921527351835580583611)
          ·
            refine ⟨7373882291027753370875417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4915921527351835580583611 7373882291027753370875417)
            ·
              refine ⟨5530411718270815028156563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7373882291027753370875417 5530411718270815028156563)
              ·
                refine ⟨8295617577406222542234845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5530411718270815028156563 8295617577406222542234845)
                ·
                  refine ⟨3110856591527333453338067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8295617577406222542234845 3110856591527333453338067)
                  ·
                    refine ⟨4666284887291000180007101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3110856591527333453338067 4666284887291000180007101)
                    ·
                      refine ⟨1749856832734125067502663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4666284887291000180007101 1749856832734125067502663)
                      ·
                        rfl

theorem cell23_3407834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 2, 1, 3, 1, 3].length) (baseStart_3407834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3407834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3407834 prefixEnd_3407834 := by exact prefixLift 3407834
  have htrace : WordTrace (prefixWord ++ tailWord_3407834) baseStart_3407834 baseEnd_3407834 := by
    simpa [prefixWord, tailWord_3407834, baseEnd_3407834] using wordTrace_append hprefix tailTrace_3407834
  have hstable : (prefixWord ++ tailWord_3407834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3407834).length < 2 ^ (prefixWord ++ tailWord_3407834).sum := by decide
  have hdescent : baseEnd_3407834 < baseStart_3407834 := by decide
  rcases family_descends (prefixWord ++ tailWord_3407834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3407877 : List Nat := [1, 3, 1, 1, 2, 4, 2, 3, 1, 2, 3]
def baseStart_3407877 : Nat := 118140960795 + 3407877 * 2 ^ 59
def prefixEnd_3407877 : Nat := 4983230072969 + 3 ^ 40 * 3407877 * 2
def baseEnd_3407877 : Nat := 1749878912402268399264965

theorem tailTrace_3407877 : CollatzResearch.WordTrace tailWord_3407877 prefixEnd_3407877 1749878912402268399264965 := by
  unfold tailWord_3407877
  simp only [CollatzResearch.WordTrace]
  refine ⟨124295485474851122899805885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82863656983234081933203923 124295485474851122899805885)
  ·
    refine ⟨46610807053069171087427207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 124295485474851122899805885 46610807053069171087427207)
    ·
      refine ⟨69916210579603756631140811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46610807053069171087427207 69916210579603756631140811)
      ·
        refine ⟨104874315869405634946711217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69916210579603756631140811 104874315869405634946711217)
        ·
          refine ⟨78655736902054226210033413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104874315869405634946711217 78655736902054226210033413)
          ·
            refine ⟨14747950669135167414381265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 78655736902054226210033413 14747950669135167414381265)
            ·
              refine ⟨11060963001851375560785949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14747950669135167414381265 11060963001851375560785949)
              ·
                refine ⟨4147861125694265835294731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11060963001851375560785949 4147861125694265835294731)
                ·
                  refine ⟨6221791688541398752942097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4147861125694265835294731 6221791688541398752942097)
                  ·
                    refine ⟨4666343766406049064706573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6221791688541398752942097 4666343766406049064706573)
                    ·
                      refine ⟨1749878912402268399264965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4666343766406049064706573 1749878912402268399264965)
                      ·
                        rfl

theorem cell23_3407877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 2, 3, 1, 2, 3].length) (baseStart_3407877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3407877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3407877 prefixEnd_3407877 := by exact prefixLift 3407877
  have htrace : WordTrace (prefixWord ++ tailWord_3407877) baseStart_3407877 baseEnd_3407877 := by
    simpa [prefixWord, tailWord_3407877, baseEnd_3407877] using wordTrace_append hprefix tailTrace_3407877
  have hstable : (prefixWord ++ tailWord_3407877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3407877).length < 2 ^ (prefixWord ++ tailWord_3407877).sum := by decide
  have hdescent : baseEnd_3407877 < baseStart_3407877 := by decide
  rcases family_descends (prefixWord ++ tailWord_3407877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3407885 : List Nat := [1, 7, 1, 2, 1, 2, 1, 1, 3, 1, 3]
def baseStart_3407885 : Nat := 118140960795 + 3407885 * 2 ^ 59
def prefixEnd_3407885 : Nat := 4983230072969 + 3 ^ 40 * 3407885 * 2
def baseEnd_3407885 : Nat := 1749883020247504367964929

theorem tailTrace_3407885 : CollatzResearch.WordTrace tailWord_3407885 prefixEnd_3407885 1749883020247504367964929 := by
  unfold tailWord_3407885
  simp only [CollatzResearch.WordTrace]
  refine ⟨124295777258822140266097109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82863851505881426844064739 124295777258822140266097109)
  ·
    refine ⟨2913182279503643912486651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 124295777258822140266097109 2913182279503643912486651)
    ·
      refine ⟨4369773419255465868729977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2913182279503643912486651 4369773419255465868729977)
      ·
        refine ⟨3277330064441599401547483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4369773419255465868729977 3277330064441599401547483)
        ·
          refine ⟨4915995096662399102321225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3277330064441599401547483 4915995096662399102321225)
          ·
            refine ⟨3686996322496799326740919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4915995096662399102321225 3686996322496799326740919)
            ·
              refine ⟨5530494483745198990111379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3686996322496799326740919 5530494483745198990111379)
              ·
                refine ⟨8295741725617798485167069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5530494483745198990111379 8295741725617798485167069)
                ·
                  refine ⟨3110903147106674431937651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8295741725617798485167069 3110903147106674431937651)
                  ·
                    refine ⟨4666354720660011647906477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3110903147106674431937651 4666354720660011647906477)
                    ·
                      refine ⟨1749883020247504367964929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4666354720660011647906477 1749883020247504367964929)
                      ·
                        rfl

theorem cell23_3407885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 2, 1, 1, 3, 1, 3].length) (baseStart_3407885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3407885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3407885 prefixEnd_3407885 := by exact prefixLift 3407885
  have htrace : WordTrace (prefixWord ++ tailWord_3407885) baseStart_3407885 baseEnd_3407885 := by
    simpa [prefixWord, tailWord_3407885, baseEnd_3407885] using wordTrace_append hprefix tailTrace_3407885
  have hstable : (prefixWord ++ tailWord_3407885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3407885).length < 2 ^ (prefixWord ++ tailWord_3407885).sum := by decide
  have hdescent : baseEnd_3407885 < baseStart_3407885 := by decide
  rcases family_descends (prefixWord ++ tailWord_3407885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3407901 : List Nat := [1, 4, 2, 2, 2, 3, 2, 1, 2, 4]
def baseStart_3407901 : Nat := 118140960795 + 3407901 * 2 ^ 59
def prefixEnd_3407901 : Nat := 4983230072969 + 3 ^ 40 * 3407901 * 2
def baseEnd_3407901 : Nat := 583297078645992101788285

theorem tailTrace_3407901 : CollatzResearch.WordTrace tailWord_3407901 prefixEnd_3407901 583297078645992101788285 := by
  unfold tailWord_3407901
  simp only [CollatzResearch.WordTrace]
  refine ⟨124296360826764174998679557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82864240551176116665786371 124296360826764174998679557)
  ·
    refine ⟨23305567655018282812252417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 124296360826764174998679557 23305567655018282812252417)
    ·
      refine ⟨17479175741263712109189313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23305567655018282812252417 17479175741263712109189313)
      ·
        refine ⟨13109381805947784081891985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17479175741263712109189313 13109381805947784081891985)
        ·
          refine ⟨9832036354460838061418989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13109381805947784081891985 9832036354460838061418989)
          ·
            refine ⟨3687013632922814273032121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9832036354460838061418989 3687013632922814273032121)
            ·
              refine ⟨2765260224692110704774091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3687013632922814273032121 2765260224692110704774091)
              ·
                refine ⟨4147890337038166057161137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2765260224692110704774091 4147890337038166057161137)
                ·
                  refine ⟨3110917752778624542870853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4147890337038166057161137 3110917752778624542870853)
                  ·
                    refine ⟨583297078645992101788285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3110917752778624542870853 583297078645992101788285)
                    ·
                      rfl

theorem cell23_3407901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 3, 2, 1, 2, 4].length) (baseStart_3407901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3407901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3407901 prefixEnd_3407901 := by exact prefixLift 3407901
  have htrace : WordTrace (prefixWord ++ tailWord_3407901) baseStart_3407901 baseEnd_3407901 := by
    simpa [prefixWord, tailWord_3407901, baseEnd_3407901] using wordTrace_append hprefix tailTrace_3407901
  have hstable : (prefixWord ++ tailWord_3407901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3407901).length < 2 ^ (prefixWord ++ tailWord_3407901).sum := by decide
  have hdescent : baseEnd_3407901 < baseStart_3407901 := by decide
  rcases family_descends (prefixWord ++ tailWord_3407901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3407958 : List Nat := [5, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3]
def baseStart_3407958 : Nat := 118140960795 + 3407958 * 2 ^ 59
def prefixEnd_3407958 : Nat := 4983230072969 + 3 ^ 40 * 3407958 * 2
def baseEnd_3407958 : Nat := 1749920504335282582352093

theorem tailTrace_3407958 : CollatzResearch.WordTrace tailWord_3407958 prefixEnd_3407958 1749920504335282582352093 := by
  unfold tailWord_3407958
  simp only [CollatzResearch.WordTrace]
  refine ⟨7768652486722354608344033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 82865626525038449155669685 7768652486722354608344033)
  ·
    refine ⟨5826489365041765956258025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7768652486722354608344033 5826489365041765956258025)
    ·
      refine ⟨4369867023781324467193519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5826489365041765956258025 4369867023781324467193519)
      ·
        refine ⟨6554800535671986700790279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4369867023781324467193519 6554800535671986700790279)
        ·
          refine ⟨9832200803507980051185419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6554800535671986700790279 9832200803507980051185419)
          ·
            refine ⟨14748301205261970076778129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9832200803507980051185419 14748301205261970076778129)
            ·
              refine ⟨11061225903946477557583597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14748301205261970076778129 11061225903946477557583597)
              ·
                refine ⟨4147959713979929084093849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11061225903946477557583597 4147959713979929084093849)
                ·
                  refine ⟨3110969785484946813070387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4147959713979929084093849 3110969785484946813070387)
                  ·
                    refine ⟨4666454678227420219605581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3110969785484946813070387 4666454678227420219605581)
                    ·
                      refine ⟨1749920504335282582352093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4666454678227420219605581 1749920504335282582352093)
                      ·
                        rfl

theorem cell23_3407958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3].length) (baseStart_3407958 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3407958 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3407958 prefixEnd_3407958 := by exact prefixLift 3407958
  have htrace : WordTrace (prefixWord ++ tailWord_3407958) baseStart_3407958 baseEnd_3407958 := by
    simpa [prefixWord, tailWord_3407958, baseEnd_3407958] using wordTrace_append hprefix tailTrace_3407958
  have hstable : (prefixWord ++ tailWord_3407958).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3407958).length < 2 ^ (prefixWord ++ tailWord_3407958).sum := by decide
  have hdescent : baseEnd_3407958 < baseStart_3407958 := by decide
  rcases family_descends (prefixWord ++ tailWord_3407958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3407960 : List Nat := [2, 1, 2, 2, 1, 4, 1, 1, 1, 4, 4]
def baseStart_3407960 : Nat := 118140960795 + 3407960 * 2 ^ 59
def prefixEnd_3407960 : Nat := 4983230072969 + 3 ^ 40 * 3407960 * 2
def baseEnd_3407960 : Nat := 1749921531296591574527083

theorem tailTrace_3407960 : CollatzResearch.WordTrace tailWord_3407960 prefixEnd_3407960 1749921531296591574527083 := by
  unfold tailWord_3407960
  simp only [CollatzResearch.WordTrace]
  refine ⟨62149256366775214037538667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82865675155700285383384889 62149256366775214037538667)
  ·
    refine ⟨93223884550162821056308001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62149256366775214037538667 93223884550162821056308001)
    ·
      refine ⟨69917913412622115792231001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93223884550162821056308001 69917913412622115792231001)
      ·
        refine ⟨52438435059466586844173251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69917913412622115792231001 52438435059466586844173251)
        ·
          refine ⟨78657652589199880266259877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52438435059466586844173251 78657652589199880266259877)
          ·
            refine ⟨14748309860474977549923727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 78657652589199880266259877 14748309860474977549923727)
            ·
              refine ⟨22122464790712466324885591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14748309860474977549923727 22122464790712466324885591)
              ·
                refine ⟨33183697186068699487328387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22122464790712466324885591 33183697186068699487328387)
                ·
                  refine ⟨49775545779103049230992581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33183697186068699487328387 49775545779103049230992581)
                  ·
                    refine ⟨9332914833581821730811109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 49775545779103049230992581 9332914833581821730811109)
                    ·
                      refine ⟨1749921531296591574527083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9332914833581821730811109 1749921531296591574527083)
                      ·
                        rfl

theorem cell23_3407960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 1, 1, 1, 4, 4].length) (baseStart_3407960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3407960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3407960 prefixEnd_3407960 := by exact prefixLift 3407960
  have htrace : WordTrace (prefixWord ++ tailWord_3407960) baseStart_3407960 baseEnd_3407960 := by
    simpa [prefixWord, tailWord_3407960, baseEnd_3407960] using wordTrace_append hprefix tailTrace_3407960
  have hstable : (prefixWord ++ tailWord_3407960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3407960).length < 2 ^ (prefixWord ++ tailWord_3407960).sum := by decide
  have hdescent : baseEnd_3407960 < baseStart_3407960 := by decide
  rcases family_descends (prefixWord ++ tailWord_3407960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3407964 : List Nat := [2, 2, 4, 1, 1, 2, 1, 3, 1, 4, 2]
def baseStart_3407964 : Nat := 118140960795 + 3407964 * 2 ^ 59
def prefixEnd_3407964 : Nat := 4983230072969 + 3 ^ 40 * 3407964 * 2
def baseEnd_3407964 : Nat := 1749923585219209558877065

theorem tailTrace_3407964 : CollatzResearch.WordTrace tailWord_3407964 prefixEnd_3407964 1749923585219209558877065 := by
  unfold tailWord_3407964
  simp only [CollatzResearch.WordTrace]
  refine ⟨62149329312767968379111473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82865772417023957838815297 62149329312767968379111473)
  ·
    refine ⟨46611996984575976284333605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62149329312767968379111473 46611996984575976284333605)
    ·
      refine ⟨8739749434607995553312551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 46611996984575976284333605 8739749434607995553312551)
      ·
        refine ⟨13109624151911993329968827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8739749434607995553312551 13109624151911993329968827)
        ·
          refine ⟨19664436227867989994953241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13109624151911993329968827 19664436227867989994953241)
          ·
            refine ⟨14748327170900992496214931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19664436227867989994953241 14748327170900992496214931)
            ·
              refine ⟨22122490756351488744322397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14748327170900992496214931 22122490756351488744322397)
              ·
                refine ⟨8295934033631808279120899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22122490756351488744322397 8295934033631808279120899)
                ·
                  refine ⟨12443901050447712418681349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8295934033631808279120899 12443901050447712418681349)
                  ·
                    refine ⟨2333231446958946078502753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12443901050447712418681349 2333231446958946078502753)
                    ·
                      refine ⟨1749923585219209558877065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2333231446958946078502753 1749923585219209558877065)
                      ·
                        rfl

theorem cell23_3407964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 1, 3, 1, 4, 2].length) (baseStart_3407964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3407964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3407964 prefixEnd_3407964 := by exact prefixLift 3407964
  have htrace : WordTrace (prefixWord ++ tailWord_3407964) baseStart_3407964 baseEnd_3407964 := by
    simpa [prefixWord, tailWord_3407964, baseEnd_3407964] using wordTrace_append hprefix tailTrace_3407964
  have hstable : (prefixWord ++ tailWord_3407964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3407964).length < 2 ^ (prefixWord ++ tailWord_3407964).sum := by decide
  have hdescent : baseEnd_3407964 < baseStart_3407964 := by decide
  rcases family_descends (prefixWord ++ tailWord_3407964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3407997 : List Nat := [1, 4, 1, 1, 3, 2, 1, 2, 2, 3, 3]
def baseStart_3407997 : Nat := 118140960795 + 3407997 * 2 ^ 59
def prefixEnd_3407997 : Nat := 4983230072969 + 3 ^ 40 * 3407997 * 2
def baseEnd_3407997 : Nat := 1749940530080807929764413

theorem tailTrace_3407997 : CollatzResearch.WordTrace tailWord_3407997 prefixEnd_3407997 1749940530080807929764413 := by
  unfold tailWord_3407997
  simp only [CollatzResearch.WordTrace]
  refine ⟨124299862234416383394174245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82866574822944255596116163 124299862234416383394174245)
  ·
    refine ⟨23306224168953071886407671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 124299862234416383394174245 23306224168953071886407671)
    ·
      refine ⟨34959336253429607829611507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23306224168953071886407671 34959336253429607829611507)
      ·
        refine ⟨52439004380144411744417261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34959336253429607829611507 52439004380144411744417261)
        ·
          refine ⟨19664626642554154404156473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52439004380144411744417261 19664626642554154404156473)
          ·
            refine ⟨14748469981915615803117355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19664626642554154404156473 14748469981915615803117355)
            ·
              refine ⟨22122704972873423704676033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14748469981915615803117355 22122704972873423704676033)
              ·
                refine ⟨16592028729655067778507025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22122704972873423704676033 16592028729655067778507025)
                ·
                  refine ⟨12444021547241300833880269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16592028729655067778507025 12444021547241300833880269)
                  ·
                    refine ⟨4666508080215487812705101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12444021547241300833880269 4666508080215487812705101)
                    ·
                      refine ⟨1749940530080807929764413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4666508080215487812705101 1749940530080807929764413)
                      ·
                        rfl

theorem cell23_3407997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 1, 2, 2, 3, 3].length) (baseStart_3407997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3407997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3407997 prefixEnd_3407997 := by exact prefixLift 3407997
  have htrace : WordTrace (prefixWord ++ tailWord_3407997) baseStart_3407997 baseEnd_3407997 := by
    simpa [prefixWord, tailWord_3407997, baseEnd_3407997] using wordTrace_append hprefix tailTrace_3407997
  have hstable : (prefixWord ++ tailWord_3407997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3407997).length < 2 ^ (prefixWord ++ tailWord_3407997).sum := by decide
  have hdescent : baseEnd_3407997 < baseStart_3407997 := by decide
  rcases family_descends (prefixWord ++ tailWord_3407997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3408000 : List Nat := [2, 1, 1, 2, 1, 3, 1, 3, 4, 5]
def baseStart_3408000 : Nat := 118140960795 + 3408000 * 2 ^ 59
def prefixEnd_3408000 : Nat := 4983230072969 + 3 ^ 40 * 3408000 * 2
def baseEnd_3408000 : Nat := 583314023507590472675633

theorem tailTrace_3408000 : CollatzResearch.WordTrace tailWord_3408000 prefixEnd_3408000 583314023507590472675633 := by
  unfold tailWord_3408000
  simp only [CollatzResearch.WordTrace]
  refine ⟨62149985826702757453266727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82866647768937009937688969 62149985826702757453266727)
  ·
    refine ⟨93224978740054136179900091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62149985826702757453266727 93224978740054136179900091)
    ·
      refine ⟨139837468110081204269850137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93224978740054136179900091 139837468110081204269850137)
      ·
        refine ⟨104878101082560903202387603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 139837468110081204269850137 104878101082560903202387603)
        ·
          refine ⟨157317151623841354803581405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104878101082560903202387603 157317151623841354803581405)
          ·
            refine ⟨58993931858940508051343027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 157317151623841354803581405 58993931858940508051343027)
            ·
              refine ⟨88490897788410762077014541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58993931858940508051343027 88490897788410762077014541)
              ·
                refine ⟨33184086670654035778880453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 88490897788410762077014541 33184086670654035778880453)
                ·
                  refine ⟨6222016250747631708540085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33184086670654035778880453 6222016250747631708540085)
                  ·
                    refine ⟨583314023507590472675633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6222016250747631708540085 583314023507590472675633)
                    ·
                      rfl

theorem cell23_3408000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 3, 4, 5].length) (baseStart_3408000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3408000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3408000 prefixEnd_3408000 := by exact prefixLift 3408000
  have htrace : WordTrace (prefixWord ++ tailWord_3408000) baseStart_3408000 baseEnd_3408000 := by
    simpa [prefixWord, tailWord_3408000, baseEnd_3408000] using wordTrace_append hprefix tailTrace_3408000
  have hstable : (prefixWord ++ tailWord_3408000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3408000).length < 2 ^ (prefixWord ++ tailWord_3408000).sum := by decide
  have hdescent : baseEnd_3408000 < baseStart_3408000 := by decide
  rcases family_descends (prefixWord ++ tailWord_3408000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3408007 : List Nat := [1, 1, 4, 2, 1, 1, 2, 1, 1, 7, 2]
def baseStart_3408007 : Nat := 118140960795 + 3408007 * 2 ^ 59
def prefixEnd_3408007 : Nat := 4983230072969 + 3 ^ 40 * 3408007 * 2
def baseEnd_3408007 : Nat := 1749945664887352890639367

theorem tailTrace_3408007 : CollatzResearch.WordTrace tailWord_3408007 prefixEnd_3408007 1749945664887352890639367 := by
  unfold tailWord_3408007
  simp only [CollatzResearch.WordTrace]
  refine ⟨124300226964380155102038275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82866817976253436734692183 124300226964380155102038275)
  ·
    refine ⟨186450340446570232653057413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124300226964380155102038275 186450340446570232653057413)
    ·
      refine ⟨34959438833731918622448265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 186450340446570232653057413 34959438833731918622448265)
      ·
        refine ⟨26219579125298938966836199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34959438833731918622448265 26219579125298938966836199)
        ·
          refine ⟨39329368687948408450254299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26219579125298938966836199 39329368687948408450254299)
          ·
            refine ⟨58994053031922612675381449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39329368687948408450254299 58994053031922612675381449)
            ·
              refine ⟨44245539773941959506536087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58994053031922612675381449 44245539773941959506536087)
              ·
                refine ⟨66368309660912939259804131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44245539773941959506536087 66368309660912939259804131)
                ·
                  refine ⟨99552464491369408889706197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 66368309660912939259804131 99552464491369408889706197)
                  ·
                    refine ⟨2333260886516470520852489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 99552464491369408889706197 2333260886516470520852489)
                    ·
                      refine ⟨1749945664887352890639367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2333260886516470520852489 1749945664887352890639367)
                      ·
                        rfl

theorem cell23_3408007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 1, 1, 7, 2].length) (baseStart_3408007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3408007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3408007 prefixEnd_3408007 := by exact prefixLift 3408007
  have htrace : WordTrace (prefixWord ++ tailWord_3408007) baseStart_3408007 baseEnd_3408007 := by
    simpa [prefixWord, tailWord_3408007, baseEnd_3408007] using wordTrace_append hprefix tailTrace_3408007
  have hstable : (prefixWord ++ tailWord_3408007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3408007).length < 2 ^ (prefixWord ++ tailWord_3408007).sum := by decide
  have hdescent : baseEnd_3408007 < baseStart_3408007 := by decide
  rcases family_descends (prefixWord ++ tailWord_3408007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3408037 : List Nat := [1, 3, 1, 2, 1, 3, 2, 3, 2, 1, 4]
def baseStart_3408037 : Nat := 118140960795 + 3408037 * 2 ^ 59
def prefixEnd_3408037 : Nat := 4983230072969 + 3 ^ 40 * 3408037 * 2
def baseEnd_3408037 : Nat := 1749961069306987773264229

theorem tailTrace_3408037 : CollatzResearch.WordTrace tailWord_3408037 prefixEnd_3408037 1749961069306987773264229 := by
  unfold tailWord_3408037
  simp only [CollatzResearch.WordTrace]
  refine ⟨124301321154271470225630365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82867547436180980150420243 124301321154271470225630365)
  ·
    refine ⟨46612995432851801334611387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 124301321154271470225630365 46612995432851801334611387)
    ·
      refine ⟨69919493149277702001917081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46612995432851801334611387 69919493149277702001917081)
      ·
        refine ⟨52439619861958276501437811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69919493149277702001917081 52439619861958276501437811)
        ·
          refine ⟨78659429792937414752156717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52439619861958276501437811 78659429792937414752156717)
          ·
            refine ⟨29497286172351530532058769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 78659429792937414752156717 29497286172351530532058769)
            ·
              refine ⟨22122964629263647899044077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29497286172351530532058769 22122964629263647899044077)
              ·
                refine ⟨8296111735973867962141529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22122964629263647899044077 8296111735973867962141529)
                ·
                  refine ⟨6222083801980400971606147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8296111735973867962141529 6222083801980400971606147)
                  ·
                    refine ⟨9333125702970601457409221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6222083801980400971606147 9333125702970601457409221)
                    ·
                      refine ⟨1749961069306987773264229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9333125702970601457409221 1749961069306987773264229)
                      ·
                        rfl

theorem cell23_3408037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 2, 3, 2, 1, 4].length) (baseStart_3408037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3408037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3408037 prefixEnd_3408037 := by exact prefixLift 3408037
  have htrace : WordTrace (prefixWord ++ tailWord_3408037) baseStart_3408037 baseEnd_3408037 := by
    simpa [prefixWord, tailWord_3408037, baseEnd_3408037] using wordTrace_append hprefix tailTrace_3408037
  have hstable : (prefixWord ++ tailWord_3408037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3408037).length < 2 ^ (prefixWord ++ tailWord_3408037).sum := by decide
  have hdescent : baseEnd_3408037 < baseStart_3408037 := by decide
  rcases family_descends (prefixWord ++ tailWord_3408037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3408064 : List Nat := [2, 1, 1, 2, 5, 1, 3, 1, 3, 4]
def baseStart_3408064 : Nat := 118140960795 + 3408064 * 2 ^ 59
def prefixEnd_3408064 : Nat := 4983230072969 + 3 ^ 40 * 3408064 * 2
def baseEnd_3408064 : Nat := 583324977761553055875535

theorem tailTrace_3408064 : CollatzResearch.WordTrace tailWord_3408064 prefixEnd_3408064 583324977761553055875535 := by
  unfold tailWord_3408064
  simp only [CollatzResearch.WordTrace]
  refine ⟨62151152962586826918431623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82868203950115769224575497 62151152962586826918431623)
  ·
    refine ⟨93226729443880240377647435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62151152962586826918431623 93226729443880240377647435)
    ·
      refine ⟨139840094165820360566471153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93226729443880240377647435 139840094165820360566471153)
      ·
        refine ⟨104880070624365270424853365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 139840094165820360566471153 104880070624365270424853365)
        ·
          refine ⟨9832506621034244102330003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 104880070624365270424853365 9832506621034244102330003)
          ·
            refine ⟨14748759931551366153495005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9832506621034244102330003 14748759931551366153495005)
            ·
              refine ⟨5530784974331762307560627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14748759931551366153495005 5530784974331762307560627)
              ·
                refine ⟨8296177461497643461340941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5530784974331762307560627 8296177461497643461340941)
                ·
                  refine ⟨3111066548061616298002853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8296177461497643461340941 3111066548061616298002853)
                  ·
                    refine ⟨583324977761553055875535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3111066548061616298002853 583324977761553055875535)
                    ·
                      rfl

theorem cell23_3408064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 3, 1, 3, 4].length) (baseStart_3408064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3408064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3408064 prefixEnd_3408064 := by exact prefixLift 3408064
  have htrace : WordTrace (prefixWord ++ tailWord_3408064) baseStart_3408064 baseEnd_3408064 := by
    simpa [prefixWord, tailWord_3408064, baseEnd_3408064] using wordTrace_append hprefix tailTrace_3408064
  have hstable : (prefixWord ++ tailWord_3408064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3408064).length < 2 ^ (prefixWord ++ tailWord_3408064).sum := by decide
  have hdescent : baseEnd_3408064 < baseStart_3408064 := by decide
  rcases family_descends (prefixWord ++ tailWord_3408064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3408127 : List Nat := [1, 1, 2, 2, 1, 4, 1, 1, 5, 1, 4]
def baseStart_3408127 : Nat := 118140960795 + 3408127 * 2 ^ 59
def prefixEnd_3408127 : Nat := 4983230072969 + 3 ^ 40 * 3408127 * 2
def baseEnd_3408127 : Nat := 1750007282565892421138815

theorem tailTrace_3408127 : CollatzResearch.WordTrace tailWord_3408127 prefixEnd_3408127 1750007282565892421138815 := by
  unfold tailWord_3408127
  simp only [CollatzResearch.WordTrace]
  refine ⟨124304603723945415596406635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82869735815963610397604423 124304603723945415596406635)
  ·
    refine ⟨186456905585918123394609953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124304603723945415596406635 186456905585918123394609953)
    ·
      refine ⟨139842679189438592545957465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 186456905585918123394609953 139842679189438592545957465)
      ·
        refine ⟨104882009392078944409468099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 139842679189438592545957465 104882009392078944409468099)
        ·
          refine ⟨157323014088118416614202149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104882009392078944409468099 157323014088118416614202149)
          ·
            refine ⟨29498065141522203115162903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 157323014088118416614202149 29498065141522203115162903)
            ·
              refine ⟨44247097712283304672744355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29498065141522203115162903 44247097712283304672744355)
              ·
                refine ⟨66370646568424957009116533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44247097712283304672744355 66370646568424957009116533)
                ·
                  refine ⟨6222248115789839719604675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 66370646568424957009116533 6222248115789839719604675)
                  ·
                    refine ⟨9333372173684759579407013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6222248115789839719604675 9333372173684759579407013)
                    ·
                      refine ⟨1750007282565892421138815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9333372173684759579407013 1750007282565892421138815)
                      ·
                        rfl

theorem cell23_3408127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 1, 5, 1, 4].length) (baseStart_3408127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3408127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3408127 prefixEnd_3408127 := by exact prefixLift 3408127
  have htrace : WordTrace (prefixWord ++ tailWord_3408127) baseStart_3408127 baseEnd_3408127 := by
    simpa [prefixWord, tailWord_3408127, baseEnd_3408127] using wordTrace_append hprefix tailTrace_3408127
  have hstable : (prefixWord ++ tailWord_3408127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3408127).length < 2 ^ (prefixWord ++ tailWord_3408127).sum := by decide
  have hdescent : baseEnd_3408127 < baseStart_3408127 := by decide
  rcases family_descends (prefixWord ++ tailWord_3408127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3408137 : List Nat := [1, 2, 1, 1, 3, 4, 1, 3, 1, 6]
def baseStart_3408137 : Nat := 118140960795 + 3408137 * 2 ^ 59
def prefixEnd_3408137 : Nat := 4983230072969 + 3 ^ 40 * 3408137 * 2
def baseEnd_3408137 : Nat := 583337472457479127337923

theorem tailTrace_3408137 : CollatzResearch.WordTrace tailWord_3408137 prefixEnd_3408137 583337472457479127337923 := by
  unfold tailWord_3408137
  simp only [CollatzResearch.WordTrace]
  refine ⟨124304968453909187304270665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82869978969272791536180443 124304968453909187304270665)
  ·
    refine ⟨93228726340431890478202999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124304968453909187304270665 93228726340431890478202999)
    ·
      refine ⟨139843089510647835717304499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93228726340431890478202999 139843089510647835717304499)
      ·
        refine ⟨209764634265971753575956749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139843089510647835717304499 209764634265971753575956749)
        ·
          refine ⟨78661737849739407590983781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 209764634265971753575956749 78661737849739407590983781)
          ·
            refine ⟨14749075846826138923309459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 78661737849739407590983781 14749075846826138923309459)
            ·
              refine ⟨22123613770239208384964189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14749075846826138923309459 22123613770239208384964189)
              ·
                refine ⟨8296355163839703144361571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22123613770239208384964189 8296355163839703144361571)
                ·
                  refine ⟨12444532745759554716542357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8296355163839703144361571 12444532745759554716542357)
                  ·
                    refine ⟨583337472457479127337923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12444532745759554716542357 583337472457479127337923)
                    ·
                      rfl

theorem cell23_3408137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 1, 3, 1, 6].length) (baseStart_3408137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3408137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3408137 prefixEnd_3408137 := by exact prefixLift 3408137
  have htrace : WordTrace (prefixWord ++ tailWord_3408137) baseStart_3408137 baseEnd_3408137 := by
    simpa [prefixWord, tailWord_3408137, baseEnd_3408137] using wordTrace_append hprefix tailTrace_3408137
  have hstable : (prefixWord ++ tailWord_3408137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3408137).length < 2 ^ (prefixWord ++ tailWord_3408137).sum := by decide
  have hdescent : baseEnd_3408137 < baseStart_3408137 := by decide
  rcases family_descends (prefixWord ++ tailWord_3408137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3408158 : List Nat := [4, 3, 2, 1, 1, 2, 1, 3, 1, 5]
def baseStart_3408158 : Nat := 118140960795 + 3408158 * 2 ^ 59
def prefixEnd_3408158 : Nat := 4983230072969 + 3 ^ 40 * 3408158 * 2
def baseEnd_3408158 : Nat := 583341066822060599950391

theorem tailTrace_3408158 : CollatzResearch.WordTrace tailWord_3408158 prefixEnd_3408158 583341066822060599950391 := by
  unfold tailWord_3408158
  simp only [CollatzResearch.WordTrace]
  refine ⟨15538216798354138486348141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 82870489591222071927190085 15538216798354138486348141)
  ·
    refine ⟨5826831299382801932380553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15538216798354138486348141 5826831299382801932380553)
    ·
      refine ⟨4370123474537101449285415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5826831299382801932380553 4370123474537101449285415)
      ·
        refine ⟨6555185211805652173928123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4370123474537101449285415 6555185211805652173928123)
        ·
          refine ⟨9832777817708478260892185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6555185211805652173928123 9832777817708478260892185)
          ·
            refine ⟨7374583363281358695669139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9832777817708478260892185 7374583363281358695669139)
            ·
              refine ⟨11061875044922038043503709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7374583363281358695669139 11061875044922038043503709)
              ·
                refine ⟨4148203141845764266313891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11061875044922038043503709 4148203141845764266313891)
                ·
                  refine ⟨6222304712768646399470837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4148203141845764266313891 6222304712768646399470837)
                  ·
                    refine ⟨583341066822060599950391, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6222304712768646399470837 583341066822060599950391)
                    ·
                      rfl

theorem cell23_3408158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 1, 3, 1, 5].length) (baseStart_3408158 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3408158 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3408158 prefixEnd_3408158 := by exact prefixLift 3408158
  have htrace : WordTrace (prefixWord ++ tailWord_3408158) baseStart_3408158 baseEnd_3408158 := by
    simpa [prefixWord, tailWord_3408158, baseEnd_3408158] using wordTrace_append hprefix tailTrace_3408158
  have hstable : (prefixWord ++ tailWord_3408158).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3408158).length < 2 ^ (prefixWord ++ tailWord_3408158).sum := by decide
  have hdescent : baseEnd_3408158 < baseStart_3408158 := by decide
  rcases family_descends (prefixWord ++ tailWord_3408158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3408161 : List Nat := [1, 2, 3, 2, 1, 1, 6, 1, 1, 1, 4]
def baseStart_3408161 : Nat := 118140960795 + 3408161 * 2 ^ 59
def prefixEnd_3408161 : Nat := 4983230072969 + 3 ^ 40 * 3408161 * 2
def baseEnd_3408161 : Nat := 1750024740908145288113659

theorem tailTrace_3408161 : CollatzResearch.WordTrace tailWord_3408161 prefixEnd_3408161 1750024740908145288113659 := by
  unfold tailWord_3408161
  simp only [CollatzResearch.WordTrace]
  refine ⟨124305843805822239403144337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82870562537214826268762891 124305843805822239403144337)
  ·
    refine ⟨93229382854366679552358253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124305843805822239403144337 93229382854366679552358253)
    ·
      refine ⟨34961018570387504832134345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93229382854366679552358253 34961018570387504832134345)
      ·
        refine ⟨26220763927790628624100759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34961018570387504832134345 26220763927790628624100759)
        ·
          refine ⟨39331145891685942936151139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26220763927790628624100759 39331145891685942936151139)
          ·
            refine ⟨58996718837528914404226709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39331145891685942936151139 58996718837528914404226709)
            ·
              refine ⟨2765471195509167862698127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 58996718837528914404226709 2765471195509167862698127)
              ·
                refine ⟨4148206793263751794047191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2765471195509167862698127 4148206793263751794047191)
                ·
                  refine ⟨6222310189895627691070787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4148206793263751794047191 6222310189895627691070787)
                  ·
                    refine ⟨9333465284843441536606181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6222310189895627691070787 9333465284843441536606181)
                    ·
                      refine ⟨1750024740908145288113659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9333465284843441536606181 1750024740908145288113659)
                      ·
                        rfl

theorem cell23_3408161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 6, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 6, 1, 1, 1, 4].length) (baseStart_3408161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3408161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3408161 prefixEnd_3408161 := by exact prefixLift 3408161
  have htrace : WordTrace (prefixWord ++ tailWord_3408161) baseStart_3408161 baseEnd_3408161 := by
    simpa [prefixWord, tailWord_3408161, baseEnd_3408161] using wordTrace_append hprefix tailTrace_3408161
  have hstable : (prefixWord ++ tailWord_3408161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3408161).length < 2 ^ (prefixWord ++ tailWord_3408161).sum := by decide
  have hdescent : baseEnd_3408161 < baseStart_3408161 := by decide
  rcases family_descends (prefixWord ++ tailWord_3408161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3408212 : List Nat := [2, 4, 1, 1, 2, 4, 1, 3, 1, 2, 2]
def baseStart_3408212 : Nat := 118140960795 + 3408212 * 2 ^ 59
def prefixEnd_3408212 : Nat := 4983230072969 + 3 ^ 40 * 3408212 * 2
def baseEnd_3408212 : Nat := 1750050928421524588575925

theorem tailTrace_3408212 : CollatzResearch.WordTrace tailWord_3408212 prefixEnd_3408212 1750050928421524588575925 := by
  unfold tailWord_3408212
  simp only [CollatzResearch.WordTrace]
  refine ⟨62153851964318737556625445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82871802619091650075500593 62153851964318737556625445)
  ·
    refine ⟨11653847243309763291867271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 62153851964318737556625445 11653847243309763291867271)
    ·
      refine ⟨17480770864964644937800907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11653847243309763291867271 17480770864964644937800907)
      ·
        refine ⟨26221156297446967406701361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17480770864964644937800907 26221156297446967406701361)
        ·
          refine ⟨19665867223085225555026021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26221156297446967406701361 19665867223085225555026021)
          ·
            refine ⟨3687350104328479791567379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19665867223085225555026021 3687350104328479791567379)
            ·
              refine ⟨5531025156492719687351069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3687350104328479791567379 5531025156492719687351069)
              ·
                refine ⟨2074134433684769882756651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5531025156492719687351069 2074134433684769882756651)
                ·
                  refine ⟨3111201650527154824134977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2074134433684769882756651 3111201650527154824134977)
                  ·
                    refine ⟨2333401237895366118101233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3111201650527154824134977 2333401237895366118101233)
                    ·
                      refine ⟨1750050928421524588575925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2333401237895366118101233 1750050928421524588575925)
                      ·
                        rfl

theorem cell23_3408212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 4, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 4, 1, 3, 1, 2, 2].length) (baseStart_3408212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3408212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3408212 prefixEnd_3408212 := by exact prefixLift 3408212
  have htrace : WordTrace (prefixWord ++ tailWord_3408212) baseStart_3408212 baseEnd_3408212 := by
    simpa [prefixWord, tailWord_3408212, baseEnd_3408212] using wordTrace_append hprefix tailTrace_3408212
  have hstable : (prefixWord ++ tailWord_3408212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3408212).length < 2 ^ (prefixWord ++ tailWord_3408212).sum := by decide
  have hdescent : baseEnd_3408212 < baseStart_3408212 := by decide
  rcases family_descends (prefixWord ++ tailWord_3408212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3408217 : List Nat := [1, 2, 1, 2, 2, 2, 1, 2, 1, 5, 4]
def baseStart_3408217 : Nat := 118140960795 + 3408217 * 2 ^ 59
def prefixEnd_3408217 : Nat := 4983230072969 + 3 ^ 40 * 3408217 * 2
def baseEnd_3408217 : Nat := 1750053495824797069013401

theorem tailTrace_3408217 : CollatzResearch.WordTrace tailWord_3408217 prefixEnd_3408217 1750053495824797069013401 := by
  unfold tailWord_3408217
  simp only [CollatzResearch.WordTrace]
  refine ⟨124307886293619360967182905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82871924195746240644788603 124307886293619360967182905)
  ·
    refine ⟨93230914720214520725387179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124307886293619360967182905 93230914720214520725387179)
    ·
      refine ⟨139846372080321781088080769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93230914720214520725387179 139846372080321781088080769)
      ·
        refine ⟨104884779060241335816060577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 139846372080321781088080769 104884779060241335816060577)
        ·
          refine ⟨78663584295181001862045433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104884779060241335816060577 78663584295181001862045433)
          ·
            refine ⟨58997688221385751396534075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78663584295181001862045433 58997688221385751396534075)
            ·
              refine ⟨88496532332078627094801113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58997688221385751396534075 88496532332078627094801113)
              ·
                refine ⟨66372399249058970321100835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 88496532332078627094801113 66372399249058970321100835)
                ·
                  refine ⟨99558598873588455481651253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 66372399249058970321100835 99558598873588455481651253)
                  ·
                    refine ⟨9333618644398917701404805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 99558598873588455481651253 9333618644398917701404805)
                    ·
                      refine ⟨1750053495824797069013401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9333618644398917701404805 1750053495824797069013401)
                      ·
                        rfl

theorem cell23_3408217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 2, 1, 5, 4].length) (baseStart_3408217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3408217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3408217 prefixEnd_3408217 := by exact prefixLift 3408217
  have htrace : WordTrace (prefixWord ++ tailWord_3408217) baseStart_3408217 baseEnd_3408217 := by
    simpa [prefixWord, tailWord_3408217, baseEnd_3408217] using wordTrace_append hprefix tailTrace_3408217
  have hstable : (prefixWord ++ tailWord_3408217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3408217).length < 2 ^ (prefixWord ++ tailWord_3408217).sum := by decide
  have hdescent : baseEnd_3408217 < baseStart_3408217 := by decide
  rcases family_descends (prefixWord ++ tailWord_3408217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3408245 : List Nat := [1, 3, 4, 1, 2, 1, 4, 1, 2, 1, 3]
def baseStart_3408245 : Nat := 118140960795 + 3408245 * 2 ^ 59
def prefixEnd_3408245 : Nat := 4983230072969 + 3 ^ 40 * 3408245 * 2
def baseEnd_3408245 : Nat := 1750067873283122959463273

theorem tailTrace_3408245 : CollatzResearch.WordTrace tailWord_3408245 prefixEnd_3408245 1750067873283122959463273 := by
  unfold tailWord_3408245
  simp only [CollatzResearch.WordTrace]
  refine ⟨124308907537517921749202189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82872605025011947832801459 124308907537517921749202189)
  ·
    refine ⟨46615840326569220655950821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 124308907537517921749202189 46615840326569220655950821)
    ·
      refine ⟨8740470061231728872990779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 46615840326569220655950821 8740470061231728872990779)
      ·
        refine ⟨13110705091847593309486169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8740470061231728872990779 13110705091847593309486169)
        ·
          refine ⟨9833028818885694982114627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13110705091847593309486169 9833028818885694982114627)
          ·
            refine ⟨14749543228328542473171941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9833028818885694982114627 14749543228328542473171941)
            ·
              refine ⟨2765539355311601713719739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14749543228328542473171941 2765539355311601713719739)
              ·
                refine ⟨4148309032967402570579609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2765539355311601713719739 4148309032967402570579609)
                ·
                  refine ⟨3111231774725551927934707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4148309032967402570579609 3111231774725551927934707)
                  ·
                    refine ⟨4666847662088327891902061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3111231774725551927934707 4666847662088327891902061)
                    ·
                      refine ⟨1750067873283122959463273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4666847662088327891902061 1750067873283122959463273)
                      ·
                        rfl

theorem cell23_3408245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 4, 1, 2, 1, 3].length) (baseStart_3408245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3408245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3408245 prefixEnd_3408245 := by exact prefixLift 3408245
  have htrace : WordTrace (prefixWord ++ tailWord_3408245) baseStart_3408245 baseEnd_3408245 := by
    simpa [prefixWord, tailWord_3408245, baseEnd_3408245] using wordTrace_append hprefix tailTrace_3408245
  have hstable : (prefixWord ++ tailWord_3408245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3408245).length < 2 ^ (prefixWord ++ tailWord_3408245).sum := by decide
  have hdescent : baseEnd_3408245 < baseStart_3408245 := by decide
  rcases family_descends (prefixWord ++ tailWord_3408245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3408291 : List Nat := [1, 1, 1, 4, 1, 5, 1, 4, 5]
def baseStart_3408291 : Nat := 118140960795 + 3408291 * 2 ^ 59
def prefixEnd_3408291 : Nat := 4983230072969 + 3 ^ 40 * 3408291 * 2
def baseEnd_3408291 : Nat := 194454610377025531054229

theorem tailTrace_3408291 : CollatzResearch.WordTrace tailWord_3408291 prefixEnd_3408291 194454610377025531054229 := by
  unfold tailWord_3408291
  simp only [CollatzResearch.WordTrace]
  refine ⟨124310585295351271605376727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82873723530234181070251151 124310585295351271605376727)
  ·
    refine ⟨186465877943026907408065091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124310585295351271605376727 186465877943026907408065091)
    ·
      refine ⟨279698816914540361112097637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186465877943026907408065091 279698816914540361112097637)
      ·
        refine ⟨52443528171476317708518307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 279698816914540361112097637 52443528171476317708518307)
        ·
          refine ⟨78665292257214476562777461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52443528171476317708518307 78665292257214476562777461)
          ·
            refine ⟨7374871149113857177760387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 78665292257214476562777461 7374871149113857177760387)
            ·
              refine ⟨11062306723670785766640581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7374871149113857177760387 11062306723670785766640581)
              ·
                refine ⟨2074182510688272331245109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11062306723670785766640581 2074182510688272331245109)
                ·
                  refine ⟨194454610377025531054229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2074182510688272331245109 194454610377025531054229)
                  ·
                    rfl

theorem cell23_3408291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 1, 4, 5].length) (baseStart_3408291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3408291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3408291 prefixEnd_3408291 := by exact prefixLift 3408291
  have htrace : WordTrace (prefixWord ++ tailWord_3408291) baseStart_3408291 baseEnd_3408291 := by
    simpa [prefixWord, tailWord_3408291, baseEnd_3408291] using wordTrace_append hprefix tailTrace_3408291
  have hstable : (prefixWord ++ tailWord_3408291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3408291).length < 2 ^ (prefixWord ++ tailWord_3408291).sum := by decide
  have hdescent : baseEnd_3408291 < baseStart_3408291 := by decide
  rcases family_descends (prefixWord ++ tailWord_3408291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3408351 : List Nat := [1, 1, 2, 3, 3, 2, 1, 3, 3, 4]
def baseStart_3408351 : Nat := 118140960795 + 3408351 * 2 ^ 59
def prefixEnd_3408351 : Nat := 4983230072969 + 3 ^ 40 * 3408351 * 2
def baseEnd_3408351 : Nat := 583374100744166514912595

theorem tailTrace_3408351 : CollatzResearch.WordTrace tailWord_3408351 prefixEnd_3408351 583374100744166514912595 := by
  unfold tailWord_3408351
  simp only [CollatzResearch.WordTrace]
  refine ⟨124312773675133901852560907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82875182450089267901707271 124312773675133901852560907)
  ·
    refine ⟨186469160512700852778841361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124312773675133901852560907 186469160512700852778841361)
    ·
      refine ⟨139851870384525639584131021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 186469160512700852778841361 139851870384525639584131021)
      ·
        refine ⟨52444451394197114844049133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 139851870384525639584131021 52444451394197114844049133)
        ·
          refine ⟨19666669272823918066518425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52444451394197114844049133 19666669272823918066518425)
          ·
            refine ⟨14750001954617938549888819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19666669272823918066518425 14750001954617938549888819)
            ·
              refine ⟨22125002931926907824833229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14750001954617938549888819 22125002931926907824833229)
              ·
                refine ⟨8296876099472590434312461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22125002931926907824833229 8296876099472590434312461)
                ·
                  refine ⟨3111328537302221412867173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8296876099472590434312461 3111328537302221412867173)
                  ·
                    refine ⟨583374100744166514912595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3111328537302221412867173 583374100744166514912595)
                    ·
                      rfl

theorem cell23_3408351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 1, 3, 3, 4].length) (baseStart_3408351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3408351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3408351 prefixEnd_3408351 := by exact prefixLift 3408351
  have htrace : WordTrace (prefixWord ++ tailWord_3408351) baseStart_3408351 baseEnd_3408351 := by
    simpa [prefixWord, tailWord_3408351, baseEnd_3408351] using wordTrace_append hprefix tailTrace_3408351
  have hstable : (prefixWord ++ tailWord_3408351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3408351).length < 2 ^ (prefixWord ++ tailWord_3408351).sum := by decide
  have hdescent : baseEnd_3408351 < baseStart_3408351 := by decide
  rcases family_descends (prefixWord ++ tailWord_3408351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3408385 : List Nat := [1, 2, 4, 1, 3, 1, 3, 3, 1, 4]
def baseStart_3408385 : Nat := 118140960795 + 3408385 * 2 ^ 59
def prefixEnd_3408385 : Nat := 4983230072969 + 3 ^ 40 * 3408385 * 2
def baseEnd_3408385 : Nat := 583379920191584137237543

theorem tailTrace_3408385 : CollatzResearch.WordTrace tailWord_3408385 prefixEnd_3408385 583379920191584137237543 := by
  unfold tailWord_3408385
  simp only [CollatzResearch.WordTrace]
  refine ⟨124314013757010725659298609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82876009171340483772865739 124314013757010725659298609)
  ·
    refine ⟨93235510317758044244473957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124314013757010725659298609 93235510317758044244473957)
    ·
      refine ⟨17481658184579633295838867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 93235510317758044244473957 17481658184579633295838867)
      ·
        refine ⟨26222487276869449943758301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17481658184579633295838867 26222487276869449943758301)
        ·
          refine ⟨9833432728826043728909363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26222487276869449943758301 9833432728826043728909363)
          ·
            refine ⟨14750149093239065593364045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9833432728826043728909363 14750149093239065593364045)
            ·
              refine ⟨5531305909964649597511517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14750149093239065593364045 5531305909964649597511517)
              ·
                refine ⟨2074239716236743599066819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5531305909964649597511517 2074239716236743599066819)
                ·
                  refine ⟨3111359574355115398600229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2074239716236743599066819 3111359574355115398600229)
                  ·
                    refine ⟨583379920191584137237543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3111359574355115398600229 583379920191584137237543)
                    ·
                      rfl

theorem cell23_3408385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 3, 3, 1, 4].length) (baseStart_3408385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3408385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3408385 prefixEnd_3408385 := by exact prefixLift 3408385
  have htrace : WordTrace (prefixWord ++ tailWord_3408385) baseStart_3408385 baseEnd_3408385 := by
    simpa [prefixWord, tailWord_3408385, baseEnd_3408385] using wordTrace_append hprefix tailTrace_3408385
  have hstable : (prefixWord ++ tailWord_3408385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3408385).length < 2 ^ (prefixWord ++ tailWord_3408385).sum := by decide
  have hdescent : baseEnd_3408385 < baseStart_3408385 := by decide
  rcases family_descends (prefixWord ++ tailWord_3408385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3408401 : List Nat := [1, 2, 2, 1, 1, 2, 2, 2, 3, 5, 2]
def baseStart_3408401 : Nat := 118140960795 + 3408401 * 2 ^ 59
def prefixEnd_3408401 : Nat := 4983230072969 + 3 ^ 40 * 3408401 * 2
def baseEnd_3408401 : Nat := 1750147976265224349112555

theorem tailTrace_3408401 : CollatzResearch.WordTrace tailWord_3408401 prefixEnd_3408401 1750147976265224349112555 := by
  unfold tailWord_3408401
  simp only [CollatzResearch.WordTrace]
  refine ⟨124314597324952760391881057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82876398216635173594587371 124314597324952760391881057)
  ·
    refine ⟨93235947993714570293910793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124314597324952760391881057 93235947993714570293910793)
    ·
      refine ⟨69926960995285927720433095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93235947993714570293910793 69926960995285927720433095)
      ·
        refine ⟨104890441492928891580649643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69926960995285927720433095 104890441492928891580649643)
        ·
          refine ⟨157335662239393337370974465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104890441492928891580649643 157335662239393337370974465)
          ·
            refine ⟨118001746679545003028230849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 157335662239393337370974465 118001746679545003028230849)
            ·
              refine ⟨88501310009658752271173137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 118001746679545003028230849 88501310009658752271173137)
              ·
                refine ⟨66375982507244064203379853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 88501310009658752271173137 66375982507244064203379853)
                ·
                  refine ⟨24890993440216524076267445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 66375982507244064203379853 24890993440216524076267445)
                  ·
                    refine ⟨2333530635020299132150073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 24890993440216524076267445 2333530635020299132150073)
                    ·
                      refine ⟨1750147976265224349112555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2333530635020299132150073 1750147976265224349112555)
                      ·
                        rfl

theorem cell23_3408401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 5, 2].length) (baseStart_3408401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3408401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3408401 prefixEnd_3408401 := by exact prefixLift 3408401
  have htrace : WordTrace (prefixWord ++ tailWord_3408401) baseStart_3408401 baseEnd_3408401 := by
    simpa [prefixWord, tailWord_3408401, baseEnd_3408401] using wordTrace_append hprefix tailTrace_3408401
  have hstable : (prefixWord ++ tailWord_3408401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3408401).length < 2 ^ (prefixWord ++ tailWord_3408401).sum := by decide
  have hdescent : baseEnd_3408401 < baseStart_3408401 := by decide
  rcases family_descends (prefixWord ++ tailWord_3408401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3408418 : List Nat := [3, 3, 1, 1, 1, 1, 1, 1, 6, 3, 2]
def baseStart_3408418 : Nat := 118140960795 + 3408418 * 2 ^ 59
def prefixEnd_3408418 : Nat := 4983230072969 + 3 ^ 40 * 3408418 * 2
def baseEnd_3408418 : Nat := 1750156705436350782599977

theorem tailTrace_3408418 : CollatzResearch.WordTrace tailWord_3408418 prefixEnd_3408418 1750156705436350782599977 := by
  unfold tailWord_3408418
  simp only [CollatzResearch.WordTrace]
  refine ⟨31078804341472793073812477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82876811577260781530166605 31078804341472793073812477)
  ·
    refine ⟨11654551628052297402679679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31078804341472793073812477 11654551628052297402679679)
    ·
      refine ⟨17481827442078446104019519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11654551628052297402679679 17481827442078446104019519)
      ·
        refine ⟨26222741163117669156029279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17481827442078446104019519 26222741163117669156029279)
        ·
          refine ⟨39334111744676503734043919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26222741163117669156029279 39334111744676503734043919)
          ·
            refine ⟨59001167617014755601065879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39334111744676503734043919 59001167617014755601065879)
            ·
              refine ⟨88501751425522133401598819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59001167617014755601065879 88501751425522133401598819)
              ·
                refine ⟨132752627138283200102398229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 88501751425522133401598819 132752627138283200102398229)
                ·
                  refine ⟨6222779397107025004799917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 132752627138283200102398229 6222779397107025004799917)
                  ·
                    refine ⟨2333542273915134376799969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6222779397107025004799917 2333542273915134376799969)
                    ·
                      refine ⟨1750156705436350782599977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2333542273915134376799969 1750156705436350782599977)
                      ·
                        rfl

theorem cell23_3408418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 1, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 1, 6, 3, 2].length) (baseStart_3408418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3408418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3408418 prefixEnd_3408418 := by exact prefixLift 3408418
  have htrace : WordTrace (prefixWord ++ tailWord_3408418) baseStart_3408418 baseEnd_3408418 := by
    simpa [prefixWord, tailWord_3408418, baseEnd_3408418] using wordTrace_append hprefix tailTrace_3408418
  have hstable : (prefixWord ++ tailWord_3408418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3408418).length < 2 ^ (prefixWord ++ tailWord_3408418).sum := by decide
  have hdescent : baseEnd_3408418 < baseStart_3408418 := by decide
  rcases family_descends (prefixWord ++ tailWord_3408418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3408429 : List Nat := [1, 5, 4, 1, 1, 1, 2, 1, 2, 2, 3]
def baseStart_3408429 : Nat := 118140960795 + 3408429 * 2 ^ 59
def prefixEnd_3408429 : Nat := 4983230072969 + 3 ^ 40 * 3408429 * 2
def baseEnd_3408429 : Nat := 1750162353723550239562427

theorem tailTrace_3408429 : CollatzResearch.WordTrace tailWord_3408429 prefixEnd_3408429 1750162353723550239562427 := by
  unfold tailWord_3408429
  simp only [CollatzResearch.WordTrace]
  refine ⟨124315618568851321173900341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82877079045900880782600227 124315618568851321173900341)
  ·
    refine ⟨11654589240829811360053157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 124315618568851321173900341 11654589240829811360053157)
    ·
      refine ⟨2185235482655589630009967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11654589240829811360053157 2185235482655589630009967)
      ·
        refine ⟨3277853223983384445014951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2185235482655589630009967 3277853223983384445014951)
        ·
          refine ⟨4916779835975076667522427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3277853223983384445014951 4916779835975076667522427)
          ·
            refine ⟨7375169753962615001283641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4916779835975076667522427 7375169753962615001283641)
            ·
              refine ⟨5531377315471961250962731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7375169753962615001283641 5531377315471961250962731)
              ·
                refine ⟨8297065973207941876444097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5531377315471961250962731 8297065973207941876444097)
                ·
                  refine ⟨6222799479905956407333073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8297065973207941876444097 6222799479905956407333073)
                  ·
                    refine ⟨4667099609929467305499805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6222799479905956407333073 4667099609929467305499805)
                    ·
                      refine ⟨1750162353723550239562427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4667099609929467305499805 1750162353723550239562427)
                      ·
                        rfl

theorem cell23_3408429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 2, 1, 2, 2, 3].length) (baseStart_3408429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3408429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3408429 prefixEnd_3408429 := by exact prefixLift 3408429
  have htrace : WordTrace (prefixWord ++ tailWord_3408429) baseStart_3408429 baseEnd_3408429 := by
    simpa [prefixWord, tailWord_3408429, baseEnd_3408429] using wordTrace_append hprefix tailTrace_3408429
  have hstable : (prefixWord ++ tailWord_3408429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3408429).length < 2 ^ (prefixWord ++ tailWord_3408429).sum := by decide
  have hdescent : baseEnd_3408429 < baseStart_3408429 := by decide
  rcases family_descends (prefixWord ++ tailWord_3408429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3408441 : List Nat := [1, 2, 1, 5, 1, 1, 3, 2, 1, 6]
def baseStart_3408441 : Nat := 118140960795 + 3408441 * 2 ^ 59
def prefixEnd_3408441 : Nat := 4983230072969 + 3 ^ 40 * 3408441 * 2
def baseEnd_3408441 : Nat := 583389505163801397537457

theorem tailTrace_3408441 : CollatzResearch.WordTrace tailWord_3408441 prefixEnd_3408441 583389505163801397537457 := by
  unfold tailWord_3408441
  simp only [CollatzResearch.WordTrace]
  refine ⟨124316056244807847223337177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82877370829871898148891451 124316056244807847223337177)
  ·
    refine ⟨93237042183605885417502883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124316056244807847223337177 93237042183605885417502883)
    ·
      refine ⟨139855563275408828126254325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93237042183605885417502883 139855563275408828126254325)
      ·
        refine ⟨13111459057069577636836343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 139855563275408828126254325 13111459057069577636836343)
        ·
          refine ⟨19667188585604366455254515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13111459057069577636836343 19667188585604366455254515)
          ·
            refine ⟨29500782878406549682881773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19667188585604366455254515 29500782878406549682881773)
            ·
              refine ⟨11062793579402456131080665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29500782878406549682881773 11062793579402456131080665)
              ·
                refine ⟨8297095184551842098310499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11062793579402456131080665 8297095184551842098310499)
                ·
                  refine ⟨12445642776827763147465749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8297095184551842098310499 12445642776827763147465749)
                  ·
                    refine ⟨583389505163801397537457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12445642776827763147465749 583389505163801397537457)
                    ·
                      rfl

theorem cell23_3408441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 3, 2, 1, 6].length) (baseStart_3408441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3408441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3408441 prefixEnd_3408441 := by exact prefixLift 3408441
  have htrace : WordTrace (prefixWord ++ tailWord_3408441) baseStart_3408441 baseEnd_3408441 := by
    simpa [prefixWord, tailWord_3408441, baseEnd_3408441] using wordTrace_append hprefix tailTrace_3408441
  have hstable : (prefixWord ++ tailWord_3408441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3408441).length < 2 ^ (prefixWord ++ tailWord_3408441).sum := by decide
  have hdescent : baseEnd_3408441 < baseStart_3408441 := by decide
  rcases family_descends (prefixWord ++ tailWord_3408441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3408445 : List Nat := [1, 4, 1, 3, 2, 2, 3, 1, 1, 5]
def baseStart_3408445 : Nat := 118140960795 + 3408445 * 2 ^ 59
def prefixEnd_3408445 : Nat := 4983230072969 + 3 ^ 40 * 3408445 * 2
def baseEnd_3408445 : Nat := 583390189804674058987451

theorem tailTrace_3408445 : CollatzResearch.WordTrace tailWord_3408445 prefixEnd_3408445 583390189804674058987451 := by
  unfold tailWord_3408445
  simp only [CollatzResearch.WordTrace]
  refine ⟨124316202136793355906482789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82877468091195570604321859 124316202136793355906482789)
  ·
    refine ⟨23309287900648754232465523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 124316202136793355906482789 23309287900648754232465523)
    ·
      refine ⟨34963931850973131348698285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23309287900648754232465523 34963931850973131348698285)
      ·
        refine ⟨13111474444114924255761857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34963931850973131348698285 13111474444114924255761857)
        ·
          refine ⟨9833605833086193191821393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13111474444114924255761857 9833605833086193191821393)
          ·
            refine ⟨7375204374814644893866045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9833605833086193191821393 7375204374814644893866045)
            ·
              refine ⟨2765701640555491835199767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7375204374814644893866045 2765701640555491835199767)
              ·
                refine ⟨4148552460833237752799651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2765701640555491835199767 4148552460833237752799651)
                ·
                  refine ⟨6222828691249856629199477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4148552460833237752799651 6222828691249856629199477)
                  ·
                    refine ⟨583390189804674058987451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6222828691249856629199477 583390189804674058987451)
                    ·
                      rfl

theorem cell23_3408445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 3, 1, 1, 5].length) (baseStart_3408445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3408445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3408445 prefixEnd_3408445 := by exact prefixLift 3408445
  have htrace : WordTrace (prefixWord ++ tailWord_3408445) baseStart_3408445 baseEnd_3408445 := by
    simpa [prefixWord, tailWord_3408445, baseEnd_3408445] using wordTrace_append hprefix tailTrace_3408445
  have hstable : (prefixWord ++ tailWord_3408445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3408445).length < 2 ^ (prefixWord ++ tailWord_3408445).sum := by decide
  have hdescent : baseEnd_3408445 < baseStart_3408445 := by decide
  rcases family_descends (prefixWord ++ tailWord_3408445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3408458 : List Nat := [3, 1, 2, 1, 1, 4, 1, 4, 2, 4]
def baseStart_3408458 : Nat := 118140960795 + 3408458 * 2 ^ 59
def prefixEnd_3408458 : Nat := 4983230072969 + 3 ^ 40 * 3408458 * 2
def baseEnd_3408458 : Nat := 583392414887510208699931

theorem tailTrace_3408458 : CollatzResearch.WordTrace tailWord_3408458 prefixEnd_3408458 583392414887510208699931 := by
  unfold tailWord_3408458
  simp only [CollatzResearch.WordTrace]
  refine ⟨31079169071436564781676507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82877784190497506084470685 31079169071436564781676507)
  ·
    refine ⟨46618753607154847172514761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31079169071436564781676507 46618753607154847172514761)
    ·
      refine ⟨34964065205366135379386071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46618753607154847172514761 34964065205366135379386071)
      ·
        refine ⟨52446097808049203069079107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34964065205366135379386071 52446097808049203069079107)
        ·
          refine ⟨78669146712073804603618661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52446097808049203069079107 78669146712073804603618661)
          ·
            refine ⟨14750465008513838363178499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 78669146712073804603618661 14750465008513838363178499)
            ·
              refine ⟨22125697512770757544767749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14750465008513838363178499 22125697512770757544767749)
              ·
                refine ⟨4148568283644517039643953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22125697512770757544767749 4148568283644517039643953)
                ·
                  refine ⟨3111426212733387779732965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4148568283644517039643953 3111426212733387779732965)
                  ·
                    refine ⟨583392414887510208699931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3111426212733387779732965 583392414887510208699931)
                    ·
                      rfl

theorem cell23_3408458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 1, 4, 2, 4].length) (baseStart_3408458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3408458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3408458 prefixEnd_3408458 := by exact prefixLift 3408458
  have htrace : WordTrace (prefixWord ++ tailWord_3408458) baseStart_3408458 baseEnd_3408458 := by
    simpa [prefixWord, tailWord_3408458, baseEnd_3408458] using wordTrace_append hprefix tailTrace_3408458
  have hstable : (prefixWord ++ tailWord_3408458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3408458).length < 2 ^ (prefixWord ++ tailWord_3408458).sum := by decide
  have hdescent : baseEnd_3408458 < baseStart_3408458 := by decide
  rcases family_descends (prefixWord ++ tailWord_3408458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3408464 : List Nat := [2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 7]
def baseStart_3408464 : Nat := 118140960795 + 3408464 * 2 ^ 59
def prefixEnd_3408464 : Nat := 4983230072969 + 3 ^ 40 * 3408464 * 2
def baseEnd_3408464 : Nat := 1750180325546457602624765

theorem tailTrace_3408464 : CollatzResearch.WordTrace tailWord_3408464 prefixEnd_3408464 1750180325546457602624765 := by
  unfold tailWord_3408464
  simp only [CollatzResearch.WordTrace]
  refine ⟨62158447561862261075712223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82877930082483014767616297 62158447561862261075712223)
  ·
    refine ⟨93237671342793391613568335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62158447561862261075712223 93237671342793391613568335)
    ·
      refine ⟨139856507014190087420352503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93237671342793391613568335 139856507014190087420352503)
      ·
        refine ⟨209784760521285131130528755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139856507014190087420352503 209784760521285131130528755)
        ·
          refine ⟨314677140781927696695793133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 209784760521285131130528755 314677140781927696695793133)
          ·
            refine ⟨118003927793222886260922425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 314677140781927696695793133 118003927793222886260922425)
            ·
              refine ⟨88502945844917164695691819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 118003927793222886260922425 88502945844917164695691819)
              ·
                refine ⟨132754418767375747043537729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 88502945844917164695691819 132754418767375747043537729)
                ·
                  refine ⟨99565814075531810282653297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 132754418767375747043537729 99565814075531810282653297)
                  ·
                    refine ⟨74674360556648857711989973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 99565814075531810282653297 74674360556648857711989973)
                    ·
                      refine ⟨1750180325546457602624765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 74674360556648857711989973 1750180325546457602624765)
                      ·
                        rfl

theorem cell23_3408464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 7].length) (baseStart_3408464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3408464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3408464 prefixEnd_3408464 := by exact prefixLift 3408464
  have htrace : WordTrace (prefixWord ++ tailWord_3408464) baseStart_3408464 baseEnd_3408464 := by
    simpa [prefixWord, tailWord_3408464, baseEnd_3408464] using wordTrace_append hprefix tailTrace_3408464
  have hstable : (prefixWord ++ tailWord_3408464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3408464).length < 2 ^ (prefixWord ++ tailWord_3408464).sum := by decide
  have hdescent : baseEnd_3408464 < baseStart_3408464 := by decide
  rcases family_descends (prefixWord ++ tailWord_3408464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3408468 : List Nat := [2, 4, 1, 1, 1, 3, 1, 2, 3, 2, 3]
def baseStart_3408468 : Nat := 118140960795 + 3408468 * 2 ^ 59
def prefixEnd_3408468 : Nat := 4983230072969 + 3 ^ 40 * 3408468 * 2
def baseEnd_3408468 : Nat := 1750182379469075586974747

theorem tailTrace_3408468 : CollatzResearch.WordTrace tailWord_3408468 prefixEnd_3408468 1750182379469075586974747 := by
  unfold tailWord_3408468
  simp only [CollatzResearch.WordTrace]
  refine ⟨62158520507855015417285029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82878027343806687223046705 62158520507855015417285029)
  ·
    refine ⟨11654722595222815390740943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 62158520507855015417285029 11654722595222815390740943)
    ·
      refine ⟨17482083892834223086111415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11654722595222815390740943 17482083892834223086111415)
      ·
        refine ⟨26223125839251334629167123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17482083892834223086111415 26223125839251334629167123)
        ·
          refine ⟨39334688758877001943750685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26223125839251334629167123 39334688758877001943750685)
          ·
            refine ⟨14750508284578875728906507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39334688758877001943750685 14750508284578875728906507)
            ·
              refine ⟨22125762426868313593359761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14750508284578875728906507 22125762426868313593359761)
              ·
                refine ⟨16594321820151235195019821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22125762426868313593359761 16594321820151235195019821)
                ·
                  refine ⟨6222870682556713198132433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16594321820151235195019821 6222870682556713198132433)
                  ·
                    refine ⟨4667153011917534898599325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6222870682556713198132433 4667153011917534898599325)
                    ·
                      refine ⟨1750182379469075586974747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4667153011917534898599325 1750182379469075586974747)
                      ·
                        rfl

theorem cell23_3408468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 1, 2, 3, 2, 3].length) (baseStart_3408468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3408468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3408468 prefixEnd_3408468 := by exact prefixLift 3408468
  have htrace : WordTrace (prefixWord ++ tailWord_3408468) baseStart_3408468 baseEnd_3408468 := by
    simpa [prefixWord, tailWord_3408468, baseEnd_3408468] using wordTrace_append hprefix tailTrace_3408468
  have hstable : (prefixWord ++ tailWord_3408468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3408468).length < 2 ^ (prefixWord ++ tailWord_3408468).sum := by decide
  have hdescent : baseEnd_3408468 < baseStart_3408468 := by decide
  rcases family_descends (prefixWord ++ tailWord_3408468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3408502 : List Nat := [5, 1, 1, 2, 3, 1, 1, 3, 1, 2, 3]
def baseStart_3408502 : Nat := 118140960795 + 3408502 * 2 ^ 59
def prefixEnd_3408502 : Nat := 4983230072969 + 3 ^ 40 * 3408502 * 2
def baseEnd_3408502 : Nat := 1750199837811328453949591

theorem tailTrace_3408502 : CollatzResearch.WordTrace tailWord_3408502 prefixEnd_3408502 1750199837811328453949591 := by
  unfold tailWord_3408502
  simp only [CollatzResearch.WordTrace]
  refine ⟨7769892568599178415081735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 82878854065057903094205173 7769892568599178415081735)
  ·
    refine ⟨11654838852898767622622603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7769892568599178415081735 11654838852898767622622603)
    ·
      refine ⟨17482258279348151433933905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11654838852898767622622603 17482258279348151433933905)
      ·
        refine ⟨13111693709511113575450429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17482258279348151433933905 13111693709511113575450429)
        ·
          refine ⟨4916885141066667590793911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13111693709511113575450429 4916885141066667590793911)
          ·
            refine ⟨7375327711600001386190867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4916885141066667590793911 7375327711600001386190867)
            ·
              refine ⟨11062991567400002079286301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7375327711600001386190867 11062991567400002079286301)
              ·
                refine ⟨4148621837775000779732363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11062991567400002079286301 4148621837775000779732363)
                ·
                  refine ⟨6222932756662501169598545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4148621837775000779732363 6222932756662501169598545)
                  ·
                    refine ⟨4667199567496875877198909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6222932756662501169598545 4667199567496875877198909)
                    ·
                      refine ⟨1750199837811328453949591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4667199567496875877198909 1750199837811328453949591)
                      ·
                        rfl

theorem cell23_3408502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 1, 3, 1, 2, 3].length) (baseStart_3408502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3408502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3408502 prefixEnd_3408502 := by exact prefixLift 3408502
  have htrace : WordTrace (prefixWord ++ tailWord_3408502) baseStart_3408502 baseEnd_3408502 := by
    simpa [prefixWord, tailWord_3408502, baseEnd_3408502] using wordTrace_append hprefix tailTrace_3408502
  have hstable : (prefixWord ++ tailWord_3408502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3408502).length < 2 ^ (prefixWord ++ tailWord_3408502).sum := by decide
  have hdescent : baseEnd_3408502 < baseStart_3408502 := by decide
  rcases family_descends (prefixWord ++ tailWord_3408502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3408515 : List Nat := [1, 1, 1, 3, 3, 1, 5, 2, 2, 1, 3]
def baseStart_3408515 : Nat := 118140960795 + 3408515 * 2 ^ 59
def prefixEnd_3408515 : Nat := 4983230072969 + 3 ^ 40 * 3408515 * 2
def baseEnd_3408515 : Nat := 1750206513059836903087031

theorem tailTrace_3408515 : CollatzResearch.WordTrace tailWord_3408515 prefixEnd_3408515 1750206513059836903087031 := by
  unfold tailWord_3408515
  simp only [CollatzResearch.WordTrace]
  refine ⟨124318755246539757861530999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82879170164359838574353999 124318755246539757861530999)
  ·
    refine ⟨186478132869809636792296499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124318755246539757861530999 186478132869809636792296499)
    ·
      refine ⟨279717199304714455188444749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186478132869809636792296499 279717199304714455188444749)
      ·
        refine ⟨104893949739267920695666781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 279717199304714455188444749 104893949739267920695666781)
        ·
          refine ⟨39335231152225470260875043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 104893949739267920695666781 39335231152225470260875043)
          ·
            refine ⟨59002846728338205391312565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39335231152225470260875043 59002846728338205391312565)
            ·
              refine ⟨5531516880781706755435553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 59002846728338205391312565 5531516880781706755435553)
              ·
                refine ⟨4148637660586280066576665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5531516880781706755435553 4148637660586280066576665)
                ·
                  refine ⟨3111478245439710049932499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4148637660586280066576665 3111478245439710049932499)
                  ·
                    refine ⟨4667217368159565074898749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3111478245439710049932499 4667217368159565074898749)
                    ·
                      refine ⟨1750206513059836903087031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4667217368159565074898749 1750206513059836903087031)
                      ·
                        rfl

theorem cell23_3408515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 5, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 5, 2, 2, 1, 3].length) (baseStart_3408515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3408515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3408515 prefixEnd_3408515 := by exact prefixLift 3408515
  have htrace : WordTrace (prefixWord ++ tailWord_3408515) baseStart_3408515 baseEnd_3408515 := by
    simpa [prefixWord, tailWord_3408515, baseEnd_3408515] using wordTrace_append hprefix tailTrace_3408515
  have hstable : (prefixWord ++ tailWord_3408515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3408515).length < 2 ^ (prefixWord ++ tailWord_3408515).sum := by decide
  have hdescent : baseEnd_3408515 < baseStart_3408515 := by decide
  rcases family_descends (prefixWord ++ tailWord_3408515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3408532 : List Nat := [2, 4, 2, 2, 1, 3, 1, 1, 1, 3, 3]
def baseStart_3408532 : Nat := 118140960795 + 3408532 * 2 ^ 59
def prefixEnd_3408532 : Nat := 4983230072969 + 3 ^ 40 * 3408532 * 2
def baseEnd_3408532 : Nat := 1750215242230963336574453

theorem tailTrace_3408532 : CollatzResearch.WordTrace tailWord_3408532 prefixEnd_3408532 1750215242230963336574453 := by
  unfold tailWord_3408532
  simp only [CollatzResearch.WordTrace]
  refine ⟨62159687643739084882449925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82879583524985446509933233 62159687643739084882449925)
  ·
    refine ⟨11654941433201078415459361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 62159687643739084882449925 11654941433201078415459361)
    ·
      refine ⟨8741206074900808811594521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11654941433201078415459361 8741206074900808811594521)
      ·
        refine ⟨6555904556175606608695891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8741206074900808811594521 6555904556175606608695891)
        ·
          refine ⟨9833856834263409913043837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6555904556175606608695891 9833856834263409913043837)
          ·
            refine ⟨3687696312848778717391439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9833856834263409913043837 3687696312848778717391439)
            ·
              refine ⟨5531544469273168076087159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3687696312848778717391439 5531544469273168076087159)
              ·
                refine ⟨8297316703909752114130739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5531544469273168076087159 8297316703909752114130739)
                ·
                  refine ⟨12445975055864628171196109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8297316703909752114130739 12445975055864628171196109)
                  ·
                    refine ⟨4667240645949235564198541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12445975055864628171196109 4667240645949235564198541)
                    ·
                      refine ⟨1750215242230963336574453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4667240645949235564198541 1750215242230963336574453)
                      ·
                        rfl

theorem cell23_3408532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 3, 1, 1, 1, 3, 3].length) (baseStart_3408532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3408532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3408532 prefixEnd_3408532 := by exact prefixLift 3408532
  have htrace : WordTrace (prefixWord ++ tailWord_3408532) baseStart_3408532 baseEnd_3408532 := by
    simpa [prefixWord, tailWord_3408532, baseEnd_3408532] using wordTrace_append hprefix tailTrace_3408532
  have hstable : (prefixWord ++ tailWord_3408532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3408532).length < 2 ^ (prefixWord ++ tailWord_3408532).sum := by decide
  have hdescent : baseEnd_3408532 < baseStart_3408532 := by decide
  rcases family_descends (prefixWord ++ tailWord_3408532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3408572 : List Nat := [2, 2, 2, 3, 1, 1, 2, 4, 2, 2, 2]
def baseStart_3408572 : Nat := 118140960795 + 3408572 * 2 ^ 59
def prefixEnd_3408572 : Nat := 4983230072969 + 3 ^ 40 * 3408572 * 2
def baseEnd_3408572 : Nat := 1750235781457143180074269

theorem tailTrace_3408572 : CollatzResearch.WordTrace tailWord_3408572 prefixEnd_3408572 1750235781457143180074269 := by
  unfold tailWord_3408572
  simp only [CollatzResearch.WordTrace]
  refine ⟨62160417103666628298177985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82880556138222171064237313 62160417103666628298177985)
  ·
    refine ⟨46620312827749971223633489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62160417103666628298177985 46620312827749971223633489)
    ·
      refine ⟨34965234620812478417725117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46620312827749971223633489 34965234620812478417725117)
      ·
        refine ⟨13111962982804679406646919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34965234620812478417725117 13111962982804679406646919)
        ·
          refine ⟨19667944474207019109970379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13111962982804679406646919 19667944474207019109970379)
          ·
            refine ⟨29501916711310528664955569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19667944474207019109970379 29501916711310528664955569)
            ·
              refine ⟨22126437533482896498716677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29501916711310528664955569 22126437533482896498716677)
              ·
                refine ⟨4148707037528043093509377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22126437533482896498716677 4148707037528043093509377)
                ·
                  refine ⟨3111530278146032320132033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4148707037528043093509377 3111530278146032320132033)
                  ·
                    refine ⟨2333647708609524240099025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3111530278146032320132033 2333647708609524240099025)
                    ·
                      refine ⟨1750235781457143180074269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2333647708609524240099025 1750235781457143180074269)
                      ·
                        rfl

theorem cell23_3408572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 2, 4, 2, 2, 2].length) (baseStart_3408572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3408572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3408572 prefixEnd_3408572 := by exact prefixLift 3408572
  have htrace : WordTrace (prefixWord ++ tailWord_3408572) baseStart_3408572 baseEnd_3408572 := by
    simpa [prefixWord, tailWord_3408572, baseEnd_3408572] using wordTrace_append hprefix tailTrace_3408572
  have hstable : (prefixWord ++ tailWord_3408572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3408572).length < 2 ^ (prefixWord ++ tailWord_3408572).sum := by decide
  have hdescent : baseEnd_3408572 < baseStart_3408572 := by decide
  rcases family_descends (prefixWord ++ tailWord_3408572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3408601 : List Nat := [1, 2, 1, 2, 3, 2, 1, 2, 1, 1, 7]
def baseStart_3408601 : Nat := 118140960795 + 3408601 * 2 ^ 59
def prefixEnd_3408601 : Nat := 4983230072969 + 3 ^ 40 * 3408601 * 2
def baseEnd_3408601 : Nat := 1750250672396123566611635

theorem tailTrace_3408601 : CollatzResearch.WordTrace tailWord_3408601 prefixEnd_3408601 1750250672396123566611635 := by
  unfold tailWord_3408601
  simp only [CollatzResearch.WordTrace]
  refine ⟨124321891924228194549161657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82881261282818796366107771 124321891924228194549161657)
  ·
    refine ⟨93241418943171145911871243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124321891924228194549161657 93241418943171145911871243)
    ·
      refine ⟨139862128414756718867806865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93241418943171145911871243 139862128414756718867806865)
      ·
        refine ⟨104896596311067539150855149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 139862128414756718867806865 104896596311067539150855149)
        ·
          refine ⟨39336223616650327181570681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 104896596311067539150855149 39336223616650327181570681)
          ·
            refine ⟨29502167712487745386178011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39336223616650327181570681 29502167712487745386178011)
            ·
              refine ⟨44253251568731618079267017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29502167712487745386178011 44253251568731618079267017)
              ·
                refine ⟨33189938676548713559450263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44253251568731618079267017 33189938676548713559450263)
                ·
                  refine ⟨49784908014823070339175395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33189938676548713559450263 49784908014823070339175395)
                  ·
                    refine ⟨74677362022234605508763093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 49784908014823070339175395 74677362022234605508763093)
                    ·
                      refine ⟨1750250672396123566611635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 74677362022234605508763093 1750250672396123566611635)
                      ·
                        rfl

theorem cell23_3408601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 2, 1, 1, 7].length) (baseStart_3408601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3408601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3408601 prefixEnd_3408601 := by exact prefixLift 3408601
  have htrace : WordTrace (prefixWord ++ tailWord_3408601) baseStart_3408601 baseEnd_3408601 := by
    simpa [prefixWord, tailWord_3408601, baseEnd_3408601] using wordTrace_append hprefix tailTrace_3408601
  have hstable : (prefixWord ++ tailWord_3408601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3408601).length < 2 ^ (prefixWord ++ tailWord_3408601).sum := by decide
  have hdescent : baseEnd_3408601 < baseStart_3408601 := by decide
  rcases family_descends (prefixWord ++ tailWord_3408601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3408631 : List Nat := [1, 1, 3, 1, 1, 1, 3, 1, 1, 5, 5]
def baseStart_3408631 : Nat := 118140960795 + 3408631 * 2 ^ 59
def prefixEnd_3408631 : Nat := 4983230072969 + 3 ^ 40 * 3408631 * 2
def baseEnd_3408631 : Nat := 1750266076815758449236497

theorem tailTrace_3408631 : CollatzResearch.WordTrace tailWord_3408631 prefixEnd_3408631 1750266076815758449236497 := by
  unfold tailWord_3408631
  simp only [CollatzResearch.WordTrace]
  refine ⟨124322986114119509672753747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82881990742746339781835831 124322986114119509672753747)
  ·
    refine ⟨186484479171179264509130621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124322986114119509672753747 186484479171179264509130621)
    ·
      refine ⟨69931679689192224190923983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 186484479171179264509130621 69931679689192224190923983)
      ·
        refine ⟨104897519533788336286385975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69931679689192224190923983 104897519533788336286385975)
        ·
          refine ⟨157346279300682504429578963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104897519533788336286385975 157346279300682504429578963)
          ·
            refine ⟨236019418951023756644368445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 157346279300682504429578963 236019418951023756644368445)
            ·
              refine ⟨88507282106633908741638167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 236019418951023756644368445 88507282106633908741638167)
              ·
                refine ⟨132760923159950863112457251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 88507282106633908741638167 132760923159950863112457251)
                ·
                  refine ⟨199141384739926294668685877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 132760923159950863112457251 199141384739926294668685877)
                  ·
                    refine ⟨18669504819368090125189301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 199141384739926294668685877 18669504819368090125189301)
                    ·
                      refine ⟨1750266076815758449236497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18669504819368090125189301 1750266076815758449236497)
                      ·
                        rfl

theorem cell23_3408631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 1, 1, 5, 5].length) (baseStart_3408631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3408631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3408631 prefixEnd_3408631 := by exact prefixLift 3408631
  have htrace : WordTrace (prefixWord ++ tailWord_3408631) baseStart_3408631 baseEnd_3408631 := by
    simpa [prefixWord, tailWord_3408631, baseEnd_3408631] using wordTrace_append hprefix tailTrace_3408631
  have hstable : (prefixWord ++ tailWord_3408631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3408631).length < 2 ^ (prefixWord ++ tailWord_3408631).sum := by decide
  have hdescent : baseEnd_3408631 < baseStart_3408631 := by decide
  rcases family_descends (prefixWord ++ tailWord_3408631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3408651 : List Nat := [1, 1, 1, 1, 5, 1, 1, 2, 10]
def baseStart_3408651 : Nat := 118140960795 + 3408651 * 2 ^ 59
def prefixEnd_3408651 : Nat := 4983230072969 + 3 ^ 40 * 3408651 * 2
def baseEnd_3408651 : Nat := 194475149603205374554045

theorem tailTrace_3408651 : CollatzResearch.WordTrace tailWord_3408651 prefixEnd_3408651 194475149603205374554045 := by
  unfold tailWord_3408651
  simp only [CollatzResearch.WordTrace]
  refine ⟨124323715574047053088481807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82882477049364702058987871 124323715574047053088481807)
  ·
    refine ⟨186485573361070579632722711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124323715574047053088481807 186485573361070579632722711)
    ·
      refine ⟨279728360041605869449084067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186485573361070579632722711 279728360041605869449084067)
      ·
        refine ⟨419592540062408804173626101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 279728360041605869449084067 419592540062408804173626101)
        ·
          refine ⟨39336800630850825391277447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 419592540062408804173626101 39336800630850825391277447)
          ·
            refine ⟨59005200946276238086916171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39336800630850825391277447 59005200946276238086916171)
            ·
              refine ⟨88507801419414357130374257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59005200946276238086916171 88507801419414357130374257)
              ·
                refine ⟨66380851064560767847780693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 88507801419414357130374257 66380851064560767847780693)
                ·
                  refine ⟨194475149603205374554045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 66380851064560767847780693 194475149603205374554045)
                  ·
                    rfl

theorem cell23_3408651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 2, 10].length) (baseStart_3408651 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3408651 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3408651 prefixEnd_3408651 := by exact prefixLift 3408651
  have htrace : WordTrace (prefixWord ++ tailWord_3408651) baseStart_3408651 baseEnd_3408651 := by
    simpa [prefixWord, tailWord_3408651, baseEnd_3408651] using wordTrace_append hprefix tailTrace_3408651
  have hstable : (prefixWord ++ tailWord_3408651).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3408651).length < 2 ^ (prefixWord ++ tailWord_3408651).sum := by decide
  have hdescent : baseEnd_3408651 < baseStart_3408651 := by decide
  rcases family_descends (prefixWord ++ tailWord_3408651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3408672 : List Nat := [2, 1, 1, 5, 1, 2, 1, 5, 1, 4]
def baseStart_3408672 : Nat := 118140960795 + 3408672 * 2 ^ 59
def prefixEnd_3408672 : Nat := 4983230072969 + 3 ^ 40 * 3408672 * 2
def baseEnd_3408672 : Nat := 583429043174197596274603

theorem tailTrace_3408672 : CollatzResearch.WordTrace tailWord_3408672 prefixEnd_3408672 583429043174197596274603 := by
  unfold tailWord_3408672
  simp only [CollatzResearch.WordTrace]
  refine ⟨62162240753485486837498135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82882987671313982449997513 62162240753485486837498135)
  ·
    refine ⟨93243361130228230256247203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62162240753485486837498135 93243361130228230256247203)
    ·
      refine ⟨139865041695342345384370805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93243361130228230256247203 139865041695342345384370805)
      ·
        refine ⟨13112347658938344879784763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 139865041695342345384370805 13112347658938344879784763)
        ·
          refine ⟨19668521488407517319677145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13112347658938344879784763 19668521488407517319677145)
          ·
            refine ⟨14751391116305637989757859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19668521488407517319677145 14751391116305637989757859)
            ·
              refine ⟨22127086674458456984636789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14751391116305637989757859 22127086674458456984636789)
              ·
                refine ⟨2074414375730480342309699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 22127086674458456984636789 2074414375730480342309699)
                ·
                  refine ⟨3111621563595720513464549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2074414375730480342309699 3111621563595720513464549)
                  ·
                    refine ⟨583429043174197596274603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3111621563595720513464549 583429043174197596274603)
                    ·
                      rfl

theorem cell23_3408672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 1, 5, 1, 4].length) (baseStart_3408672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3408672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3408672 prefixEnd_3408672 := by exact prefixLift 3408672
  have htrace : WordTrace (prefixWord ++ tailWord_3408672) baseStart_3408672 baseEnd_3408672 := by
    simpa [prefixWord, tailWord_3408672, baseEnd_3408672] using wordTrace_append hprefix tailTrace_3408672
  have hstable : (prefixWord ++ tailWord_3408672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3408672).length < 2 ^ (prefixWord ++ tailWord_3408672).sum := by decide
  have hdescent : baseEnd_3408672 < baseStart_3408672 := by decide
  rcases family_descends (prefixWord ++ tailWord_3408672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3408718 : List Nat := [4, 1, 1, 1, 1, 1, 1, 2, 2, 5, 4]
def baseStart_3408718 : Nat := 118140960795 + 3408718 * 2 ^ 59
def prefixEnd_3408718 : Nat := 4983230072969 + 3 ^ 40 * 3408718 * 2
def baseEnd_3408718 : Nat := 1750310749632699608848597

theorem tailTrace_3408718 : CollatzResearch.WordTrace tailWord_3408718 prefixEnd_3408718 1750310749632699608848597 := by
  unfold tailWord_3408718
  simp only [CollatzResearch.WordTrace]
  refine ⟨15540769908100540441396351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 82884106176536215687447205 15540769908100540441396351)
  ·
    refine ⟨23311154862150810662094527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15540769908100540441396351 23311154862150810662094527)
    ·
      refine ⟨34966732293226215993141791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23311154862150810662094527 34966732293226215993141791)
      ·
        refine ⟨52450098439839323989712687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34966732293226215993141791 52450098439839323989712687)
        ·
          refine ⟨78675147659758985984569031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52450098439839323989712687 78675147659758985984569031)
          ·
            refine ⟨118012721489638478976853547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78675147659758985984569031 118012721489638478976853547)
            ·
              refine ⟨177019082234457718465280321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 118012721489638478976853547 177019082234457718465280321)
              ·
                refine ⟨132764311675843288848960241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 177019082234457718465280321 132764311675843288848960241)
                ·
                  refine ⟨99573233756882466636720181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 132764311675843288848960241 99573233756882466636720181)
                  ·
                    refine ⟨9334990664707731247192517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 99573233756882466636720181 9334990664707731247192517)
                    ·
                      refine ⟨1750310749632699608848597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9334990664707731247192517 1750310749632699608848597)
                      ·
                        rfl

theorem cell23_3408718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 2, 2, 5, 4].length) (baseStart_3408718 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3408718 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3408718 prefixEnd_3408718 := by exact prefixLift 3408718
  have htrace : WordTrace (prefixWord ++ tailWord_3408718) baseStart_3408718 baseEnd_3408718 := by
    simpa [prefixWord, tailWord_3408718, baseEnd_3408718] using wordTrace_append hprefix tailTrace_3408718
  have hstable : (prefixWord ++ tailWord_3408718).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3408718).length < 2 ^ (prefixWord ++ tailWord_3408718).sum := by decide
  have hdescent : baseEnd_3408718 < baseStart_3408718 := by decide
  rcases family_descends (prefixWord ++ tailWord_3408718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3408722 : List Nat := [3, 2, 2, 1, 1, 2, 2, 3, 2, 3, 2]
def baseStart_3408722 : Nat := 118140960795 + 3408722 * 2 ^ 59
def prefixEnd_3408722 : Nat := 4983230072969 + 3 ^ 40 * 3408722 * 2
def baseEnd_3408722 : Nat := 1750312803555317593198579

theorem tailTrace_3408722 : CollatzResearch.WordTrace tailWord_3408722 prefixEnd_3408722 1750312803555317593198579 := by
  unfold tailWord_3408722
  simp only [CollatzResearch.WordTrace]
  refine ⟨31081576289197458053579105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82884203437859888142877613 31081576289197458053579105)
  ·
    refine ⟨23311182216898093540184329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31081576289197458053579105 23311182216898093540184329)
    ·
      refine ⟨17483386662673570155138247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23311182216898093540184329 17483386662673570155138247)
      ·
        refine ⟨26225079994010355232707371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17483386662673570155138247 26225079994010355232707371)
        ·
          refine ⟨39337619991015532849061057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26225079994010355232707371 39337619991015532849061057)
          ·
            refine ⟨29503214993261649636795793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39337619991015532849061057 29503214993261649636795793)
            ·
              refine ⟨22127411244946237227596845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29503214993261649636795793 22127411244946237227596845)
              ·
                refine ⟨8297779216854838960348817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22127411244946237227596845 8297779216854838960348817)
                ·
                  refine ⟨6223334412641129220261613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8297779216854838960348817 6223334412641129220261613)
                  ·
                    refine ⟨2333750404740423457598105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6223334412641129220261613 2333750404740423457598105)
                    ·
                      refine ⟨1750312803555317593198579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2333750404740423457598105 1750312803555317593198579)
                      ·
                        rfl

theorem cell23_3408722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 2, 3, 2, 3, 2].length) (baseStart_3408722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3408722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3408722 prefixEnd_3408722 := by exact prefixLift 3408722
  have htrace : WordTrace (prefixWord ++ tailWord_3408722) baseStart_3408722 baseEnd_3408722 := by
    simpa [prefixWord, tailWord_3408722, baseEnd_3408722] using wordTrace_append hprefix tailTrace_3408722
  have hstable : (prefixWord ++ tailWord_3408722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3408722).length < 2 ^ (prefixWord ++ tailWord_3408722).sum := by decide
  have hdescent : baseEnd_3408722 < baseStart_3408722 := by decide
  rcases family_descends (prefixWord ++ tailWord_3408722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3408728 : List Nat := [2, 1, 2, 2, 1, 1, 1, 6, 1, 6]
def baseStart_3408728 : Nat := 118140960795 + 3408728 * 2 ^ 59
def prefixEnd_3408728 : Nat := 4983230072969 + 3 ^ 40 * 3408728 * 2
def baseEnd_3408728 : Nat := 583438628146414856574517

theorem tailTrace_3408728 : CollatzResearch.WordTrace tailWord_3408728 prefixEnd_3408728 583438628146414856574517 := by
  unfold tailWord_3408728
  simp only [CollatzResearch.WordTrace]
  refine ⟨62163261997384047619517419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82884349329845396826023225 62163261997384047619517419)
  ·
    refine ⟨93244892996076071429276129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62163261997384047619517419 93244892996076071429276129)
    ·
      refine ⟨69933669747057053571957097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93244892996076071429276129 69933669747057053571957097)
      ·
        refine ⟨52450252310292790178967823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69933669747057053571957097 52450252310292790178967823)
        ·
          refine ⟨78675378465439185268451735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52450252310292790178967823 78675378465439185268451735)
          ·
            refine ⟨118013067698158777902677603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78675378465439185268451735 118013067698158777902677603)
            ·
              refine ⟨177019601547238166854016405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 118013067698158777902677603 177019601547238166854016405)
              ·
                refine ⟨8297793822526789071282019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 177019601547238166854016405 8297793822526789071282019)
                ·
                  refine ⟨12446690733790183606923029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8297793822526789071282019 12446690733790183606923029)
                  ·
                    refine ⟨583438628146414856574517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12446690733790183606923029 583438628146414856574517)
                    ·
                      rfl

theorem cell23_3408728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 6, 1, 6].length) (baseStart_3408728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3408728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3408728 prefixEnd_3408728 := by exact prefixLift 3408728
  have htrace : WordTrace (prefixWord ++ tailWord_3408728) baseStart_3408728 baseEnd_3408728 := by
    simpa [prefixWord, tailWord_3408728, baseEnd_3408728] using wordTrace_append hprefix tailTrace_3408728
  have hstable : (prefixWord ++ tailWord_3408728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3408728).length < 2 ^ (prefixWord ++ tailWord_3408728).sum := by decide
  have hdescent : baseEnd_3408728 < baseStart_3408728 := by decide
  rcases family_descends (prefixWord ++ tailWord_3408728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3408729 : List Nat := [1, 2, 1, 2, 2, 4, 3, 3, 1, 1, 3]
def baseStart_3408729 : Nat := 118140960795 + 3408729 * 2 ^ 59
def prefixEnd_3408729 : Nat := 4983230072969 + 3 ^ 40 * 3408729 * 2
def baseEnd_3408729 : Nat := 1750316397919899065811047

theorem tailTrace_3408729 : CollatzResearch.WordTrace tailWord_3408729 prefixEnd_3408729 1750316397919899065811047 := by
  unfold tailWord_3408729
  simp only [CollatzResearch.WordTrace]
  refine ⟨124326560467764472409821241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82884373645176314939880827 124326560467764472409821241)
  ·
    refine ⟨93244920350823354307365931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124326560467764472409821241 93244920350823354307365931)
    ·
      refine ⟨139867380526235031461048897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93244920350823354307365931 139867380526235031461048897)
      ·
        refine ⟨104900535394676273595786673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 139867380526235031461048897 104900535394676273595786673)
        ·
          refine ⟨78675401546007205196840005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104900535394676273595786673 78675401546007205196840005)
          ·
            refine ⟨14751637789876350974407501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 78675401546007205196840005 14751637789876350974407501)
            ·
              refine ⟨5531864171203631615402813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14751637789876350974407501 5531864171203631615402813)
              ·
                refine ⟨2074449064201361855776055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5531864171203631615402813 2074449064201361855776055)
                ·
                  refine ⟨3111673596302042783664083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2074449064201361855776055 3111673596302042783664083)
                  ·
                    refine ⟨4667510394453064175496125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3111673596302042783664083 4667510394453064175496125)
                    ·
                      refine ⟨1750316397919899065811047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4667510394453064175496125 1750316397919899065811047)
                      ·
                        rfl

theorem cell23_3408729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 3, 3, 1, 1, 3].length) (baseStart_3408729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3408729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3408729 prefixEnd_3408729 := by exact prefixLift 3408729
  have htrace : WordTrace (prefixWord ++ tailWord_3408729) baseStart_3408729 baseEnd_3408729 := by
    simpa [prefixWord, tailWord_3408729, baseEnd_3408729] using wordTrace_append hprefix tailTrace_3408729
  have hstable : (prefixWord ++ tailWord_3408729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3408729).length < 2 ^ (prefixWord ++ tailWord_3408729).sum := by decide
  have hdescent : baseEnd_3408729 < baseStart_3408729 := by decide
  rcases family_descends (prefixWord ++ tailWord_3408729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3408732 : List Nat := [2, 2, 4, 2, 1, 1, 2, 3, 1, 5]
def baseStart_3408732 : Nat := 118140960795 + 3408732 * 2 ^ 59
def prefixEnd_3408732 : Nat := 4983230072969 + 3 ^ 40 * 3408732 * 2
def baseEnd_3408732 : Nat := 583439312787287518024511

theorem tailTrace_3408732 : CollatzResearch.WordTrace tailWord_3408732 prefixEnd_3408732 583439312787287518024511 := by
  unfold tailWord_3408732
  simp only [CollatzResearch.WordTrace]
  refine ⟨62163334943376801961090225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82884446591169069281453633 62163334943376801961090225)
  ·
    refine ⟨46622501207532601470817669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62163334943376801961090225 46622501207532601470817669)
    ·
      refine ⟨8741718976412362775778313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 46622501207532601470817669 8741718976412362775778313)
      ·
        refine ⟨6556289232309272081833735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8741718976412362775778313 6556289232309272081833735)
        ·
          refine ⟨9834433848463908122750603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6556289232309272081833735 9834433848463908122750603)
          ·
            refine ⟨14751650772695862184125905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9834433848463908122750603 14751650772695862184125905)
            ·
              refine ⟨11063738079521896638094429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14751650772695862184125905 11063738079521896638094429)
              ·
                refine ⟨4148901779820711239285411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11063738079521896638094429 4148901779820711239285411)
                ·
                  refine ⟨6223352669731066858928117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4148901779820711239285411 6223352669731066858928117)
                  ·
                    refine ⟨583439312787287518024511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6223352669731066858928117 583439312787287518024511)
                    ·
                      rfl

theorem cell23_3408732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 2, 3, 1, 5].length) (baseStart_3408732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3408732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3408732 prefixEnd_3408732 := by exact prefixLift 3408732
  have htrace : WordTrace (prefixWord ++ tailWord_3408732) baseStart_3408732 baseEnd_3408732 := by
    simpa [prefixWord, tailWord_3408732, baseEnd_3408732] using wordTrace_append hprefix tailTrace_3408732
  have hstable : (prefixWord ++ tailWord_3408732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3408732).length < 2 ^ (prefixWord ++ tailWord_3408732).sum := by decide
  have hdescent : baseEnd_3408732 < baseStart_3408732 := by decide
  rcases family_descends (prefixWord ++ tailWord_3408732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3408735 : List Nat := [1, 1, 2, 3, 1, 3, 1, 5, 1, 1, 4]
def baseStart_3408735 : Nat := 118140960795 + 3408735 * 2 ^ 59
def prefixEnd_3408735 : Nat := 4983230072969 + 3 ^ 40 * 3408735 * 2
def baseEnd_3408735 : Nat := 1750319478803826042336019

theorem tailTrace_3408735 : CollatzResearch.WordTrace tailWord_3408735 prefixEnd_3408735 1750319478803826042336019 := by
  unfold tailWord_3408735
  simp only [CollatzResearch.WordTrace]
  refine ⟨124326779305742735434539659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82884519537161823623026439 124326779305742735434539659)
  ·
    refine ⟨186490168958614103151809489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124326779305742735434539659 186490168958614103151809489)
    ·
      refine ⟨139867626718960577363857117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 186490168958614103151809489 139867626718960577363857117)
      ·
        refine ⟨52450360019610216511446419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 139867626718960577363857117 52450360019610216511446419)
        ·
          refine ⟨78675540029415324767169629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52450360019610216511446419 78675540029415324767169629)
          ·
            refine ⟨29503327511030746787688611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 78675540029415324767169629 29503327511030746787688611)
            ·
              refine ⟨44254991266546120181532917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29503327511030746787688611 44254991266546120181532917)
              ·
                refine ⟨4148905431238698767018711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 44254991266546120181532917 4148905431238698767018711)
                ·
                  refine ⟨6223358146858048150528067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4148905431238698767018711 6223358146858048150528067)
                  ·
                    refine ⟨9335037220287072225792101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6223358146858048150528067 9335037220287072225792101)
                    ·
                      refine ⟨1750319478803826042336019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9335037220287072225792101 1750319478803826042336019)
                      ·
                        rfl

theorem cell23_3408735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 5, 1, 1, 4].length) (baseStart_3408735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3408735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3408735 prefixEnd_3408735 := by exact prefixLift 3408735
  have htrace : WordTrace (prefixWord ++ tailWord_3408735) baseStart_3408735 baseEnd_3408735 := by
    simpa [prefixWord, tailWord_3408735, baseEnd_3408735] using wordTrace_append hprefix tailTrace_3408735
  have hstable : (prefixWord ++ tailWord_3408735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3408735).length < 2 ^ (prefixWord ++ tailWord_3408735).sum := by decide
  have hdescent : baseEnd_3408735 < baseStart_3408735 := by decide
  rcases family_descends (prefixWord ++ tailWord_3408735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3408748 : List Nat := [2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 6]
def baseStart_3408748 : Nat := 118140960795 + 3408748 * 2 ^ 59
def prefixEnd_3408748 : Nat := 4983230072969 + 3 ^ 40 * 3408748 * 2
def baseEnd_3408748 : Nat := 1750326154052334491473459

theorem tailTrace_3408748 : CollatzResearch.WordTrace tailWord_3408748 prefixEnd_3408748 1750326154052334491473459 := by
  unfold tailWord_3408748
  simp only [CollatzResearch.WordTrace]
  refine ⟨62163626727347819327381449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82884835636463759103175265 62163626727347819327381449)
  ·
    refine ⟨46622720045510864495536087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62163626727347819327381449 46622720045510864495536087)
    ·
      refine ⟨69934080068266296743304131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46622720045510864495536087 69934080068266296743304131)
      ·
        refine ⟨104901120102399445114956197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69934080068266296743304131 104901120102399445114956197)
        ·
          refine ⟨19668960019199895959054287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 104901120102399445114956197 19668960019199895959054287)
          ·
            refine ⟨29503440028799843938581431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19668960019199895959054287 29503440028799843938581431)
            ·
              refine ⟨44255160043199765907872147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29503440028799843938581431 44255160043199765907872147)
              ·
                refine ⟨66382740064799648861808221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44255160043199765907872147 66382740064799648861808221)
                ·
                  refine ⟨24893527524299868323178083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 66382740064799648861808221 24893527524299868323178083)
                  ·
                    refine ⟨37340291286449802484767125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24893527524299868323178083 37340291286449802484767125)
                    ·
                      refine ⟨1750326154052334491473459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 37340291286449802484767125 1750326154052334491473459)
                      ·
                        rfl

theorem cell23_3408748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 6].length) (baseStart_3408748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3408748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3408748 prefixEnd_3408748 := by exact prefixLift 3408748
  have htrace : WordTrace (prefixWord ++ tailWord_3408748) baseStart_3408748 baseEnd_3408748 := by
    simpa [prefixWord, tailWord_3408748, baseEnd_3408748] using wordTrace_append hprefix tailTrace_3408748
  have hstable : (prefixWord ++ tailWord_3408748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3408748).length < 2 ^ (prefixWord ++ tailWord_3408748).sum := by decide
  have hdescent : baseEnd_3408748 < baseStart_3408748 := by decide
  rcases family_descends (prefixWord ++ tailWord_3408748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3408766 : List Nat := [4, 2, 3, 1, 2, 2, 1, 2, 1, 5]
def baseStart_3408766 : Nat := 118140960795 + 3408766 * 2 ^ 59
def prefixEnd_3408766 : Nat := 4983230072969 + 3 ^ 40 * 3408766 * 2
def baseEnd_3408766 : Nat := 583445132234705140349459

theorem tailTrace_3408766 : CollatzResearch.WordTrace tailWord_3408766 prefixEnd_3408766 583445132234705140349459 := by
  unfold tailWord_3408766
  simp only [CollatzResearch.WordTrace]
  refine ⟨15540988746078803466114769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 82885273312420285152612101 15540988746078803466114769)
  ·
    refine ⟨11655741559559102599586077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15540988746078803466114769 11655741559559102599586077)
    ·
      refine ⟨4370903084834663474844779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11655741559559102599586077 4370903084834663474844779)
      ·
        refine ⟨6556354627251995212267169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4370903084834663474844779 6556354627251995212267169)
        ·
          refine ⟨4917265970438996409200377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6556354627251995212267169 4917265970438996409200377)
          ·
            refine ⟨3687949477829247306900283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4917265970438996409200377 3687949477829247306900283)
            ·
              refine ⟨5531924216743870960350425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3687949477829247306900283 5531924216743870960350425)
              ·
                refine ⟨4148943162557903220262819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5531924216743870960350425 4148943162557903220262819)
                ·
                  refine ⟨6223414743836854830394229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4148943162557903220262819 6223414743836854830394229)
                  ·
                    refine ⟨583445132234705140349459, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6223414743836854830394229 583445132234705140349459)
                    ·
                      rfl

theorem cell23_3408766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 2, 1, 2, 1, 5].length) (baseStart_3408766 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3408766 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3408766 prefixEnd_3408766 := by exact prefixLift 3408766
  have htrace : WordTrace (prefixWord ++ tailWord_3408766) baseStart_3408766 baseEnd_3408766 := by
    simpa [prefixWord, tailWord_3408766, baseEnd_3408766] using wordTrace_append hprefix tailTrace_3408766
  have hstable : (prefixWord ++ tailWord_3408766).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3408766).length < 2 ^ (prefixWord ++ tailWord_3408766).sum := by decide
  have hdescent : baseEnd_3408766 < baseStart_3408766 := by decide
  rcases family_descends (prefixWord ++ tailWord_3408766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3408786 : List Nat := [3, 2, 3, 2, 2, 1, 3, 1, 1, 1, 4]
def baseStart_3408786 : Nat := 118140960795 + 3408786 * 2 ^ 59
def prefixEnd_3408786 : Nat := 4983230072969 + 3 ^ 40 * 3408786 * 2
def baseEnd_3408786 : Nat := 1750345666317205342798285

theorem tailTrace_3408786 : CollatzResearch.WordTrace tailWord_3408786 prefixEnd_3408786 1750345666317205342798285 := by
  unfold tailWord_3408786
  simp only [CollatzResearch.WordTrace]
  refine ⟨31082159857139492786161553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82885759619038647429764141 31082159857139492786161553)
  ·
    refine ⟨23311619892854619589621165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31082159857139492786161553 23311619892854619589621165)
    ·
      refine ⟨8741857459820482346107937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23311619892854619589621165 8741857459820482346107937)
      ·
        refine ⟨6556393094865361759580953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8741857459820482346107937 6556393094865361759580953)
        ·
          refine ⟨4917294821149021319685715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6556393094865361759580953 4917294821149021319685715)
          ·
            refine ⟨7375942231723531979528573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4917294821149021319685715 7375942231723531979528573)
            ·
              refine ⟨2765978336896324492323215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7375942231723531979528573 2765978336896324492323215)
              ·
                refine ⟨4148967505344486738484823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2765978336896324492323215 4148967505344486738484823)
                ·
                  refine ⟨6223451258016730107727235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4148967505344486738484823 6223451258016730107727235)
                  ·
                    refine ⟨9335176887025095161590853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6223451258016730107727235 9335176887025095161590853)
                    ·
                      refine ⟨1750345666317205342798285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9335176887025095161590853 1750345666317205342798285)
                      ·
                        rfl

theorem cell23_3408786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 3, 1, 1, 1, 4].length) (baseStart_3408786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3408786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3408786 prefixEnd_3408786 := by exact prefixLift 3408786
  have htrace : WordTrace (prefixWord ++ tailWord_3408786) baseStart_3408786 baseEnd_3408786 := by
    simpa [prefixWord, tailWord_3408786, baseEnd_3408786] using wordTrace_append hprefix tailTrace_3408786
  have hstable : (prefixWord ++ tailWord_3408786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3408786).length < 2 ^ (prefixWord ++ tailWord_3408786).sum := by decide
  have hdescent : baseEnd_3408786 < baseStart_3408786 := by decide
  rcases family_descends (prefixWord ++ tailWord_3408786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3408789 : List Nat := [1, 3, 2, 1, 1, 5, 3, 1, 1, 2, 3]
def baseStart_3408789 : Nat := 118140960795 + 3408789 * 2 ^ 59
def prefixEnd_3408789 : Nat := 4983230072969 + 3 ^ 40 * 3408789 * 2
def baseEnd_3408789 : Nat := 1750347206759168831060771

theorem tailTrace_3408789 : CollatzResearch.WordTrace tailWord_3408789 prefixEnd_3408789 1750347206759168831060771 := by
  unfold tailWord_3408789
  simp only [CollatzResearch.WordTrace]
  refine ⟨124328748847547102657005421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82885832565031401771336947 124328748847547102657005421)
  ·
    refine ⟨46623280817830163496377033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 124328748847547102657005421 46623280817830163496377033)
    ·
      refine ⟨34967460613372622622282775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46623280817830163496377033 34967460613372622622282775)
      ·
        refine ⟨52451190920058933933424163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34967460613372622622282775 52451190920058933933424163)
        ·
          refine ⟨78676786380088400900136245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52451190920058933933424163 78676786380088400900136245)
          ·
            refine ⟨7375948723133287584387773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 78676786380088400900136245 7375948723133287584387773)
            ·
              refine ⟨2765980771174982844145415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7375948723133287584387773 2765980771174982844145415)
              ·
                refine ⟨4148971156762474266218123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2765980771174982844145415 4148971156762474266218123)
                ·
                  refine ⟨6223456735143711399327185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4148971156762474266218123 6223456735143711399327185)
                  ·
                    refine ⟨4667592551357783549495389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6223456735143711399327185 4667592551357783549495389)
                    ·
                      refine ⟨1750347206759168831060771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4667592551357783549495389 1750347206759168831060771)
                      ·
                        rfl

theorem cell23_3408789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 3, 1, 1, 2, 3].length) (baseStart_3408789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3408789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3408789 prefixEnd_3408789 := by exact prefixLift 3408789
  have htrace : WordTrace (prefixWord ++ tailWord_3408789) baseStart_3408789 baseEnd_3408789 := by
    simpa [prefixWord, tailWord_3408789, baseEnd_3408789] using wordTrace_append hprefix tailTrace_3408789
  have hstable : (prefixWord ++ tailWord_3408789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3408789).length < 2 ^ (prefixWord ++ tailWord_3408789).sum := by decide
  have hdescent : baseEnd_3408789 < baseStart_3408789 := by decide
  rcases family_descends (prefixWord ++ tailWord_3408789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3408846 : List Nat := [4, 1, 1, 1, 2, 3, 4, 1, 1, 3, 2]
def baseStart_3408846 : Nat := 118140960795 + 3408846 * 2 ^ 59
def prefixEnd_3408846 : Nat := 4983230072969 + 3 ^ 40 * 3408846 * 2
def baseEnd_3408846 : Nat := 1750376475156475108048009

theorem tailTrace_3408846 : CollatzResearch.WordTrace tailWord_3408846 prefixEnd_3408846 1750376475156475108048009 := by
  unfold tailWord_3408846
  simp only [CollatzResearch.WordTrace]
  refine ⟨15541353476042575173978799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 82887218538893734261220261 15541353476042575173978799)
  ·
    refine ⟨23312030214063862760968199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15541353476042575173978799 23312030214063862760968199)
    ·
      refine ⟨34968045321095794141452299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23312030214063862760968199 34968045321095794141452299)
      ·
        refine ⟨52452067981643691212178449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34968045321095794141452299 52452067981643691212178449)
        ·
          refine ⟨39339050986232768409133837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52452067981643691212178449 39339050986232768409133837)
          ·
            refine ⟨14752144119837288153425189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39339050986232768409133837 14752144119837288153425189)
            ·
              refine ⟨2766027022469491528767223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14752144119837288153425189 2766027022469491528767223)
              ·
                refine ⟨4149040533704237293150835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2766027022469491528767223 4149040533704237293150835)
                ·
                  refine ⟨6223560800556355939726253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4149040533704237293150835 6223560800556355939726253)
                  ·
                    refine ⟨2333835300208633477397345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6223560800556355939726253 2333835300208633477397345)
                    ·
                      refine ⟨1750376475156475108048009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2333835300208633477397345 1750376475156475108048009)
                      ·
                        rfl

theorem cell23_3408846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 4, 1, 1, 3, 2].length) (baseStart_3408846 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3408846 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3408846 prefixEnd_3408846 := by exact prefixLift 3408846
  have htrace : WordTrace (prefixWord ++ tailWord_3408846) baseStart_3408846 baseEnd_3408846 := by
    simpa [prefixWord, tailWord_3408846, baseEnd_3408846] using wordTrace_append hprefix tailTrace_3408846
  have hstable : (prefixWord ++ tailWord_3408846).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3408846).length < 2 ^ (prefixWord ++ tailWord_3408846).sum := by decide
  have hdescent : baseEnd_3408846 < baseStart_3408846 := by decide
  rcases family_descends (prefixWord ++ tailWord_3408846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3408848 : List Nat := [2, 1, 1, 1, 1, 2, 3, 1, 11]
def baseStart_3408848 : Nat := 118140960795 + 3408848 * 2 ^ 59
def prefixEnd_3408848 : Nat := 4983230072969 + 3 ^ 40 * 3408848 * 2
def baseEnd_3408848 : Nat := 194486389124198233358111

theorem tailTrace_3408848 : CollatzResearch.WordTrace tailWord_3408848 prefixEnd_3408848 194486389124198233358111 := by
  unfold tailWord_3408848
  simp only [CollatzResearch.WordTrace]
  refine ⟨62165450377166677866701599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82887267169555570488935465 62165450377166677866701599)
  ·
    refine ⟨93248175565750016800052399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62165450377166677866701599 93248175565750016800052399)
    ·
      refine ⟨139872263348625025200078599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93248175565750016800052399 139872263348625025200078599)
      ·
        refine ⟨209808395022937537800117899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139872263348625025200078599 209808395022937537800117899)
        ·
          refine ⟨314712592534406306700176849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 209808395022937537800117899 314712592534406306700176849)
          ·
            refine ⟨236034444400804730025132637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 314712592534406306700176849 236034444400804730025132637)
            ·
              refine ⟨88512916650301773759424739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 236034444400804730025132637 88512916650301773759424739)
              ·
                refine ⟨132769374975452660639137109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 88512916650301773759424739 132769374975452660639137109)
                ·
                  refine ⟨194486389124198233358111, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 132769374975452660639137109 194486389124198233358111)
                  ·
                    rfl

theorem cell23_3408848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 1, 11].length) (baseStart_3408848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3408848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3408848 prefixEnd_3408848 := by exact prefixLift 3408848
  have htrace : WordTrace (prefixWord ++ tailWord_3408848) baseStart_3408848 baseEnd_3408848 := by
    simpa [prefixWord, tailWord_3408848, baseEnd_3408848] using wordTrace_append hprefix tailTrace_3408848
  have hstable : (prefixWord ++ tailWord_3408848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3408848).length < 2 ^ (prefixWord ++ tailWord_3408848).sum := by decide
  have hdescent : baseEnd_3408848 < baseStart_3408848 := by decide
  rcases family_descends (prefixWord ++ tailWord_3408848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3408853 : List Nat := [1, 3, 2, 3, 4, 1, 1, 2, 2, 1, 3]
def baseStart_3408853 : Nat := 118140960795 + 3408853 * 2 ^ 59
def prefixEnd_3408853 : Nat := 4983230072969 + 3 ^ 40 * 3408853 * 2
def baseEnd_3408853 : Nat := 1750380069521056580660477

theorem tailTrace_3408853 : CollatzResearch.WordTrace tailWord_3408853 prefixEnd_3408853 1750380069521056580660477 := by
  unfold tailWord_3408853
  simp only [CollatzResearch.WordTrace]
  refine ⟨124331083119315241587335213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82887388746210161058223475 124331083119315241587335213)
  ·
    refine ⟨46624156169743215595250705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 124331083119315241587335213 46624156169743215595250705)
    ·
      refine ⟨34968117127307411696438029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46624156169743215595250705 34968117127307411696438029)
      ·
        refine ⟨13113043922740279386164261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34968117127307411696438029 13113043922740279386164261)
        ·
          refine ⟨2458695735513802384905799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13113043922740279386164261 2458695735513802384905799)
          ·
            refine ⟨3688043603270703577358699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2458695735513802384905799 3688043603270703577358699)
            ·
              refine ⟨5532065404906055366038049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3688043603270703577358699 5532065404906055366038049)
              ·
                refine ⟨4149049053679541524528537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5532065404906055366038049 4149049053679541524528537)
                ·
                  refine ⟨3111786790259656143396403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4149049053679541524528537 3111786790259656143396403)
                  ·
                    refine ⟨4667680185389484215094605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3111786790259656143396403 4667680185389484215094605)
                    ·
                      refine ⟨1750380069521056580660477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4667680185389484215094605 1750380069521056580660477)
                      ·
                        rfl

theorem cell23_3408853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 4, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 4, 1, 1, 2, 2, 1, 3].length) (baseStart_3408853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3408853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3408853 prefixEnd_3408853 := by exact prefixLift 3408853
  have htrace : WordTrace (prefixWord ++ tailWord_3408853) baseStart_3408853 baseEnd_3408853 := by
    simpa [prefixWord, tailWord_3408853, baseEnd_3408853] using wordTrace_append hprefix tailTrace_3408853
  have hstable : (prefixWord ++ tailWord_3408853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3408853).length < 2 ^ (prefixWord ++ tailWord_3408853).sum := by decide
  have hdescent : baseEnd_3408853 < baseStart_3408853 := by decide
  rcases family_descends (prefixWord ++ tailWord_3408853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3408959 : List Nat := [1, 1, 2, 2, 3, 1, 1, 7, 1, 4]
def baseStart_3408959 : Nat := 118140960795 + 3408959 * 2 ^ 59
def prefixEnd_3408959 : Nat := 4983230072969 + 3 ^ 40 * 3408959 * 2
def baseEnd_3408959 : Nat := 583478166156811055311663

theorem tailTrace_3408959 : CollatzResearch.WordTrace tailWord_3408959 prefixEnd_3408959 583478166156811055311663 := by
  unfold tailWord_3408959
  simp only [CollatzResearch.WordTrace]
  refine ⟨124334949256931221690693931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82889966171287481127129287 124334949256931221690693931)
  ·
    refine ⟨186502423885396832536040897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124334949256931221690693931 186502423885396832536040897)
    ·
      refine ⟨139876817914047624402030673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 186502423885396832536040897 139876817914047624402030673)
      ·
        refine ⟨104907613435535718301523005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 139876817914047624402030673 104907613435535718301523005)
        ·
          refine ⟨39340355038325894363071127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 104907613435535718301523005 39340355038325894363071127)
          ·
            refine ⟨59010532557488841544606691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39340355038325894363071127 59010532557488841544606691)
            ·
              refine ⟨88515798836233262316910037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59010532557488841544606691 88515798836233262316910037)
              ·
                refine ⟨2074589035224217085552579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 88515798836233262316910037 2074589035224217085552579)
                ·
                  refine ⟨3111883552836325628328869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2074589035224217085552579 3111883552836325628328869)
                  ·
                    refine ⟨583478166156811055311663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3111883552836325628328869 583478166156811055311663)
                    ·
                      rfl

theorem cell23_3408959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 7, 1, 4].length) (baseStart_3408959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3408959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3408959 prefixEnd_3408959 := by exact prefixLift 3408959
  have htrace : WordTrace (prefixWord ++ tailWord_3408959) baseStart_3408959 baseEnd_3408959 := by
    simpa [prefixWord, tailWord_3408959, baseEnd_3408959] using wordTrace_append hprefix tailTrace_3408959
  have hstable : (prefixWord ++ tailWord_3408959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3408959).length < 2 ^ (prefixWord ++ tailWord_3408959).sum := by decide
  have hdescent : baseEnd_3408959 < baseStart_3408959 := by decide
  rcases family_descends (prefixWord ++ tailWord_3408959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3408966 : List Nat := [6, 1, 1, 1, 1, 2, 2, 2, 2, 1, 4]
def baseStart_3408966 : Nat := 118140960795 + 3408966 * 2 ^ 59
def prefixEnd_3408966 : Nat := 4983230072969 + 3 ^ 40 * 3408966 * 2
def baseEnd_3408966 : Nat := 1750438092835014638547457

theorem tailTrace_3408966 : CollatzResearch.WordTrace tailWord_3408966 prefixEnd_3408966 1750438092835014638547457 := by
  unfold tailWord_3408966
  simp only [CollatzResearch.WordTrace]
  refine ⟨3885475142747058183943711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 82890136378603907924132501 3885475142747058183943711)
  ·
    refine ⟨5828212714120587275915567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3885475142747058183943711 5828212714120587275915567)
    ·
      refine ⟨8742319071180880913873351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5828212714120587275915567 8742319071180880913873351)
      ·
        refine ⟨13113478606771321370810027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8742319071180880913873351 13113478606771321370810027)
        ·
          refine ⟨19670217910156982056215041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13113478606771321370810027 19670217910156982056215041)
          ·
            refine ⟨14752663432617736542161281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19670217910156982056215041 14752663432617736542161281)
            ·
              refine ⟨11064497574463302406620961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14752663432617736542161281 11064497574463302406620961)
              ·
                refine ⟨8298373180847476804965721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11064497574463302406620961 8298373180847476804965721)
                ·
                  refine ⟨6223779885635607603724291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8298373180847476804965721 6223779885635607603724291)
                  ·
                    refine ⟨9335669828453411405586437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6223779885635607603724291 9335669828453411405586437)
                    ·
                      refine ⟨1750438092835014638547457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9335669828453411405586437 1750438092835014638547457)
                      ·
                        rfl

theorem cell23_3408966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 2, 2, 2, 1, 4].length) (baseStart_3408966 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3408966 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3408966 prefixEnd_3408966 := by exact prefixLift 3408966
  have htrace : WordTrace (prefixWord ++ tailWord_3408966) baseStart_3408966 baseEnd_3408966 := by
    simpa [prefixWord, tailWord_3408966, baseEnd_3408966] using wordTrace_append hprefix tailTrace_3408966
  have hstable : (prefixWord ++ tailWord_3408966).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3408966).length < 2 ^ (prefixWord ++ tailWord_3408966).sum := by decide
  have hdescent : baseEnd_3408966 < baseStart_3408966 := by decide
  rcases family_descends (prefixWord ++ tailWord_3408966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3408995 : List Nat := [1, 1, 1, 5, 1, 1, 1, 1, 1, 3, 7]
def baseStart_3408995 : Nat := 118140960795 + 3408995 * 2 ^ 59
def prefixEnd_3408995 : Nat := 4983230072969 + 3 ^ 40 * 3408995 * 2
def baseEnd_3408995 : Nat := 1750452983773995025084823

theorem tailTrace_3408995 : CollatzResearch.WordTrace tailWord_3408995 prefixEnd_3408995 1750452983773995025084823 := by
  unfold tailWord_3408995
  simp only [CollatzResearch.WordTrace]
  refine ⟨124336262284800799839004439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82890841523200533226002959 124336262284800799839004439)
  ·
    refine ⟨186504393427201199758506659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124336262284800799839004439 186504393427201199758506659)
    ·
      refine ⟨279756590140801799637759989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186504393427201199758506659 279756590140801799637759989)
      ·
        refine ⟨26227180325700168716039999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 279756590140801799637759989 26227180325700168716039999)
        ·
          refine ⟨39340770488550253074059999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26227180325700168716039999 39340770488550253074059999)
          ·
            refine ⟨59011155732825379611089999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39340770488550253074059999 59011155732825379611089999)
            ·
              refine ⟨88516733599238069416634999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59011155732825379611089999 88516733599238069416634999)
              ·
                refine ⟨132775100398857104124952499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 88516733599238069416634999 132775100398857104124952499)
                ·
                  refine ⟨199162650598285656187428749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 132775100398857104124952499 199162650598285656187428749)
                  ·
                    refine ⟨74685993974357121070285781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 199162650598285656187428749 74685993974357121070285781)
                    ·
                      refine ⟨1750452983773995025084823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 74685993974357121070285781 1750452983773995025084823)
                      ·
                        rfl

theorem cell23_3408995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 1, 1, 3, 7].length) (baseStart_3408995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3408995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3408995 prefixEnd_3408995 := by exact prefixLift 3408995
  have htrace : WordTrace (prefixWord ++ tailWord_3408995) baseStart_3408995 baseEnd_3408995 := by
    simpa [prefixWord, tailWord_3408995, baseEnd_3408995] using wordTrace_append hprefix tailTrace_3408995
  have hstable : (prefixWord ++ tailWord_3408995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3408995).length < 2 ^ (prefixWord ++ tailWord_3408995).sum := by decide
  have hdescent : baseEnd_3408995 < baseStart_3408995 := by decide
  rcases family_descends (prefixWord ++ tailWord_3408995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3408999 : List Nat := [1, 1, 5, 1, 1, 3, 1, 1, 5, 1, 3]
def baseStart_3408999 : Nat := 118140960795 + 3408999 * 2 ^ 59
def prefixEnd_3408999 : Nat := 4983230072969 + 3 ^ 40 * 3408999 * 2
def baseEnd_3408999 : Nat := 1750455037696613009434805

theorem tailTrace_3408999 : CollatzResearch.WordTrace tailWord_3408999 prefixEnd_3408999 1750455037696613009434805 := by
  unfold tailWord_3408999
  simp only [CollatzResearch.WordTrace]
  refine ⟨124336408176786308522150051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82890938784524205681433367 124336408176786308522150051)
  ·
    refine ⟨186504612265179462783225077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124336408176786308522150051 186504612265179462783225077)
    ·
      refine ⟨17484807399860574635927351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 186504612265179462783225077 17484807399860574635927351)
      ·
        refine ⟨26227211099790861953891027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17484807399860574635927351 26227211099790861953891027)
        ·
          refine ⟨39340816649686292930836541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26227211099790861953891027 39340816649686292930836541)
          ·
            refine ⟨14752806243632359849063703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39340816649686292930836541 14752806243632359849063703)
            ·
              refine ⟨22129209365448539773595555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14752806243632359849063703 22129209365448539773595555)
              ·
                refine ⟨33193814048172809660393333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22129209365448539773595555 33193814048172809660393333)
                ·
                  refine ⟨3111920067016200905661875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 33193814048172809660393333 3111920067016200905661875)
                  ·
                    refine ⟨4667880100524301358492813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3111920067016200905661875 4667880100524301358492813)
                    ·
                      refine ⟨1750455037696613009434805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4667880100524301358492813 1750455037696613009434805)
                      ·
                        rfl

theorem cell23_3408999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 1, 1, 5, 1, 3].length) (baseStart_3408999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3408999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3408999 prefixEnd_3408999 := by exact prefixLift 3408999
  have htrace : WordTrace (prefixWord ++ tailWord_3408999) baseStart_3408999 baseEnd_3408999 := by
    simpa [prefixWord, tailWord_3408999, baseEnd_3408999] using wordTrace_append hprefix tailTrace_3408999
  have hstable : (prefixWord ++ tailWord_3408999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3408999).length < 2 ^ (prefixWord ++ tailWord_3408999).sum := by decide
  have hdescent : baseEnd_3408999 < baseStart_3408999 := by decide
  rcases family_descends (prefixWord ++ tailWord_3408999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3409009 : List Nat := [1, 2, 2, 2, 1, 1, 2, 5, 2, 3, 2]
def baseStart_3409009 : Nat := 118140960795 + 3409009 * 2 ^ 59
def prefixEnd_3409009 : Nat := 4983230072969 + 3 ^ 40 * 3409009 * 2
def baseEnd_3409009 : Nat := 1750460172503157970309759

theorem tailTrace_3409009 : CollatzResearch.WordTrace tailWord_3409009 prefixEnd_3409009 1750460172503157970309759 := by
  unfold tailWord_3409009
  simp only [CollatzResearch.WordTrace]
  refine ⟨124336772906750080230014081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82891181937833386820009387 124336772906750080230014081)
  ·
    refine ⟨93252579680062560172510561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124336772906750080230014081 93252579680062560172510561)
    ·
      refine ⟨69939434760046920129382921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93252579680062560172510561 69939434760046920129382921)
      ·
        refine ⟨52454576070035190097037191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69939434760046920129382921 52454576070035190097037191)
        ·
          refine ⟨78681864105052785145555787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52454576070035190097037191 78681864105052785145555787)
          ·
            refine ⟨118022796157579177718333681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78681864105052785145555787 118022796157579177718333681)
            ·
              refine ⟨88517097118184383288750261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 118022796157579177718333681 88517097118184383288750261)
              ·
                refine ⟨8298477854829785933320337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 88517097118184383288750261 8298477854829785933320337)
                ·
                  refine ⟨6223858391122339449990253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8298477854829785933320337 6223858391122339449990253)
                  ·
                    refine ⟨2333946896670877293746345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6223858391122339449990253 2333946896670877293746345)
                    ·
                      refine ⟨1750460172503157970309759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2333946896670877293746345 1750460172503157970309759)
                      ·
                        rfl

theorem cell23_3409009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 5, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 5, 2, 3, 2].length) (baseStart_3409009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3409009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3409009 prefixEnd_3409009 := by exact prefixLift 3409009
  have htrace : WordTrace (prefixWord ++ tailWord_3409009) baseStart_3409009 baseEnd_3409009 := by
    simpa [prefixWord, tailWord_3409009, baseEnd_3409009] using wordTrace_append hprefix tailTrace_3409009
  have hstable : (prefixWord ++ tailWord_3409009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3409009).length < 2 ^ (prefixWord ++ tailWord_3409009).sum := by decide
  have hdescent : baseEnd_3409009 < baseStart_3409009 := by decide
  rcases family_descends (prefixWord ++ tailWord_3409009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3409016 : List Nat := [2, 1, 2, 1, 1, 1, 5, 5, 1, 1, 3]
def baseStart_3409016 : Nat := 118140960795 + 3409016 * 2 ^ 59
def prefixEnd_3409016 : Nat := 4983230072969 + 3 ^ 40 * 3409016 * 2
def baseEnd_3409016 : Nat := 1750463766867739442922227

theorem tailTrace_3409016 : CollatzResearch.WordTrace tailWord_3409016 prefixEnd_3409016 1750463766867739442922227 := by
  unfold tailWord_3409016
  simp only [CollatzResearch.WordTrace]
  refine ⟨62168514108862360212759451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82891352145149813617012601 62168514108862360212759451)
  ·
    refine ⟨93252771163293540319139177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62168514108862360212759451 93252771163293540319139177)
    ·
      refine ⟨69939578372470155239354383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93252771163293540319139177 69939578372470155239354383)
      ·
        refine ⟨104909367558705232859031575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69939578372470155239354383 104909367558705232859031575)
        ·
          refine ⟨157364051338057849288547363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104909367558705232859031575 157364051338057849288547363)
          ·
            refine ⟨236046077007086773932821045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 157364051338057849288547363 236046077007086773932821045)
            ·
              refine ⟨22129319719414385056201973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 236046077007086773932821045 22129319719414385056201973)
              ·
                refine ⟨2074623723695098599018935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 22129319719414385056201973 2074623723695098599018935)
                ·
                  refine ⟨3111935585542647898528403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2074623723695098599018935 3111935585542647898528403)
                  ·
                    refine ⟨4667903378313971847792605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3111935585542647898528403 4667903378313971847792605)
                    ·
                      refine ⟨1750463766867739442922227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4667903378313971847792605 1750463766867739442922227)
                      ·
                        rfl

theorem cell23_3409016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 5, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 5, 5, 1, 1, 3].length) (baseStart_3409016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3409016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3409016 prefixEnd_3409016 := by exact prefixLift 3409016
  have htrace : WordTrace (prefixWord ++ tailWord_3409016) baseStart_3409016 baseEnd_3409016 := by
    simpa [prefixWord, tailWord_3409016, baseEnd_3409016] using wordTrace_append hprefix tailTrace_3409016
  have hstable : (prefixWord ++ tailWord_3409016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3409016).length < 2 ^ (prefixWord ++ tailWord_3409016).sum := by decide
  have hdescent : baseEnd_3409016 < baseStart_3409016 := by decide
  rcases family_descends (prefixWord ++ tailWord_3409016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3409056 : List Nat := [2, 1, 1, 4, 2, 1, 1, 4, 3, 2, 2]
def baseStart_3409056 : Nat := 118140960795 + 3409056 * 2 ^ 59
def prefixEnd_3409056 : Nat := 4983230072969 + 3 ^ 40 * 3409056 * 2
def baseEnd_3409056 : Nat := 1750484306093919286422043

theorem tailTrace_3409056 : CollatzResearch.WordTrace tailWord_3409056 prefixEnd_3409056 1750484306093919286422043 := by
  unfold tailWord_3409056
  simp only [CollatzResearch.WordTrace]
  refine ⟨62169243568789903628487511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82892324758386538171316681 62169243568789903628487511)
  ·
    refine ⟨93253865353184855442731267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62169243568789903628487511 93253865353184855442731267)
    ·
      refine ⟨139880798029777283164096901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93253865353184855442731267 139880798029777283164096901)
      ·
        refine ⟨26227649630583240593268169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 139880798029777283164096901 26227649630583240593268169)
        ·
          refine ⟨19670737222937430444951127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26227649630583240593268169 19670737222937430444951127)
          ·
            refine ⟨29506105834406145667426691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19670737222937430444951127 29506105834406145667426691)
            ·
              refine ⟨44259158751609218501140037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29506105834406145667426691 44259158751609218501140037)
              ·
                refine ⟨8298592265926728468963757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 44259158751609218501140037 8298592265926728468963757)
                ·
                  refine ⟨3111972099722523175861409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8298592265926728468963757 3111972099722523175861409)
                  ·
                    refine ⟨2333979074791892381896057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3111972099722523175861409 2333979074791892381896057)
                    ·
                      refine ⟨1750484306093919286422043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2333979074791892381896057 1750484306093919286422043)
                      ·
                        rfl

theorem cell23_3409056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 4, 3, 2, 2].length) (baseStart_3409056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3409056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3409056 prefixEnd_3409056 := by exact prefixLift 3409056
  have htrace : WordTrace (prefixWord ++ tailWord_3409056) baseStart_3409056 baseEnd_3409056 := by
    simpa [prefixWord, tailWord_3409056, baseEnd_3409056] using wordTrace_append hprefix tailTrace_3409056
  have hstable : (prefixWord ++ tailWord_3409056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3409056).length < 2 ^ (prefixWord ++ tailWord_3409056).sum := by decide
  have hdescent : baseEnd_3409056 < baseStart_3409056 := by decide
  rcases family_descends (prefixWord ++ tailWord_3409056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3409066 : List Nat := [3, 1, 5, 1, 1, 1, 1, 2, 4, 4]
def baseStart_3409066 : Nat := 118140960795 + 3409066 * 2 ^ 59
def prefixEnd_3409066 : Nat := 4983230072969 + 3 ^ 40 * 3409066 * 2
def baseEnd_3409066 : Nat := 583496480300154749098999

theorem tailTrace_3409066 : CollatzResearch.WordTrace tailWord_3409066 prefixEnd_3409066 583496480300154749098999 := by
  unfold tailWord_3409066
  simp only [CollatzResearch.WordTrace]
  refine ⟨31084712966885894741209763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82892567911695719309892701 31084712966885894741209763)
  ·
    refine ⟨46627069450328842111814645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31084712966885894741209763 46627069450328842111814645)
    ·
      refine ⟨4371287760968328947982623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 46627069450328842111814645 4371287760968328947982623)
      ·
        refine ⟨6556931641452493421973935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4371287760968328947982623 6556931641452493421973935)
        ·
          refine ⟨9835397462178740132960903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6556931641452493421973935 9835397462178740132960903)
          ·
            refine ⟨14753096193268110199441355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9835397462178740132960903 14753096193268110199441355)
            ·
              refine ⟨22129644289902165299162033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14753096193268110199441355 22129644289902165299162033)
              ·
                refine ⟨16597233217426623974371525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22129644289902165299162033 16597233217426623974371525)
                ·
                  refine ⟨3111981228267491995194661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16597233217426623974371525 3111981228267491995194661)
                  ·
                    refine ⟨583496480300154749098999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3111981228267491995194661 583496480300154749098999)
                    ·
                      rfl

theorem cell23_3409066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 1, 2, 4, 4].length) (baseStart_3409066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3409066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3409066 prefixEnd_3409066 := by exact prefixLift 3409066
  have htrace : WordTrace (prefixWord ++ tailWord_3409066) baseStart_3409066 baseEnd_3409066 := by
    simpa [prefixWord, tailWord_3409066, baseEnd_3409066] using wordTrace_append hprefix tailTrace_3409066
  have hstable : (prefixWord ++ tailWord_3409066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3409066).length < 2 ^ (prefixWord ++ tailWord_3409066).sum := by decide
  have hdescent : baseEnd_3409066 < baseStart_3409066 := by decide
  rcases family_descends (prefixWord ++ tailWord_3409066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3409152 : List Nat := [2, 1, 1, 2, 1, 1, 3, 5, 7]
def baseStart_3409152 : Nat := 118140960795 + 3409152 * 2 ^ 59
def prefixEnd_3409152 : Nat := 4983230072969 + 3 ^ 40 * 3409152 * 2
def baseEnd_3409152 : Nat := 194503733359638990091289

theorem tailTrace_3409152 : CollatzResearch.WordTrace tailWord_3409152 prefixEnd_3409152 194503733359638990091289 := by
  unfold tailWord_3409152
  simp only [CollatzResearch.WordTrace]
  refine ⟨62170994272616007826234855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82894659030154677101646473 62170994272616007826234855)
  ·
    refine ⟨93256491408924011739352283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62170994272616007826234855 93256491408924011739352283)
    ·
      refine ⟨139884737113386017609028425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93256491408924011739352283 139884737113386017609028425)
      ·
        refine ⟨104913552835039513206771319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 139884737113386017609028425 104913552835039513206771319)
        ·
          refine ⟨157370329252559269810156979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104913552835039513206771319 157370329252559269810156979)
          ·
            refine ⟨236055493878838904715235469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 157370329252559269810156979 236055493878838904715235469)
            ·
              refine ⟨88520810204564589268213301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 236055493878838904715235469 88520810204564589268213301)
              ·
                refine ⟨8298825956677930243894997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 88520810204564589268213301 8298825956677930243894997)
                ·
                  refine ⟨194503733359638990091289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8298825956677930243894997 194503733359638990091289)
                  ·
                    rfl

theorem cell23_3409152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 5, 7].length) (baseStart_3409152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3409152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3409152 prefixEnd_3409152 := by exact prefixLift 3409152
  have htrace : WordTrace (prefixWord ++ tailWord_3409152) baseStart_3409152 baseEnd_3409152 := by
    simpa [prefixWord, tailWord_3409152, baseEnd_3409152] using wordTrace_append hprefix tailTrace_3409152
  have hstable : (prefixWord ++ tailWord_3409152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3409152).length < 2 ^ (prefixWord ++ tailWord_3409152).sum := by decide
  have hdescent : baseEnd_3409152 < baseStart_3409152 := by decide
  rcases family_descends (prefixWord ++ tailWord_3409152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3409163 : List Nat := [1, 1, 1, 1, 5, 3, 2, 3, 2, 2, 2]
def baseStart_3409163 : Nat := 118140960795 + 3409163 * 2 ^ 59
def prefixEnd_3409163 : Nat := 4983230072969 + 3 ^ 40 * 3409163 * 2
def baseEnd_3409163 : Nat := 1750539248523950367784051

theorem tailTrace_3409163 : CollatzResearch.WordTrace tailWord_3409163 prefixEnd_3409163 1750539248523950367784051 := by
  unfold tailWord_3409163
  simp only [CollatzResearch.WordTrace]
  refine ⟨124342389748192164531120143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82894926498794776354080095 124342389748192164531120143)
  ·
    refine ⟨186513584622288246796680215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124342389748192164531120143 186513584622288246796680215)
    ·
      refine ⟨279770376933432370195020323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186513584622288246796680215 279770376933432370195020323)
      ·
        refine ⟨419655565400148555292530485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 279770376933432370195020323 419655565400148555292530485)
        ·
          refine ⟨39342709256263927058674733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 419655565400148555292530485 39342709256263927058674733)
          ·
            refine ⟨14753515971098972647003025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39342709256263927058674733 14753515971098972647003025)
            ·
              refine ⟨11065136978324229485252269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14753515971098972647003025 11065136978324229485252269)
              ·
                refine ⟨4149426366871586056969601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11065136978324229485252269 4149426366871586056969601)
                ·
                  refine ⟨3112069775153689542727201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4149426366871586056969601 3112069775153689542727201)
                  ·
                    refine ⟨2334052331365267157045401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3112069775153689542727201 2334052331365267157045401)
                    ·
                      refine ⟨1750539248523950367784051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2334052331365267157045401 1750539248523950367784051)
                      ·
                        rfl

theorem cell23_3409163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 2, 3, 2, 2, 2].length) (baseStart_3409163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3409163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3409163 prefixEnd_3409163 := by exact prefixLift 3409163
  have htrace : WordTrace (prefixWord ++ tailWord_3409163) baseStart_3409163 baseEnd_3409163 := by
    simpa [prefixWord, tailWord_3409163, baseEnd_3409163] using wordTrace_append hprefix tailTrace_3409163
  have hstable : (prefixWord ++ tailWord_3409163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3409163).length < 2 ^ (prefixWord ++ tailWord_3409163).sum := by decide
  have hdescent : baseEnd_3409163 < baseStart_3409163 := by decide
  rcases family_descends (prefixWord ++ tailWord_3409163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3409197 : List Nat := [1, 5, 3, 1, 1, 1, 3, 2, 2, 2, 2]
def baseStart_3409197 : Nat := 118140960795 + 3409197 * 2 ^ 59
def prefixEnd_3409197 : Nat := 4983230072969 + 3 ^ 40 * 3409197 * 2
def baseEnd_3409197 : Nat := 1750556706866203234758895

theorem tailTrace_3409197 : CollatzResearch.WordTrace tailWord_3409197 prefixEnd_3409197 1750556706866203234758895 := by
  unfold tailWord_3409197
  simp only [CollatzResearch.WordTrace]
  refine ⟨124343629830068988337857845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82895753220045992225238563 124343629830068988337857845)
  ·
    refine ⟨11657215296568967656674173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 124343629830068988337857845 11657215296568967656674173)
    ·
      refine ⟨4371455736213362871252815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11657215296568967656674173 4371455736213362871252815)
      ·
        refine ⟨6557183604320044306879223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4371455736213362871252815 6557183604320044306879223)
        ·
          refine ⟨9835775406480066460318835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6557183604320044306879223 9835775406480066460318835)
          ·
            refine ⟨14753663109720099690478253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9835775406480066460318835 14753663109720099690478253)
            ·
              refine ⟨5532623666145037383929345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14753663109720099690478253 5532623666145037383929345)
              ·
                refine ⟨4149467749608778037947009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5532623666145037383929345 4149467749608778037947009)
                ·
                  refine ⟨3112100812206583528460257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4149467749608778037947009 3112100812206583528460257)
                  ·
                    refine ⟨2334075609154937646345193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3112100812206583528460257 2334075609154937646345193)
                    ·
                      refine ⟨1750556706866203234758895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2334075609154937646345193 1750556706866203234758895)
                      ·
                        rfl

theorem cell23_3409197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 3, 2, 2, 2, 2].length) (baseStart_3409197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3409197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3409197 prefixEnd_3409197 := by exact prefixLift 3409197
  have htrace : WordTrace (prefixWord ++ tailWord_3409197) baseStart_3409197 baseEnd_3409197 := by
    simpa [prefixWord, tailWord_3409197, baseEnd_3409197] using wordTrace_append hprefix tailTrace_3409197
  have hstable : (prefixWord ++ tailWord_3409197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3409197).length < 2 ^ (prefixWord ++ tailWord_3409197).sum := by decide
  have hdescent : baseEnd_3409197 < baseStart_3409197 := by decide
  rcases family_descends (prefixWord ++ tailWord_3409197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3409236 : List Nat := [2, 4, 1, 1, 2, 1, 2, 3, 2, 1, 4]
def baseStart_3409236 : Nat := 118140960795 + 3409236 * 2 ^ 59
def prefixEnd_3409236 : Nat := 4983230072969 + 3 ^ 40 * 3409236 * 2
def baseEnd_3409236 : Nat := 1750576732611728582171215

theorem tailTrace_3409236 : CollatzResearch.WordTrace tailWord_3409236 prefixEnd_3409236 1750576732611728582171215 := by
  unfold tailWord_3409236
  simp only [CollatzResearch.WordTrace]
  refine ⟨62172526138463848999263781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82896701517951798665685041 62172526138463848999263781)
  ·
    refine ⟨11657348650961971687361959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 62172526138463848999263781 11657348650961971687361959)
    ·
      refine ⟨17486022976442957531042939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11657348650961971687361959 17486022976442957531042939)
      ·
        refine ⟨26229034464664436296564409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17486022976442957531042939 26229034464664436296564409)
        ·
          refine ⟨19671775848498327222423307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26229034464664436296564409 19671775848498327222423307)
          ·
            refine ⟨29507663772747490833634961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19671775848498327222423307 29507663772747490833634961)
            ·
              refine ⟨22130747829560618125226221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29507663772747490833634961 22130747829560618125226221)
              ·
                refine ⟨8299030436085231796959833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22130747829560618125226221 8299030436085231796959833)
                ·
                  refine ⟨6224272827063923847719875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8299030436085231796959833 6224272827063923847719875)
                  ·
                    refine ⟨9336409240595885771579813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6224272827063923847719875 9336409240595885771579813)
                    ·
                      refine ⟨1750576732611728582171215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9336409240595885771579813 1750576732611728582171215)
                      ·
                        rfl

theorem cell23_3409236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 2, 3, 2, 1, 4].length) (baseStart_3409236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3409236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3409236 prefixEnd_3409236 := by exact prefixLift 3409236
  have htrace : WordTrace (prefixWord ++ tailWord_3409236) baseStart_3409236 baseEnd_3409236 := by
    simpa [prefixWord, tailWord_3409236, baseEnd_3409236] using wordTrace_append hprefix tailTrace_3409236
  have hstable : (prefixWord ++ tailWord_3409236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3409236).length < 2 ^ (prefixWord ++ tailWord_3409236).sum := by decide
  have hdescent : baseEnd_3409236 < baseStart_3409236 := by decide
  rcases family_descends (prefixWord ++ tailWord_3409236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3409310 : List Nat := [4, 3, 1, 2, 2, 1, 2, 2, 6]
def baseStart_3409310 : Nat := 118140960795 + 3409310 * 2 ^ 59
def prefixEnd_3409310 : Nat := 4983230072969 + 3 ^ 40 * 3409310 * 2
def baseEnd_3409310 : Nat := 194512747797795699182875

theorem tailTrace_3409310 : CollatzResearch.WordTrace tailWord_3409310 prefixEnd_3409310 194512747797795699182875 := by
  unfold tailWord_3409310
  simp only [CollatzResearch.WordTrace]
  refine ⟨15543468909832451079590173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 82898500852439739091147589 15543468909832451079590173)
  ·
    refine ⟨5828800841187169154846315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15543468909832451079590173 5828800841187169154846315)
    ·
      refine ⟨8743201261780753732269473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5828800841187169154846315 8743201261780753732269473)
      ·
        refine ⟨6557400946335565299202105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8743201261780753732269473 6557400946335565299202105)
        ·
          refine ⟨4918050709751673974401579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6557400946335565299202105 4918050709751673974401579)
          ·
            refine ⟨7377076064627510961602369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4918050709751673974401579 7377076064627510961602369)
            ·
              refine ⟨5532807048470633221201777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7377076064627510961602369 5532807048470633221201777)
              ·
                refine ⟨4149605286352974915901333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5532807048470633221201777 4149605286352974915901333)
                ·
                  refine ⟨194512747797795699182875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4149605286352974915901333 194512747797795699182875)
                  ·
                    rfl

theorem cell23_3409310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 2, 2, 6].length) (baseStart_3409310 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3409310 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3409310 prefixEnd_3409310 := by exact prefixLift 3409310
  have htrace : WordTrace (prefixWord ++ tailWord_3409310) baseStart_3409310 baseEnd_3409310 := by
    simpa [prefixWord, tailWord_3409310, baseEnd_3409310] using wordTrace_append hprefix tailTrace_3409310
  have hstable : (prefixWord ++ tailWord_3409310).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3409310).length < 2 ^ (prefixWord ++ tailWord_3409310).sum := by decide
  have hdescent : baseEnd_3409310 < baseStart_3409310 := by decide
  rcases family_descends (prefixWord ++ tailWord_3409310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3409370 : List Nat := [3, 1, 1, 2, 3, 4, 1, 2, 2, 4]
def baseStart_3409370 : Nat := 118140960795 + 3409370 * 2 ^ 59
def prefixEnd_3409370 : Nat := 4983230072969 + 3 ^ 40 * 3409370 * 2
def baseEnd_3409370 : Nat := 583548513006477019298533

theorem tailTrace_3409370 : CollatzResearch.WordTrace tailWord_3409370 prefixEnd_3409370 583548513006477019298533 := by
  unfold tailWord_3409370
  simp only [CollatzResearch.WordTrace]
  refine ⟨31087484914610559720976391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82899959772294825922603709 31087484914610559720976391)
  ·
    refine ⟨46631227371915839581464587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31087484914610559720976391 46631227371915839581464587)
    ·
      refine ⟨69946841057873759372196881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46631227371915839581464587 69946841057873759372196881)
      ·
        refine ⟨52460130793405319529147661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69946841057873759372196881 52460130793405319529147661)
        ·
          refine ⟨19672549047526994823430373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52460130793405319529147661 19672549047526994823430373)
          ·
            refine ⟨3688602946411311529393195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19672549047526994823430373 3688602946411311529393195)
            ·
              refine ⟨5532904419616967294089793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3688602946411311529393195 5532904419616967294089793)
              ·
                refine ⟨4149678314712725470567345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5532904419616967294089793 4149678314712725470567345)
                ·
                  refine ⟨3112258736034544102925509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4149678314712725470567345 3112258736034544102925509)
                  ·
                    refine ⟨583548513006477019298533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3112258736034544102925509 583548513006477019298533)
                    ·
                      rfl

theorem cell23_3409370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 4, 1, 2, 2, 4].length) (baseStart_3409370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3409370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3409370 prefixEnd_3409370 := by exact prefixLift 3409370
  have htrace : WordTrace (prefixWord ++ tailWord_3409370) baseStart_3409370 baseEnd_3409370 := by
    simpa [prefixWord, tailWord_3409370, baseEnd_3409370] using wordTrace_append hprefix tailTrace_3409370
  have hstable : (prefixWord ++ tailWord_3409370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3409370).length < 2 ^ (prefixWord ++ tailWord_3409370).sum := by decide
  have hdescent : baseEnd_3409370 < baseStart_3409370 := by decide
  rcases family_descends (prefixWord ++ tailWord_3409370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3409377 : List Nat := [1, 2, 3, 1, 2, 3, 2, 4, 1, 2, 2]
def baseStart_3409377 : Nat := 118140960795 + 3409377 * 2 ^ 59
def prefixEnd_3409377 : Nat := 4983230072969 + 3 ^ 40 * 3409377 * 2
def baseEnd_3409377 : Nat := 1750649133384012530508067

theorem tailTrace_3409377 : CollatzResearch.WordTrace tailWord_3409377 prefixEnd_3409377 1750649133384012530508067 := by
  unfold tailWord_3409377
  simp only [CollatzResearch.WordTrace]
  refine ⟨124350194969416879079410385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82900129979611252719606923 124350194969416879079410385)
  ·
    refine ⟨93262646227062659309557789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124350194969416879079410385 93262646227062659309557789)
    ·
      refine ⟨34973492335148497241084171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93262646227062659309557789 34973492335148497241084171)
      ·
        refine ⟨52460238502722745861626257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34973492335148497241084171 52460238502722745861626257)
        ·
          refine ⟨39345178877042059396219693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52460238502722745861626257 39345178877042059396219693)
          ·
            refine ⟨14754442078890772273582385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39345178877042059396219693 14754442078890772273582385)
            ·
              refine ⟨11065831559168079205186789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14754442078890772273582385 11065831559168079205186789)
              ·
                refine ⟨2074843417344014850972523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11065831559168079205186789 2074843417344014850972523)
                ·
                  refine ⟨3112265126016022276458785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2074843417344014850972523 3112265126016022276458785)
                  ·
                    refine ⟨2334198844512016707344089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3112265126016022276458785 2334198844512016707344089)
                    ·
                      refine ⟨1750649133384012530508067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2334198844512016707344089 1750649133384012530508067)
                      ·
                        rfl

theorem cell23_3409377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 2, 4, 1, 2, 2].length) (baseStart_3409377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3409377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3409377 prefixEnd_3409377 := by exact prefixLift 3409377
  have htrace : WordTrace (prefixWord ++ tailWord_3409377) baseStart_3409377 baseEnd_3409377 := by
    simpa [prefixWord, tailWord_3409377, baseEnd_3409377] using wordTrace_append hprefix tailTrace_3409377
  have hstable : (prefixWord ++ tailWord_3409377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3409377).length < 2 ^ (prefixWord ++ tailWord_3409377).sum := by decide
  have hdescent : baseEnd_3409377 < baseStart_3409377 := by decide
  rcases family_descends (prefixWord ++ tailWord_3409377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3409393 : List Nat := [1, 2, 2, 2, 3, 2, 3, 1, 1, 3, 3]
def baseStart_3409393 : Nat := 118140960795 + 3409393 * 2 ^ 59
def prefixEnd_3409393 : Nat := 4983230072969 + 3 ^ 40 * 3409393 * 2
def baseEnd_3409393 : Nat := 1750657349074484467907993

theorem tailTrace_3409393 : CollatzResearch.WordTrace tailWord_3409393 prefixEnd_3409393 1750657349074484467907993 := by
  unfold tailWord_3409393
  simp only [CollatzResearch.WordTrace]
  refine ⟨124350778537358913811992833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82900519024905942541328555 124350778537358913811992833)
  ·
    refine ⟨93263083903019185358994625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124350778537358913811992833 93263083903019185358994625)
    ·
      refine ⟨69947312927264389019245969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93263083903019185358994625 69947312927264389019245969)
      ·
        refine ⟨52460484695448291764434477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69947312927264389019245969 52460484695448291764434477)
        ·
          refine ⟨19672681760793109411662929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52460484695448291764434477 19672681760793109411662929)
          ·
            refine ⟨14754511320594832058747197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19672681760793109411662929 14754511320594832058747197)
            ·
              refine ⟨5532941745223062022030199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14754511320594832058747197 5532941745223062022030199)
              ·
                refine ⟨8299412617834593033045299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5532941745223062022030199 8299412617834593033045299)
                ·
                  refine ⟨12449118926751889549567949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8299412617834593033045299 12449118926751889549567949)
                  ·
                    refine ⟨4668419597531958581087981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12449118926751889549567949 4668419597531958581087981)
                    ·
                      refine ⟨1750657349074484467907993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4668419597531958581087981 1750657349074484467907993)
                      ·
                        rfl

theorem cell23_3409393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 3, 1, 1, 3, 3].length) (baseStart_3409393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3409393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3409393 prefixEnd_3409393 := by exact prefixLift 3409393
  have htrace : WordTrace (prefixWord ++ tailWord_3409393) baseStart_3409393 baseEnd_3409393 := by
    simpa [prefixWord, tailWord_3409393, baseEnd_3409393] using wordTrace_append hprefix tailTrace_3409393
  have hstable : (prefixWord ++ tailWord_3409393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3409393).length < 2 ^ (prefixWord ++ tailWord_3409393).sum := by decide
  have hdescent : baseEnd_3409393 < baseStart_3409393 := by decide
  rcases family_descends (prefixWord ++ tailWord_3409393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3409397 : List Nat := [1, 3, 5, 1, 1, 2, 2, 2, 1, 2, 3]
def baseStart_3409397 : Nat := 118140960795 + 3409397 * 2 ^ 59
def prefixEnd_3409397 : Nat := 4983230072969 + 3 ^ 40 * 3409397 * 2
def baseEnd_3409397 : Nat := 1750659402997102452257975

theorem tailTrace_3409397 : CollatzResearch.WordTrace tailWord_3409397 prefixEnd_3409397 1750659402997102452257975 := by
  unfold tailWord_3409397
  simp only [CollatzResearch.WordTrace]
  refine ⟨124350924429344422495138445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82900616286229614996758963 124350924429344422495138445)
  ·
    refine ⟨46631596661004158435676917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 124350924429344422495138445 46631596661004158435676917)
    ·
      refine ⟨4371712186969139853344711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 46631596661004158435676917 4371712186969139853344711)
      ·
        refine ⟨6557568280453709780017067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4371712186969139853344711 6557568280453709780017067)
        ·
          refine ⟨9836352420680564670025601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6557568280453709780017067 9836352420680564670025601)
          ·
            refine ⟨7377264315510423502519201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9836352420680564670025601 7377264315510423502519201)
            ·
              refine ⟨5532948236632817626889401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7377264315510423502519201 5532948236632817626889401)
              ·
                refine ⟨4149711177474613220167051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5532948236632817626889401 4149711177474613220167051)
                ·
                  refine ⟨6224566766211919830250577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4149711177474613220167051 6224566766211919830250577)
                  ·
                    refine ⟨4668425074658939872687933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6224566766211919830250577 4668425074658939872687933)
                    ·
                      refine ⟨1750659402997102452257975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4668425074658939872687933 1750659402997102452257975)
                      ·
                        rfl

theorem cell23_3409397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 2, 2, 1, 2, 3].length) (baseStart_3409397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3409397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3409397 prefixEnd_3409397 := by exact prefixLift 3409397
  have htrace : WordTrace (prefixWord ++ tailWord_3409397) baseStart_3409397 baseEnd_3409397 := by
    simpa [prefixWord, tailWord_3409397, baseEnd_3409397] using wordTrace_append hprefix tailTrace_3409397
  have hstable : (prefixWord ++ tailWord_3409397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3409397).length < 2 ^ (prefixWord ++ tailWord_3409397).sum := by decide
  have hdescent : baseEnd_3409397 < baseStart_3409397 := by decide
  rcases family_descends (prefixWord ++ tailWord_3409397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3409399 : List Nat := [1, 1, 3, 1, 1, 1, 1, 3, 1, 2, 8]
def baseStart_3409399 : Nat := 118140960795 + 3409399 * 2 ^ 59
def prefixEnd_3409399 : Nat := 4983230072969 + 3 ^ 40 * 3409399 * 2
def baseEnd_3409399 : Nat := 1750660429958411444432965

theorem tailTrace_3409399 : CollatzResearch.WordTrace tailWord_3409399 prefixEnd_3409399 1750660429958411444432965 := by
  unfold tailWord_3409399
  simp only [CollatzResearch.WordTrace]
  refine ⟨124350997375337176836711251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82900664916891451224474167 124350997375337176836711251)
  ·
    refine ⟨186526496063005765255066877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124350997375337176836711251 186526496063005765255066877)
    ·
      refine ⟨69947436023627161970650079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 186526496063005765255066877 69947436023627161970650079)
      ·
        refine ⟨104921154035440742955975119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69947436023627161970650079 104921154035440742955975119)
        ·
          refine ⟨157381731053161114433962679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104921154035440742955975119 157381731053161114433962679)
          ·
            refine ⟨236072596579741671650944019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 157381731053161114433962679 236072596579741671650944019)
            ·
              refine ⟨354108894869612507476416029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 236072596579741671650944019 354108894869612507476416029)
              ·
                refine ⟨132790835576104690303656011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 354108894869612507476416029 132790835576104690303656011)
                ·
                  refine ⟨199186253364157035455484017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 132790835576104690303656011 199186253364157035455484017)
                  ·
                    refine ⟨149389690023117776591613013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 199186253364157035455484017 149389690023117776591613013)
                    ·
                      refine ⟨1750660429958411444432965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 149389690023117776591613013 1750660429958411444432965)
                      ·
                        rfl

theorem cell23_3409399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 3, 1, 2, 8].length) (baseStart_3409399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3409399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3409399 prefixEnd_3409399 := by exact prefixLift 3409399
  have htrace : WordTrace (prefixWord ++ tailWord_3409399) baseStart_3409399 baseEnd_3409399 := by
    simpa [prefixWord, tailWord_3409399, baseEnd_3409399] using wordTrace_append hprefix tailTrace_3409399
  have hstable : (prefixWord ++ tailWord_3409399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3409399).length < 2 ^ (prefixWord ++ tailWord_3409399).sum := by decide
  have hdescent : baseEnd_3409399 < baseStart_3409399 := by decide
  rcases family_descends (prefixWord ++ tailWord_3409399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3409414 : List Nat := [6, 2, 1, 1, 2, 1, 2, 1, 1, 1, 5]
def baseStart_3409414 : Nat := 118140960795 + 3409414 * 2 ^ 59
def prefixEnd_3409414 : Nat := 4983230072969 + 3 ^ 40 * 3409414 * 2
def baseEnd_3409414 : Nat := 1750668132168228885745397

theorem tailTrace_3409414 : CollatzResearch.WordTrace tailWord_3409414 prefixEnd_3409414 1750668132168228885745397 := by
  unfold tailWord_3409414
  simp only [CollatzResearch.WordTrace]
  refine ⟨3885985764696338574953353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 82901029646855222932338197 3885985764696338574953353)
  ·
    refine ⟨2914489323522253931215015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3885985764696338574953353 2914489323522253931215015)
    ·
      refine ⟨4371733985283380896822523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2914489323522253931215015 4371733985283380896822523)
      ·
        refine ⟨6557600977925071345233785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4371733985283380896822523 6557600977925071345233785)
        ·
          refine ⟨4918200733443803508925339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6557600977925071345233785 4918200733443803508925339)
          ·
            refine ⟨7377301100165705263388009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4918200733443803508925339 7377301100165705263388009)
            ·
              refine ⟨5532975825124278947541007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7377301100165705263388009 5532975825124278947541007)
              ·
                refine ⟨8299463737686418421311511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5532975825124278947541007 8299463737686418421311511)
                ·
                  refine ⟨12449195606529627631967267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8299463737686418421311511 12449195606529627631967267)
                  ·
                    refine ⟨18673793409794441447950901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12449195606529627631967267 18673793409794441447950901)
                    ·
                      refine ⟨1750668132168228885745397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18673793409794441447950901 1750668132168228885745397)
                      ·
                        rfl

theorem cell23_3409414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 2, 1, 1, 1, 5].length) (baseStart_3409414 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3409414 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3409414 prefixEnd_3409414 := by exact prefixLift 3409414
  have htrace : WordTrace (prefixWord ++ tailWord_3409414) baseStart_3409414 baseEnd_3409414 := by
    simpa [prefixWord, tailWord_3409414, baseEnd_3409414] using wordTrace_append hprefix tailTrace_3409414
  have hstable : (prefixWord ++ tailWord_3409414).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3409414).length < 2 ^ (prefixWord ++ tailWord_3409414).sum := by decide
  have hdescent : baseEnd_3409414 < baseStart_3409414 := by decide
  rcases family_descends (prefixWord ++ tailWord_3409414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3409428 : List Nat := [2, 4, 3, 1, 2, 1, 3, 2, 1, 2, 2]
def baseStart_3409428 : Nat := 118140960795 + 3409428 * 2 ^ 59
def prefixEnd_3409428 : Nat := 4983230072969 + 3 ^ 40 * 3409428 * 2
def baseEnd_3409428 : Nat := 1750675320897391830970333

theorem tailTrace_3409428 : CollatzResearch.WordTrace tailWord_3409428 prefixEnd_3409428 1750675320897391830970333 := by
  unfold tailWord_3409428
  simp only [CollatzResearch.WordTrace]
  refine ⟨62176027546116057394758469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82901370061488076526344625 62176027546116057394758469)
  ·
    refine ⟨11658005164896760761517213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 62176027546116057394758469 11658005164896760761517213)
    ·
      refine ⟨4371751936836285285568955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11658005164896760761517213 4371751936836285285568955)
      ·
        refine ⟨6557627905254427928353433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4371751936836285285568955 6557627905254427928353433)
        ·
          refine ⟨4918220928940820946265075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6557627905254427928353433 4918220928940820946265075)
          ·
            refine ⟨7377331393411231419397613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4918220928940820946265075 7377331393411231419397613)
            ·
              refine ⟨2766499272529211782274105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7377331393411231419397613 2766499272529211782274105)
              ·
                refine ⟨2074874454396908836705579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2766499272529211782274105 2074874454396908836705579)
                ·
                  refine ⟨3112311681595363255058369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2074874454396908836705579 3112311681595363255058369)
                  ·
                    refine ⟨2334233761196522441293777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3112311681595363255058369 2334233761196522441293777)
                    ·
                      refine ⟨1750675320897391830970333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2334233761196522441293777 1750675320897391830970333)
                      ·
                        rfl

theorem cell23_3409428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 3, 2, 1, 2, 2].length) (baseStart_3409428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3409428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3409428 prefixEnd_3409428 := by exact prefixLift 3409428
  have htrace : WordTrace (prefixWord ++ tailWord_3409428) baseStart_3409428 baseEnd_3409428 := by
    simpa [prefixWord, tailWord_3409428, baseEnd_3409428] using wordTrace_append hprefix tailTrace_3409428
  have hstable : (prefixWord ++ tailWord_3409428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3409428).length < 2 ^ (prefixWord ++ tailWord_3409428).sum := by decide
  have hdescent : baseEnd_3409428 < baseStart_3409428 := by decide
  rcases family_descends (prefixWord ++ tailWord_3409428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3409436 : List Nat := [2, 2, 3, 1, 2, 1, 1, 2, 1, 3, 5]
def baseStart_3409436 : Nat := 118140960795 + 3409436 * 2 ^ 59
def prefixEnd_3409436 : Nat := 4983230072969 + 3 ^ 40 * 3409436 * 2
def baseEnd_3409436 : Nat := 1750679428742627799670295

theorem tailTrace_3409436 : CollatzResearch.WordTrace tailWord_3409436 prefixEnd_3409436 1750679428742627799670295 := by
  unfold tailWord_3409436
  simp only [CollatzResearch.WordTrace]
  refine ⟨62176173438101566077904081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82901564584135421437205441 62176173438101566077904081)
  ·
    refine ⟨46632130078576174558428061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62176173438101566077904081 46632130078576174558428061)
    ·
      refine ⟨17487048779466065459410523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46632130078576174558428061 17487048779466065459410523)
      ·
        refine ⟨26230573169199098189115785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17487048779466065459410523 26230573169199098189115785)
        ·
          refine ⟨19672929876899323641836839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26230573169199098189115785 19672929876899323641836839)
          ·
            refine ⟨29509394815348985462755259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19672929876899323641836839 29509394815348985462755259)
            ·
              refine ⟨44264092223023478194132889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29509394815348985462755259 44264092223023478194132889)
              ·
                refine ⟨33198069167267608645599667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44264092223023478194132889 33198069167267608645599667)
                ·
                  refine ⟨49797103750901412968399501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33198069167267608645599667 49797103750901412968399501)
                  ·
                    refine ⟨18673913906588029863149813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 49797103750901412968399501 18673913906588029863149813)
                    ·
                      refine ⟨1750679428742627799670295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18673913906588029863149813 1750679428742627799670295)
                      ·
                        rfl

theorem cell23_3409436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 2, 1, 3, 5].length) (baseStart_3409436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3409436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3409436 prefixEnd_3409436 := by exact prefixLift 3409436
  have htrace : WordTrace (prefixWord ++ tailWord_3409436) baseStart_3409436 baseEnd_3409436 := by
    simpa [prefixWord, tailWord_3409436, baseEnd_3409436] using wordTrace_append hprefix tailTrace_3409436
  have hstable : (prefixWord ++ tailWord_3409436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3409436).length < 2 ^ (prefixWord ++ tailWord_3409436).sum := by decide
  have hdescent : baseEnd_3409436 < baseStart_3409436 := by decide
  rcases family_descends (prefixWord ++ tailWord_3409436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3409438 : List Nat := [4, 3, 3, 1, 1, 2, 2, 1, 2, 4]
def baseStart_3409438 : Nat := 118140960795 + 3409438 * 2 ^ 59
def prefixEnd_3409438 : Nat := 4983230072969 + 3 ^ 40 * 3409438 * 2
def baseEnd_3409438 : Nat := 583560151901312263948429

theorem tailTrace_3409438 : CollatzResearch.WordTrace tailWord_3409438 prefixEnd_3409438 583560151901312263948429 := by
  unfold tailWord_3409438
  simp only [CollatzResearch.WordTrace]
  refine ⟨15544052477774485812172621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 82901613214797257664920645 15544052477774485812172621)
  ·
    refine ⟨5829019679165432179564733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15544052477774485812172621 5829019679165432179564733)
    ·
      refine ⟨2185882379687037067336775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5829019679165432179564733 2185882379687037067336775)
      ·
        refine ⟨3278823569530555601005163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2185882379687037067336775 3278823569530555601005163)
        ·
          refine ⟨4918235354295833401507745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3278823569530555601005163 4918235354295833401507745)
          ·
            refine ⟨3688676515721875051130809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4918235354295833401507745 3688676515721875051130809)
            ·
              refine ⟨2766507386791406288348107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3688676515721875051130809 2766507386791406288348107)
              ·
                refine ⟨4149761080187109432522161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2766507386791406288348107 4149761080187109432522161)
                ·
                  refine ⟨3112320810140332074391621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4149761080187109432522161 3112320810140332074391621)
                  ·
                    refine ⟨583560151901312263948429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3112320810140332074391621 583560151901312263948429)
                    ·
                      rfl

theorem cell23_3409438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 2, 2, 1, 2, 4].length) (baseStart_3409438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3409438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3409438 prefixEnd_3409438 := by exact prefixLift 3409438
  have htrace : WordTrace (prefixWord ++ tailWord_3409438) baseStart_3409438 baseEnd_3409438 := by
    simpa [prefixWord, tailWord_3409438, baseEnd_3409438] using wordTrace_append hprefix tailTrace_3409438
  have hstable : (prefixWord ++ tailWord_3409438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3409438).length < 2 ^ (prefixWord ++ tailWord_3409438).sum := by decide
  have hdescent : baseEnd_3409438 < baseStart_3409438 := by decide
  rcases family_descends (prefixWord ++ tailWord_3409438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3409450 : List Nat := [3, 1, 4, 1, 1, 1, 2, 3, 1, 4, 2]
def baseStart_3409450 : Nat := 118140960795 + 3409450 * 2 ^ 59
def prefixEnd_3409450 : Nat := 4983230072969 + 3 ^ 40 * 3409450 * 2
def baseEnd_3409450 : Nat := 1750686617471790744895231

theorem tailTrace_3409450 : CollatzResearch.WordTrace tailWord_3409450 prefixEnd_3409450 1750686617471790744895231 := by
  unfold tailWord_3409450
  simp only [CollatzResearch.WordTrace]
  refine ⟨31088214374538103136704451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82901904998768275031211869 31088214374538103136704451)
  ·
    refine ⟨46632321561807154705056677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31088214374538103136704451 46632321561807154705056677)
    ·
      refine ⟨8743560292838841507198127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 46632321561807154705056677 8743560292838841507198127)
      ·
        refine ⟨13115340439258262260797191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8743560292838841507198127 13115340439258262260797191)
        ·
          refine ⟨19673010658887393391195787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13115340439258262260797191 19673010658887393391195787)
          ·
            refine ⟨29509515988331090086793681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19673010658887393391195787 29509515988331090086793681)
            ·
              refine ⟨22132136991248317565095261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29509515988331090086793681 22132136991248317565095261)
              ·
                refine ⟨8299551371718119086910723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22132136991248317565095261 8299551371718119086910723)
                ·
                  refine ⟨12449327057577178630366085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8299551371718119086910723 12449327057577178630366085)
                  ·
                    refine ⟨2334248823295720993193641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12449327057577178630366085 2334248823295720993193641)
                    ·
                      refine ⟨1750686617471790744895231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2334248823295720993193641 1750686617471790744895231)
                      ·
                        rfl

theorem cell23_3409450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 2, 3, 1, 4, 2].length) (baseStart_3409450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3409450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3409450 prefixEnd_3409450 := by exact prefixLift 3409450
  have htrace : WordTrace (prefixWord ++ tailWord_3409450) baseStart_3409450 baseEnd_3409450 := by
    simpa [prefixWord, tailWord_3409450, baseEnd_3409450] using wordTrace_append hprefix tailTrace_3409450
  have hstable : (prefixWord ++ tailWord_3409450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3409450).length < 2 ^ (prefixWord ++ tailWord_3409450).sum := by decide
  have hdescent : baseEnd_3409450 < baseStart_3409450 := by decide
  rcases family_descends (prefixWord ++ tailWord_3409450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3409454 : List Nat := [4, 1, 3, 1, 2, 3, 1, 2, 1, 3, 2]
def baseStart_3409454 : Nat := 118140960795 + 3409454 * 2 ^ 59
def prefixEnd_3409454 : Nat := 4983230072969 + 3 ^ 40 * 3409454 * 2
def baseEnd_3409454 : Nat := 1750688671394408729245213

theorem tailTrace_3409454 : CollatzResearch.WordTrace tailWord_3409454 prefixEnd_3409454 1750688671394408729245213 := by
  unfold tailWord_3409454
  simp only [CollatzResearch.WordTrace]
  refine ⟨15544125423767240153745427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 82902002260091947486642277 15544125423767240153745427)
  ·
    refine ⟨23316188135650860230618141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15544125423767240153745427 23316188135650860230618141)
    ·
      refine ⟨8743570550869072586481803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23316188135650860230618141 8743570550869072586481803)
      ·
        refine ⟨13115355826303608879722705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8743570550869072586481803 13115355826303608879722705)
        ·
          refine ⟨9836516869727706659792029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13115355826303608879722705 9836516869727706659792029)
          ·
            refine ⟨3688693826147889997422011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9836516869727706659792029 3688693826147889997422011)
            ·
              refine ⟨5533040739221834996133017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3688693826147889997422011 5533040739221834996133017)
              ·
                refine ⟨4149780554416376247099763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5533040739221834996133017 4149780554416376247099763)
                ·
                  refine ⟨6224670831624564370649645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4149780554416376247099763 6224670831624564370649645)
                  ·
                    refine ⟨2334251561859211638993617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6224670831624564370649645 2334251561859211638993617)
                    ·
                      refine ⟨1750688671394408729245213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2334251561859211638993617 1750688671394408729245213)
                      ·
                        rfl

theorem cell23_3409454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 3, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 3, 1, 2, 1, 3, 2].length) (baseStart_3409454 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3409454 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3409454 prefixEnd_3409454 := by exact prefixLift 3409454
  have htrace : WordTrace (prefixWord ++ tailWord_3409454) baseStart_3409454 baseEnd_3409454 := by
    simpa [prefixWord, tailWord_3409454, baseEnd_3409454] using wordTrace_append hprefix tailTrace_3409454
  have hstable : (prefixWord ++ tailWord_3409454).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3409454).length < 2 ^ (prefixWord ++ tailWord_3409454).sum := by decide
  have hdescent : baseEnd_3409454 < baseStart_3409454 := by decide
  rcases family_descends (prefixWord ++ tailWord_3409454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3409486 : List Nat := [4, 1, 1, 1, 1, 2, 1, 2, 3, 7]
def baseStart_3409486 : Nat := 118140960795 + 3409486 * 2 ^ 59
def prefixEnd_3409486 : Nat := 4983230072969 + 3 ^ 40 * 3409486 * 2
def baseEnd_3409486 : Nat := 583568367591784201348355

theorem tailTrace_3409486 : CollatzResearch.WordTrace tailWord_3409486 prefixEnd_3409486 583568367591784201348355 := by
  unfold tailWord_3409486
  simp only [CollatzResearch.WordTrace]
  refine ⟨15544271315752748836891039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 82902780350681327130085541 15544271315752748836891039)
  ·
    refine ⟨23316406973629123255336559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15544271315752748836891039 23316406973629123255336559)
    ·
      refine ⟨34974610460443684883004839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23316406973629123255336559 34974610460443684883004839)
      ·
        refine ⟨52461915690665527324507259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34974610460443684883004839 52461915690665527324507259)
        ·
          refine ⟨78692873535998290986760889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52461915690665527324507259 78692873535998290986760889)
          ·
            refine ⟨59019655151998718240070667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78692873535998290986760889 59019655151998718240070667)
            ·
              refine ⟨88529482727998077360106001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59019655151998718240070667 88529482727998077360106001)
              ·
                refine ⟨66397112045998558020079501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 88529482727998077360106001 66397112045998558020079501)
                ·
                  refine ⟨24898917017249459257529813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 66397112045998558020079501 24898917017249459257529813)
                  ·
                    refine ⟨583568367591784201348355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 24898917017249459257529813 583568367591784201348355)
                    ·
                      rfl

theorem cell23_3409486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 2, 3, 7].length) (baseStart_3409486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3409486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3409486 prefixEnd_3409486 := by exact prefixLift 3409486
  have htrace : WordTrace (prefixWord ++ tailWord_3409486) baseStart_3409486 baseEnd_3409486 := by
    simpa [prefixWord, tailWord_3409486, baseEnd_3409486] using wordTrace_append hprefix tailTrace_3409486
  have hstable : (prefixWord ++ tailWord_3409486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3409486).length < 2 ^ (prefixWord ++ tailWord_3409486).sum := by decide
  have hdescent : baseEnd_3409486 < baseStart_3409486 := by decide
  rcases family_descends (prefixWord ++ tailWord_3409486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3409490 : List Nat := [3, 2, 2, 1, 2, 3, 1, 4, 5]
def baseStart_3409490 : Nat := 118140960795 + 3409490 * 2 ^ 59
def prefixEnd_3409490 : Nat := 4983230072969 + 3 ^ 40 * 3409490 * 2
def baseEnd_3409490 : Nat := 194523017410885620932783

theorem tailTrace_3409490 : CollatzResearch.WordTrace tailWord_3409490 prefixEnd_3409490 194523017410885620932783 := by
  unfold tailWord_3409490
  simp only [CollatzResearch.WordTrace]
  refine ⟨31088579104501874844568481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82902877612004999585515949 31088579104501874844568481)
  ·
    refine ⟨23316434328376406133426361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31088579104501874844568481 23316434328376406133426361)
    ·
      refine ⟨17487325746282304600069771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23316434328376406133426361 17487325746282304600069771)
      ·
        refine ⟨26230988619423456900104657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17487325746282304600069771 26230988619423456900104657)
        ·
          refine ⟨19673241464567592675078493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26230988619423456900104657 19673241464567592675078493)
          ·
            refine ⟨7377465549212847253154435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19673241464567592675078493 7377465549212847253154435)
            ·
              refine ⟨11066198323819270879731653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7377465549212847253154435 11066198323819270879731653)
              ·
                refine ⟨2074912185716113289949685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11066198323819270879731653 2074912185716113289949685)
                ·
                  refine ⟨194523017410885620932783, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2074912185716113289949685 194523017410885620932783)
                  ·
                    rfl

theorem cell23_3409490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 1, 4, 5].length) (baseStart_3409490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3409490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3409490 prefixEnd_3409490 := by exact prefixLift 3409490
  have htrace : WordTrace (prefixWord ++ tailWord_3409490) baseStart_3409490 baseEnd_3409490 := by
    simpa [prefixWord, tailWord_3409490, baseEnd_3409490] using wordTrace_append hprefix tailTrace_3409490
  have hstable : (prefixWord ++ tailWord_3409490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3409490).length < 2 ^ (prefixWord ++ tailWord_3409490).sum := by decide
  have hdescent : baseEnd_3409490 < baseStart_3409490 := by decide
  rcases family_descends (prefixWord ++ tailWord_3409490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3409500 : List Nat := [2, 2, 4, 1, 2, 2, 1, 1, 2, 3, 3]
def baseStart_3409500 : Nat := 118140960795 + 3409500 * 2 ^ 59
def prefixEnd_3409500 : Nat := 4983230072969 + 3 ^ 40 * 3409500 * 2
def baseEnd_3409500 : Nat := 1750712291504515549270001

theorem tailTrace_3409500 : CollatzResearch.WordTrace tailWord_3409500 prefixEnd_3409500 1750712291504515549270001 := by
  unfold tailWord_3409500
  simp only [CollatzResearch.WordTrace]
  refine ⟨62177340573985635543068977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82903120765314180724091969 62177340573985635543068977)
  ·
    refine ⟨46633005430489226657301733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62177340573985635543068977 46633005430489226657301733)
    ·
      refine ⟨8743688518216729998244075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 46633005430489226657301733 8743688518216729998244075)
      ·
        refine ⟨13115532777325094997366113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8743688518216729998244075 13115532777325094997366113)
        ·
          refine ⟨9836649582993821248024585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13115532777325094997366113 9836649582993821248024585)
          ·
            refine ⟨7377487187245365936018439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9836649582993821248024585 7377487187245365936018439)
            ·
              refine ⟨11066230780868048904027659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7377487187245365936018439 11066230780868048904027659)
              ·
                refine ⟨16599346171302073356041489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11066230780868048904027659 16599346171302073356041489)
                ·
                  refine ⟨12449509628476555017031117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16599346171302073356041489 12449509628476555017031117)
                  ·
                    refine ⟨4668566110678708131386669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12449509628476555017031117 4668566110678708131386669)
                    ·
                      refine ⟨1750712291504515549270001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4668566110678708131386669 1750712291504515549270001)
                      ·
                        rfl

theorem cell23_3409500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 1, 1, 2, 3, 3].length) (baseStart_3409500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3409500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3409500 prefixEnd_3409500 := by exact prefixLift 3409500
  have htrace : WordTrace (prefixWord ++ tailWord_3409500) baseStart_3409500 baseEnd_3409500 := by
    simpa [prefixWord, tailWord_3409500, baseEnd_3409500] using wordTrace_append hprefix tailTrace_3409500
  have hstable : (prefixWord ++ tailWord_3409500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3409500).length < 2 ^ (prefixWord ++ tailWord_3409500).sum := by decide
  have hdescent : baseEnd_3409500 < baseStart_3409500 := by decide
  rcases family_descends (prefixWord ++ tailWord_3409500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3409520 : List Nat := [2, 1, 1, 1, 6, 3, 1, 1, 2, 5]
def baseStart_3409520 : Nat := 118140960795 + 3409520 * 2 ^ 59
def prefixEnd_3409520 : Nat := 4983230072969 + 3 ^ 40 * 3409520 * 2
def baseEnd_3409520 : Nat := 583574187039201823673303

theorem tailTrace_3409520 : CollatzResearch.WordTrace tailWord_3409520 prefixEnd_3409520 583574187039201823673303 := by
  unfold tailWord_3409520
  simp only [CollatzResearch.WordTrace]
  refine ⟨62177705303949407250933007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82903607071932543001244009 62177705303949407250933007)
  ·
    refine ⟨93266557955924110876399511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62177705303949407250933007 93266557955924110876399511)
    ·
      refine ⟨139899836933886166314599267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93266557955924110876399511 139899836933886166314599267)
      ·
        refine ⟨209849755400829249471898901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139899836933886166314599267 209849755400829249471898901)
        ·
          refine ⟨9836707284413871068995261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 209849755400829249471898901 9836707284413871068995261)
          ·
            refine ⟨3688765231655201650873223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9836707284413871068995261 3688765231655201650873223)
            ·
              refine ⟨5533147847482802476309835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3688765231655201650873223 5533147847482802476309835)
              ·
                refine ⟨8299721771224203714464753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5533147847482802476309835 8299721771224203714464753)
                ·
                  refine ⟨6224791328418152785848565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8299721771224203714464753 6224791328418152785848565)
                  ·
                    refine ⟨583574187039201823673303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6224791328418152785848565 583574187039201823673303)
                    ·
                      rfl

theorem cell23_3409520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 3, 1, 1, 2, 5].length) (baseStart_3409520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3409520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3409520 prefixEnd_3409520 := by exact prefixLift 3409520
  have htrace : WordTrace (prefixWord ++ tailWord_3409520) baseStart_3409520 baseEnd_3409520 := by
    simpa [prefixWord, tailWord_3409520, baseEnd_3409520] using wordTrace_append hprefix tailTrace_3409520
  have hstable : (prefixWord ++ tailWord_3409520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3409520).length < 2 ^ (prefixWord ++ tailWord_3409520).sum := by decide
  have hdescent : baseEnd_3409520 < baseStart_3409520 := by decide
  rcases family_descends (prefixWord ++ tailWord_3409520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3409536 : List Nat := [2, 1, 1, 2, 1, 4, 1, 1, 1, 3, 6]
def baseStart_3409536 : Nat := 118140960795 + 3409536 * 2 ^ 59
def prefixEnd_3409536 : Nat := 4983230072969 + 3 ^ 40 * 3409536 * 2
def baseEnd_3409536 : Nat := 1750730776808077408419835

theorem tailTrace_3409536 : CollatzResearch.WordTrace tailWord_3409536 prefixEnd_3409536 1750730776808077408419835 := by
  unfold tailWord_3409536
  simp only [CollatzResearch.WordTrace]
  refine ⟨62177997087920424617224231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82903996117227232822965641 62177997087920424617224231)
  ·
    refine ⟨93266995631880636925836347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62177997087920424617224231 93266995631880636925836347)
    ·
      refine ⟨139900493447820955388754521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93266995631880636925836347 139900493447820955388754521)
      ·
        refine ⟨104925370085865716541565891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 139900493447820955388754521 104925370085865716541565891)
        ·
          refine ⟨157388055128798574812348837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104925370085865716541565891 157388055128798574812348837)
          ·
            refine ⟨29510260336649732777315407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 157388055128798574812348837 29510260336649732777315407)
            ·
              refine ⟨44265390504974599165973111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29510260336649732777315407 44265390504974599165973111)
              ·
                refine ⟨66398085757461898748959667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44265390504974599165973111 66398085757461898748959667)
                ·
                  refine ⟨99597128636192848123439501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 66398085757461898748959667 99597128636192848123439501)
                  ·
                    refine ⟨37348923238572318046289813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 99597128636192848123439501 37348923238572318046289813)
                    ·
                      refine ⟨1750730776808077408419835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 37348923238572318046289813 1750730776808077408419835)
                      ·
                        rfl

theorem cell23_3409536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 1, 1, 3, 6].length) (baseStart_3409536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3409536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3409536 prefixEnd_3409536 := by exact prefixLift 3409536
  have htrace : WordTrace (prefixWord ++ tailWord_3409536) baseStart_3409536 baseEnd_3409536 := by
    simpa [prefixWord, tailWord_3409536, baseEnd_3409536] using wordTrace_append hprefix tailTrace_3409536
  have hstable : (prefixWord ++ tailWord_3409536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3409536).length < 2 ^ (prefixWord ++ tailWord_3409536).sum := by decide
  have hdescent : baseEnd_3409536 < baseStart_3409536 := by decide
  rcases family_descends (prefixWord ++ tailWord_3409536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3409550 : List Nat := [4, 1, 1, 3, 1, 2, 1, 3, 3, 4]
def baseStart_3409550 : Nat := 118140960795 + 3409550 * 2 ^ 59
def prefixEnd_3409550 : Nat := 4983230072969 + 3 ^ 40 * 3409550 * 2
def baseEnd_3409550 : Nat := 583579321845746784548257

theorem tailTrace_3409550 : CollatzResearch.WordTrace tailWord_3409550 prefixEnd_3409550 583579321845746784548257 := by
  unfold tailWord_3409550
  simp only [CollatzResearch.WordTrace]
  refine ⟨15544563099723766203182263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 82904336531860086416972069 15544563099723766203182263)
  ·
    refine ⟨23316844649585649304773395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15544563099723766203182263 23316844649585649304773395)
    ·
      refine ⟨34975266974378473957160093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23316844649585649304773395 34975266974378473957160093)
      ·
        refine ⟨13115725115391927733935035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34975266974378473957160093 13115725115391927733935035)
        ·
          refine ⟨19673587673087891600902553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13115725115391927733935035 19673587673087891600902553)
          ·
            refine ⟨14755190754815918700676915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19673587673087891600902553 14755190754815918700676915)
            ·
              refine ⟨22132786132223878051015373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14755190754815918700676915 22132786132223878051015373)
              ·
                refine ⟨8299794799583954269130765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22132786132223878051015373 8299794799583954269130765)
                ·
                  refine ⟨3112423049843982850924037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8299794799583954269130765 3112423049843982850924037)
                  ·
                    refine ⟨583579321845746784548257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3112423049843982850924037 583579321845746784548257)
                    ·
                      rfl

theorem cell23_3409550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 1, 3, 3, 4].length) (baseStart_3409550 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3409550 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3409550 prefixEnd_3409550 := by exact prefixLift 3409550
  have htrace : WordTrace (prefixWord ++ tailWord_3409550) baseStart_3409550 baseEnd_3409550 := by
    simpa [prefixWord, tailWord_3409550, baseEnd_3409550] using wordTrace_append hprefix tailTrace_3409550
  have hstable : (prefixWord ++ tailWord_3409550).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3409550).length < 2 ^ (prefixWord ++ tailWord_3409550).sum := by decide
  have hdescent : baseEnd_3409550 < baseStart_3409550 := by decide
  rcases family_descends (prefixWord ++ tailWord_3409550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3409623 : List Nat := [1, 1, 3, 2, 1, 3, 2, 3, 1, 6]
def baseStart_3409623 : Nat := 118140960795 + 3409623 * 2 ^ 59
def prefixEnd_3409623 : Nat := 4983230072969 + 3 ^ 40 * 3409623 * 2
def baseEnd_3409623 : Nat := 583591816541672856010645

theorem tailTrace_3409623 : CollatzResearch.WordTrace tailWord_3409623 prefixEnd_3409623 583591816541672856010645 := by
  unfold tailWord_3409623
  simp only [CollatzResearch.WordTrace]
  refine ⟨124359167326525663092865523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82906111551017108728577015 124359167326525663092865523)
  ·
    refine ⟨186538750989788494639298285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124359167326525663092865523 186538750989788494639298285)
    ·
      refine ⟨69952031621170685489736857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 186538750989788494639298285 69952031621170685489736857)
      ·
        refine ⟨52464023715878014117302643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69952031621170685489736857 52464023715878014117302643)
        ·
          refine ⟨78696035573817021175953965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52464023715878014117302643 78696035573817021175953965)
          ·
            refine ⟨29511013340181382940982737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 78696035573817021175953965 29511013340181382940982737)
            ·
              refine ⟨22133260005136037205737053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29511013340181382940982737 22133260005136037205737053)
              ·
                refine ⟨8299972501926013952151395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22133260005136037205737053 8299972501926013952151395)
                ·
                  refine ⟨12449958752889020928227093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8299972501926013952151395 12449958752889020928227093)
                  ·
                    refine ⟨583591816541672856010645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12449958752889020928227093 583591816541672856010645)
                    ·
                      rfl

theorem cell23_3409623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 2, 3, 1, 6].length) (baseStart_3409623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3409623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3409623 prefixEnd_3409623 := by exact prefixLift 3409623
  have htrace : WordTrace (prefixWord ++ tailWord_3409623) baseStart_3409623 baseEnd_3409623 := by
    simpa [prefixWord, tailWord_3409623, baseEnd_3409623] using wordTrace_append hprefix tailTrace_3409623
  have hstable : (prefixWord ++ tailWord_3409623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3409623).length < 2 ^ (prefixWord ++ tailWord_3409623).sum := by decide
  have hdescent : baseEnd_3409623 < baseStart_3409623 := by decide
  rcases family_descends (prefixWord ++ tailWord_3409623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3409640 : List Nat := [2, 1, 4, 1, 3, 2, 1, 2, 1, 6]
def baseStart_3409640 : Nat := 118140960795 + 3409640 * 2 ^ 59
def prefixEnd_3409640 : Nat := 4983230072969 + 3 ^ 40 * 3409640 * 2
def baseEnd_3409640 : Nat := 583594726265381667173119

theorem tailTrace_3409640 : CollatzResearch.WordTrace tailWord_3409640 prefixEnd_3409640 583594726265381667173119 := by
  unfold tailWord_3409640
  simp only [CollatzResearch.WordTrace]
  refine ⟨62179893683732037498117187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82906524911642716664156249 62179893683732037498117187)
  ·
    refine ⟨93269840525598056247175781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62179893683732037498117187 93269840525598056247175781)
    ·
      refine ⟨17488095098549635546345459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 93269840525598056247175781 17488095098549635546345459)
      ·
        refine ⟨26232142647824453319518189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17488095098549635546345459 26232142647824453319518189)
        ·
          refine ⟨9837053492934169994819321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26232142647824453319518189 9837053492934169994819321)
          ·
            refine ⟨7377790119700627496114491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9837053492934169994819321 7377790119700627496114491)
            ·
              refine ⟨11066685179550941244171737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7377790119700627496114491 11066685179550941244171737)
              ·
                refine ⟨8300013884663205933128803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11066685179550941244171737 8300013884663205933128803)
                ·
                  refine ⟨12450020826994808899693205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8300013884663205933128803 12450020826994808899693205)
                  ·
                    refine ⟨583594726265381667173119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12450020826994808899693205 583594726265381667173119)
                    ·
                      rfl

theorem cell23_3409640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 1, 2, 1, 6].length) (baseStart_3409640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3409640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3409640 prefixEnd_3409640 := by exact prefixLift 3409640
  have htrace : WordTrace (prefixWord ++ tailWord_3409640) baseStart_3409640 baseEnd_3409640 := by
    simpa [prefixWord, tailWord_3409640, baseEnd_3409640] using wordTrace_append hprefix tailTrace_3409640
  have hstable : (prefixWord ++ tailWord_3409640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3409640).length < 2 ^ (prefixWord ++ tailWord_3409640).sum := by decide
  have hdescent : baseEnd_3409640 < baseStart_3409640 := by decide
  rcases family_descends (prefixWord ++ tailWord_3409640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3409643 : List Nat := [1, 1, 1, 1, 2, 4, 3, 1, 3, 2, 4]
def baseStart_3409643 : Nat := 118140960795 + 3409643 * 2 ^ 59
def prefixEnd_3409643 : Nat := 4983230072969 + 3 ^ 40 * 3409643 * 2
def baseEnd_3409643 : Nat := 1750785719238108489781843

theorem tailTrace_3409643 : CollatzResearch.WordTrace tailWord_3409643 prefixEnd_3409643 1750785719238108489781843 := by
  unfold tailWord_3409643
  simp only [CollatzResearch.WordTrace]
  refine ⟨124359896786453206508593583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82906597857635471005729055 124359896786453206508593583)
  ·
    refine ⟨186539845179679809762890375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124359896786453206508593583 186539845179679809762890375)
    ·
      refine ⟨279809767769519714644335563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186539845179679809762890375 279809767769519714644335563)
      ·
        refine ⟨419714651654279571966503345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 279809767769519714644335563 419714651654279571966503345)
        ·
          refine ⟨314785988740709678974877509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 419714651654279571966503345 314785988740709678974877509)
          ·
            refine ⟨59022372888883064807789533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 314785988740709678974877509 59022372888883064807789533)
            ·
              refine ⟨22133389833331149302921075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59022372888883064807789533 22133389833331149302921075)
              ·
                refine ⟨33200084749996723954381613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22133389833331149302921075 33200084749996723954381613)
                ·
                  refine ⟨12450031781248771482893105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33200084749996723954381613 12450031781248771482893105)
                  ·
                    refine ⟨9337523835936578612169829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12450031781248771482893105 9337523835936578612169829)
                    ·
                      refine ⟨1750785719238108489781843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9337523835936578612169829 1750785719238108489781843)
                      ·
                        rfl

theorem cell23_3409643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 3, 1, 3, 2, 4].length) (baseStart_3409643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3409643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3409643 prefixEnd_3409643 := by exact prefixLift 3409643
  have htrace : WordTrace (prefixWord ++ tailWord_3409643) baseStart_3409643 baseEnd_3409643 := by
    simpa [prefixWord, tailWord_3409643, baseEnd_3409643] using wordTrace_append hprefix tailTrace_3409643
  have hstable : (prefixWord ++ tailWord_3409643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3409643).length < 2 ^ (prefixWord ++ tailWord_3409643).sum := by decide
  have hdescent : baseEnd_3409643 < baseStart_3409643 := by decide
  rcases family_descends (prefixWord ++ tailWord_3409643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3409647 : List Nat := [1, 1, 2, 1, 5, 1, 5, 1, 1, 1, 4]
def baseStart_3409647 : Nat := 118140960795 + 3409647 * 2 ^ 59
def prefixEnd_3409647 : Nat := 4983230072969 + 3 ^ 40 * 3409647 * 2
def baseEnd_3409647 : Nat := 1750787773160726474131825

theorem tailTrace_3409647 : CollatzResearch.WordTrace tailWord_3409647 prefixEnd_3409647 1750787773160726474131825 := by
  unfold tailWord_3409647
  simp only [CollatzResearch.WordTrace]
  refine ⟨124360042678438715191739195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82906695118959143461159463 124360042678438715191739195)
  ·
    refine ⟨186540064017658072787608793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124360042678438715191739195 186540064017658072787608793)
    ·
      refine ⟨139905048013243554590706595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 186540064017658072787608793 139905048013243554590706595)
      ·
        refine ⟨209857572019865331886059893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139905048013243554590706595 209857572019865331886059893)
        ·
          refine ⟨19674147376862374864318115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 209857572019865331886059893 19674147376862374864318115)
          ·
            refine ⟨29511221065293562296477173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19674147376862374864318115 29511221065293562296477173)
            ·
              refine ⟨2766676974871271465294735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 29511221065293562296477173 2766676974871271465294735)
              ·
                refine ⟨4150015462306907197942103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2766676974871271465294735 4150015462306907197942103)
                ·
                  refine ⟨6225023193460360796913155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4150015462306907197942103 6225023193460360796913155)
                  ·
                    refine ⟨9337534790190541195369733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6225023193460360796913155 9337534790190541195369733)
                    ·
                      refine ⟨1750787773160726474131825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9337534790190541195369733 1750787773160726474131825)
                      ·
                        rfl

theorem cell23_3409647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 5, 1, 1, 1, 4].length) (baseStart_3409647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3409647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3409647 prefixEnd_3409647 := by exact prefixLift 3409647
  have htrace : WordTrace (prefixWord ++ tailWord_3409647) baseStart_3409647 baseEnd_3409647 := by
    simpa [prefixWord, tailWord_3409647, baseEnd_3409647] using wordTrace_append hprefix tailTrace_3409647
  have hstable : (prefixWord ++ tailWord_3409647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3409647).length < 2 ^ (prefixWord ++ tailWord_3409647).sum := by decide
  have hdescent : baseEnd_3409647 < baseStart_3409647 := by decide
  rcases family_descends (prefixWord ++ tailWord_3409647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3409664 : List Nat := [2, 1, 1, 2, 1, 1, 2, 8, 1, 2, 2]
def baseStart_3409664 : Nat := 118140960795 + 3409664 * 2 ^ 59
def prefixEnd_3409664 : Nat := 4983230072969 + 3 ^ 40 * 3409664 * 2
def baseEnd_3409664 : Nat := 1750796502331852907619247

theorem tailTrace_3409664 : CollatzResearch.WordTrace tailWord_3409664 prefixEnd_3409664 1750796502331852907619247 := by
  unfold tailWord_3409664
  simp only [CollatzResearch.WordTrace]
  refine ⟨62180331359688563547554023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82907108479584751396738697 62180331359688563547554023)
  ·
    refine ⟨93270497039532845321331035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62180331359688563547554023 93270497039532845321331035)
    ·
      refine ⟨139905745559299267981996553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93270497039532845321331035 139905745559299267981996553)
      ·
        refine ⟨104929309169474450986497415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 139905745559299267981996553 104929309169474450986497415)
        ·
          refine ⟨157393963754211676479746123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104929309169474450986497415 157393963754211676479746123)
          ·
            refine ⟨236090945631317514719619185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 157393963754211676479746123 236090945631317514719619185)
            ·
              refine ⟨177068209223488136039714389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 236090945631317514719619185 177068209223488136039714389)
              ·
                refine ⟨2075018076837751594215403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 177068209223488136039714389 2075018076837751594215403)
                ·
                  refine ⟨3112527115256627391323105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2075018076837751594215403 3112527115256627391323105)
                  ·
                    refine ⟨2334395336442470543492329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3112527115256627391323105 2334395336442470543492329)
                    ·
                      refine ⟨1750796502331852907619247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2334395336442470543492329 1750796502331852907619247)
                      ·
                        rfl

theorem cell23_3409664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 8, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 8, 1, 2, 2].length) (baseStart_3409664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3409664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3409664 prefixEnd_3409664 := by exact prefixLift 3409664
  have htrace : WordTrace (prefixWord ++ tailWord_3409664) baseStart_3409664 baseEnd_3409664 := by
    simpa [prefixWord, tailWord_3409664, baseEnd_3409664] using wordTrace_append hprefix tailTrace_3409664
  have hstable : (prefixWord ++ tailWord_3409664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3409664).length < 2 ^ (prefixWord ++ tailWord_3409664).sum := by decide
  have hdescent : baseEnd_3409664 < baseStart_3409664 := by decide
  rcases family_descends (prefixWord ++ tailWord_3409664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3409714 : List Nat := [3, 2, 1, 1, 3, 2, 3, 2, 2, 1, 3]
def baseStart_3409714 : Nat := 118140960795 + 3409714 * 2 ^ 59
def prefixEnd_3409714 : Nat := 4983230072969 + 3 ^ 40 * 3409714 * 2
def baseEnd_3409714 : Nat := 1750822176364577711994017

theorem tailTrace_3409714 : CollatzResearch.WordTrace tailWord_3409714 prefixEnd_3409714 1750822176364577711994017 := by
  unfold tailWord_3409714
  simp only [CollatzResearch.WordTrace]
  refine ⟨31090621592298996408607049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82908324246130657089618797 31090621592298996408607049)
  ·
    refine ⟨23317966194224247306455287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31090621592298996408607049 23317966194224247306455287)
    ·
      refine ⟨34976949291336370959682931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23317966194224247306455287 34976949291336370959682931)
      ·
        refine ⟨52465423937004556439524397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34976949291336370959682931 52465423937004556439524397)
        ·
          refine ⟨19674533976376708664821649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52465423937004556439524397 19674533976376708664821649)
          ·
            refine ⟨14755900482282531498616237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19674533976376708664821649 14755900482282531498616237)
            ·
              refine ⟨5533462680855949311981089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14755900482282531498616237 5533462680855949311981089)
              ·
                refine ⟨4150097010641961983985817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5533462680855949311981089 4150097010641961983985817)
                ·
                  refine ⟨3112572757981471487989363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4150097010641961983985817 3112572757981471487989363)
                  ·
                    refine ⟨4668859136972207231984045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3112572757981471487989363 4668859136972207231984045)
                    ·
                      refine ⟨1750822176364577711994017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4668859136972207231984045 1750822176364577711994017)
                      ·
                        rfl

theorem cell23_3409714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 3, 2, 2, 1, 3].length) (baseStart_3409714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3409714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3409714 prefixEnd_3409714 := by exact prefixLift 3409714
  have htrace : WordTrace (prefixWord ++ tailWord_3409714) baseStart_3409714 baseEnd_3409714 := by
    simpa [prefixWord, tailWord_3409714, baseEnd_3409714] using wordTrace_append hprefix tailTrace_3409714
  have hstable : (prefixWord ++ tailWord_3409714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3409714).length < 2 ^ (prefixWord ++ tailWord_3409714).sum := by decide
  have hdescent : baseEnd_3409714 < baseStart_3409714 := by decide
  rcases family_descends (prefixWord ++ tailWord_3409714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3409741 : List Nat := [1, 6, 1, 2, 1, 1, 1, 4, 1, 3, 2]
def baseStart_3409741 : Nat := 118140960795 + 3409741 * 2 ^ 59
def prefixEnd_3409741 : Nat := 4983230072969 + 3 ^ 40 * 3409741 * 2
def baseEnd_3409741 : Nat := 1750836040342249106356393

theorem tailTrace_3409741 : CollatzResearch.WordTrace tailWord_3409741 prefixEnd_3409741 1750836040342249106356393 := by
  unfold tailWord_3409741
  simp only [CollatzResearch.WordTrace]
  refine ⟨124363471140098169245661077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82908980760065446163774051 124363471140098169245661077)
  ·
    refine ⟨5829537709692101683390363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 124363471140098169245661077 5829537709692101683390363)
    ·
      refine ⟨8744306564538152525085545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5829537709692101683390363 8744306564538152525085545)
      ·
        refine ⟨6558229923403614393814159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8744306564538152525085545 6558229923403614393814159)
        ·
          refine ⟨9837344885105421590721239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6558229923403614393814159 9837344885105421590721239)
          ·
            refine ⟨14756017327658132386081859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9837344885105421590721239 14756017327658132386081859)
            ·
              refine ⟨22134025991487198579122789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14756017327658132386081859 22134025991487198579122789)
              ·
                refine ⟨4150129873403849733585523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22134025991487198579122789 4150129873403849733585523)
                ·
                  refine ⟨6225194810105774600378285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4150129873403849733585523 6225194810105774600378285)
                  ·
                    refine ⟨2334448053789665475141857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6225194810105774600378285 2334448053789665475141857)
                    ·
                      refine ⟨1750836040342249106356393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2334448053789665475141857 1750836040342249106356393)
                      ·
                        rfl

theorem cell23_3409741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 1, 4, 1, 3, 2].length) (baseStart_3409741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3409741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3409741 prefixEnd_3409741 := by exact prefixLift 3409741
  have htrace : WordTrace (prefixWord ++ tailWord_3409741) baseStart_3409741 baseEnd_3409741 := by
    simpa [prefixWord, tailWord_3409741, baseEnd_3409741] using wordTrace_append hprefix tailTrace_3409741
  have hstable : (prefixWord ++ tailWord_3409741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3409741).length < 2 ^ (prefixWord ++ tailWord_3409741).sum := by decide
  have hdescent : baseEnd_3409741 < baseStart_3409741 := by decide
  rcases family_descends (prefixWord ++ tailWord_3409741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3409827 : List Nat := [1, 1, 1, 4, 1, 2, 1, 4, 2, 4, 2]
def baseStart_3409827 : Nat := 118140960795 + 3409827 * 2 ^ 59
def prefixEnd_3409827 : Nat := 4983230072969 + 3 ^ 40 * 3409827 * 2
def baseEnd_3409827 : Nat := 1750880199678535769880997

theorem tailTrace_3409827 : CollatzResearch.WordTrace tailWord_3409827 prefixEnd_3409827 1750880199678535769880997 := by
  unfold tailWord_3409827
  simp only [CollatzResearch.WordTrace]
  refine ⟨124366607817786605933291735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82911071878524403955527823 124366607817786605933291735)
  ·
    refine ⟨186549911726679908899937603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124366607817786605933291735 186549911726679908899937603)
    ·
      refine ⟨279824867590019863349906405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186549911726679908899937603 279824867590019863349906405)
      ·
        refine ⟨52467162673128724378107451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 279824867590019863349906405 52467162673128724378107451)
        ·
          refine ⟨78700744009693086567161177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52467162673128724378107451 78700744009693086567161177)
          ·
            refine ⟨59025558007269814925370883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78700744009693086567161177 59025558007269814925370883)
            ·
              refine ⟨88538337010904722388056325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59025558007269814925370883 88538337010904722388056325)
              ·
                refine ⟨16600938189544635447760561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 88538337010904722388056325 16600938189544635447760561)
                ·
                  refine ⟨12450703642158476585820421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16600938189544635447760561 12450703642158476585820421)
                  ·
                    refine ⟨2334506932904714359841329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12450703642158476585820421 2334506932904714359841329)
                    ·
                      refine ⟨1750880199678535769880997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2334506932904714359841329 1750880199678535769880997)
                      ·
                        rfl

theorem cell23_3409827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 4, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 4, 2, 4, 2].length) (baseStart_3409827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3409827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3409827 prefixEnd_3409827 := by exact prefixLift 3409827
  have htrace : WordTrace (prefixWord ++ tailWord_3409827) baseStart_3409827 baseEnd_3409827 := by
    simpa [prefixWord, tailWord_3409827, baseEnd_3409827] using wordTrace_append hprefix tailTrace_3409827
  have hstable : (prefixWord ++ tailWord_3409827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3409827).length < 2 ^ (prefixWord ++ tailWord_3409827).sum := by decide
  have hdescent : baseEnd_3409827 < baseStart_3409827 := by decide
  rcases family_descends (prefixWord ++ tailWord_3409827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3409838 : List Nat := [4, 1, 5, 1, 1, 1, 1, 1, 2, 3, 3]
def baseStart_3409838 : Nat := 118140960795 + 3409838 * 2 ^ 59
def prefixEnd_3409838 : Nat := 4983230072969 + 3 ^ 40 * 3409838 * 2
def baseEnd_3409838 : Nat := 1750885847965735226843447

theorem tailTrace_3409838 : CollatzResearch.WordTrace tailWord_3409838 prefixEnd_3409838 1750885847965735226843447 := by
  unfold tailWord_3409838
  simp only [CollatzResearch.WordTrace]
  refine ⟨15545876127593344351492771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 82911339347164503207961445 15545876127593344351492771)
  ·
    refine ⟨23318814191390016527239157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15545876127593344351492771 23318814191390016527239157)
    ·
      refine ⟨2186138830442814049428671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 23318814191390016527239157 2186138830442814049428671)
      ·
        refine ⟨3279208245664221074143007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2186138830442814049428671 3279208245664221074143007)
        ·
          refine ⟨4918812368496331611214511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3279208245664221074143007 4918812368496331611214511)
          ·
            refine ⟨7378218552744497416821767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4918812368496331611214511 7378218552744497416821767)
            ·
              refine ⟨11067327829116746125232651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7378218552744497416821767 11067327829116746125232651)
              ·
                refine ⟨16600991743675119187848977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11067327829116746125232651 16600991743675119187848977)
                ·
                  refine ⟨12450743807756339390886733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16600991743675119187848977 12450743807756339390886733)
                  ·
                    refine ⟨4669028927908627271582525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12450743807756339390886733 4669028927908627271582525)
                    ·
                      refine ⟨1750885847965735226843447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4669028927908627271582525 1750885847965735226843447)
                      ·
                        rfl

theorem cell23_3409838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 1, 1, 2, 3, 3].length) (baseStart_3409838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3409838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3409838 prefixEnd_3409838 := by exact prefixLift 3409838
  have htrace : WordTrace (prefixWord ++ tailWord_3409838) baseStart_3409838 baseEnd_3409838 := by
    simpa [prefixWord, tailWord_3409838, baseEnd_3409838] using wordTrace_append hprefix tailTrace_3409838
  have hstable : (prefixWord ++ tailWord_3409838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3409838).length < 2 ^ (prefixWord ++ tailWord_3409838).sum := by decide
  have hdescent : baseEnd_3409838 < baseStart_3409838 := by decide
  rcases family_descends (prefixWord ++ tailWord_3409838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3409854 : List Nat := [4, 2, 1, 1, 1, 4, 1, 2, 3, 4]
def baseStart_3409854 : Nat := 118140960795 + 3409854 * 2 ^ 59
def prefixEnd_3409854 : Nat := 4983230072969 + 3 ^ 40 * 3409854 * 2
def baseEnd_3409854 : Nat := 583631354552069054747791

theorem tailTrace_3409854 : CollatzResearch.WordTrace tailWord_3409854 prefixEnd_3409854 583631354552069054747791 := by
  unfold tailWord_3409854
  simp only [CollatzResearch.WordTrace]
  refine ⟨15545949073586098693065577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 82911728392459193029683077 15545949073586098693065577)
  ·
    refine ⟨11659461805189574019799183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15545949073586098693065577 11659461805189574019799183)
    ·
      refine ⟨17489192707784361029698775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11659461805189574019799183 17489192707784361029698775)
      ·
        refine ⟨26233789061676541544548163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17489192707784361029698775 26233789061676541544548163)
        ·
          refine ⟨39350683592514812316822245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26233789061676541544548163 39350683592514812316822245)
          ·
            refine ⟨7378253173596527309404171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39350683592514812316822245 7378253173596527309404171)
            ·
              refine ⟨11067379760394790964106257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7378253173596527309404171 11067379760394790964106257)
              ·
                refine ⟨8300534820296093223079693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11067379760394790964106257 8300534820296093223079693)
                ·
                  refine ⟨3112700557611034958654885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8300534820296093223079693 3112700557611034958654885)
                  ·
                    refine ⟨583631354552069054747791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3112700557611034958654885 583631354552069054747791)
                    ·
                      rfl

theorem cell23_3409854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 1, 2, 3, 4].length) (baseStart_3409854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3409854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3409854 prefixEnd_3409854 := by exact prefixLift 3409854
  have htrace : WordTrace (prefixWord ++ tailWord_3409854) baseStart_3409854 baseEnd_3409854 := by
    simpa [prefixWord, tailWord_3409854, baseEnd_3409854] using wordTrace_append hprefix tailTrace_3409854
  have hstable : (prefixWord ++ tailWord_3409854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3409854).length < 2 ^ (prefixWord ++ tailWord_3409854).sum := by decide
  have hdescent : baseEnd_3409854 < baseStart_3409854 := by decide
  rcases family_descends (prefixWord ++ tailWord_3409854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3409864 : List Nat := [2, 1, 3, 1, 4, 1, 3, 1, 2, 2, 3]
def baseStart_3409864 : Nat := 118140960795 + 3409864 * 2 ^ 59
def prefixEnd_3409864 : Nat := 4983230072969 + 3 ^ 40 * 3409864 * 2
def baseEnd_3409864 : Nat := 1750899198462752125118327

theorem tailTrace_3409864 : CollatzResearch.WordTrace tailWord_3409864 prefixEnd_3409864 1750899198462752125118327 := by
  unfold tailWord_3409864
  simp only [CollatzResearch.WordTrace]
  refine ⟨62183978659326280626194323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82911971545768374168259097 62183978659326280626194323)
  ·
    refine ⟨93275967988989420939291485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62183978659326280626194323 93275967988989420939291485)
    ·
      refine ⟨34978487995871032852234307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93275967988989420939291485 34978487995871032852234307)
      ·
        refine ⟨52467731993806549278351461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34978487995871032852234307 52467731993806549278351461)
        ·
          refine ⟨9837699748838727989690899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 52467731993806549278351461 9837699748838727989690899)
          ·
            refine ⟨14756549623258091984536349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9837699748838727989690899 14756549623258091984536349)
            ·
              refine ⟨5533706108721784494201131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14756549623258091984536349 5533706108721784494201131)
              ·
                refine ⟨8300559163082676741301697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5533706108721784494201131 8300559163082676741301697)
                ·
                  refine ⟨6225419372312007555976273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8300559163082676741301697 6225419372312007555976273)
                  ·
                    refine ⟨4669064529234005666982205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6225419372312007555976273 4669064529234005666982205)
                    ·
                      refine ⟨1750899198462752125118327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4669064529234005666982205 1750899198462752125118327)
                      ·
                        rfl

theorem cell23_3409864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 3, 1, 2, 2, 3].length) (baseStart_3409864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3409864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3409864 prefixEnd_3409864 := by exact prefixLift 3409864
  have htrace : WordTrace (prefixWord ++ tailWord_3409864) baseStart_3409864 baseEnd_3409864 := by
    simpa [prefixWord, tailWord_3409864, baseEnd_3409864] using wordTrace_append hprefix tailTrace_3409864
  have hstable : (prefixWord ++ tailWord_3409864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3409864).length < 2 ^ (prefixWord ++ tailWord_3409864).sum := by decide
  have hdescent : baseEnd_3409864 < baseStart_3409864 := by decide
  rcases family_descends (prefixWord ++ tailWord_3409864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3409917 : List Nat := [1, 4, 1, 1, 1, 2, 2, 3, 3, 1, 4]
def baseStart_3409917 : Nat := 118140960795 + 3409917 * 2 ^ 59
def prefixEnd_3409917 : Nat := 4983230072969 + 3 ^ 40 * 3409917 * 2
def baseEnd_3409917 : Nat := 1750926412937440417755583

theorem tailTrace_3409917 : CollatzResearch.WordTrace tailWord_3409917 prefixEnd_3409917 1750926412937440417755583 := by
  unfold tailWord_3409917
  simp only [CollatzResearch.WordTrace]
  refine ⟨124369890387460551304068005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82913260258307034202712003 124369890387460551304068005)
  ·
    refine ⟨23319354447648853369512751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 124369890387460551304068005 23319354447648853369512751)
    ·
      refine ⟨34979031671473280054269127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23319354447648853369512751 34979031671473280054269127)
      ·
        refine ⟨52468547507209920081403691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34979031671473280054269127 52468547507209920081403691)
        ·
          refine ⟨78702821260814880122105537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52468547507209920081403691 78702821260814880122105537)
          ·
            refine ⟨59027115945611160091579153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78702821260814880122105537 59027115945611160091579153)
            ·
              refine ⟨44270336959208370068684365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59027115945611160091579153 44270336959208370068684365)
              ·
                refine ⟨16601376359703138775756637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44270336959208370068684365 16601376359703138775756637)
                ·
                  refine ⟨6225516134888677040908739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16601376359703138775756637 6225516134888677040908739)
                  ·
                    refine ⟨9338274202333015561363109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6225516134888677040908739 9338274202333015561363109)
                    ·
                      refine ⟨1750926412937440417755583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9338274202333015561363109 1750926412937440417755583)
                      ·
                        rfl

theorem cell23_3409917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 3, 3, 1, 4].length) (baseStart_3409917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3409917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3409917 prefixEnd_3409917 := by exact prefixLift 3409917
  have htrace : WordTrace (prefixWord ++ tailWord_3409917) baseStart_3409917 baseEnd_3409917 := by
    simpa [prefixWord, tailWord_3409917, baseEnd_3409917] using wordTrace_append hprefix tailTrace_3409917
  have hstable : (prefixWord ++ tailWord_3409917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3409917).length < 2 ^ (prefixWord ++ tailWord_3409917).sum := by decide
  have hdescent : baseEnd_3409917 < baseStart_3409917 := by decide
  rcases family_descends (prefixWord ++ tailWord_3409917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3409934 : List Nat := [4, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4]
def baseStart_3409934 : Nat := 118140960795 + 3409934 * 2 ^ 59
def prefixEnd_3409934 : Nat := 4983230072969 + 3 ^ 40 * 3409934 * 2
def baseEnd_3409934 : Nat := 1750935142108566851243005

theorem tailTrace_3409934 : CollatzResearch.WordTrace tailWord_3409934 prefixEnd_3409934 1750935142108566851243005 := by
  unfold tailWord_3409934
  simp only [CollatzResearch.WordTrace]
  refine ⟨15546313803549870400929607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 82913673618932642138291237 15546313803549870400929607)
  ·
    refine ⟨23319470705324805601394411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15546313803549870400929607 23319470705324805601394411)
    ·
      refine ⟨34979206057987208402091617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23319470705324805601394411 34979206057987208402091617)
      ·
        refine ⟨26234404543490406301568713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34979206057987208402091617 26234404543490406301568713)
        ·
          refine ⟨19675803407617804726176535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26234404543490406301568713 19675803407617804726176535)
          ·
            refine ⟨29513705111426707089264803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19675803407617804726176535 29513705111426707089264803)
            ·
              refine ⟨44270557667140060633897205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29513705111426707089264803 44270557667140060633897205)
              ·
                refine ⟨4150364781294380684427863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 44270557667140060633897205 4150364781294380684427863)
                ·
                  refine ⟨6225547171941571026641795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4150364781294380684427863 6225547171941571026641795)
                  ·
                    refine ⟨9338320757912356539962693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6225547171941571026641795 9338320757912356539962693)
                    ·
                      refine ⟨1750935142108566851243005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9338320757912356539962693 1750935142108566851243005)
                      ·
                        rfl

theorem cell23_3409934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4].length) (baseStart_3409934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3409934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3409934 prefixEnd_3409934 := by exact prefixLift 3409934
  have htrace : WordTrace (prefixWord ++ tailWord_3409934) baseStart_3409934 baseEnd_3409934 := by
    simpa [prefixWord, tailWord_3409934, baseEnd_3409934] using wordTrace_append hprefix tailTrace_3409934
  have hstable : (prefixWord ++ tailWord_3409934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3409934).length < 2 ^ (prefixWord ++ tailWord_3409934).sum := by decide
  have hdescent : baseEnd_3409934 < baseStart_3409934 := by decide
  rcases family_descends (prefixWord ++ tailWord_3409934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3409937 : List Nat := [1, 2, 2, 1, 1, 2, 1, 1, 7, 2, 3]
def baseStart_3409937 : Nat := 118140960795 + 3409937 * 2 ^ 59
def prefixEnd_3409937 : Nat := 4983230072969 + 3 ^ 40 * 3409937 * 2
def baseEnd_3409937 : Nat := 1750936682550530339505491

theorem tailTrace_3409937 : CollatzResearch.WordTrace tailWord_3409937 prefixEnd_3409937 1750936682550530339505491 := by
  unfold tailWord_3409937
  simp only [CollatzResearch.WordTrace]
  refine ⟨124370619847388094719796065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82913746564925396479864043 124370619847388094719796065)
  ·
    refine ⟨93277964885541071039847049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124370619847388094719796065 93277964885541071039847049)
    ·
      refine ⟨69958473664155803279885287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93277964885541071039847049 69958473664155803279885287)
      ·
        refine ⟨104937710496233704919827931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69958473664155803279885287 104937710496233704919827931)
        ·
          refine ⟨157406565744350557379741897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104937710496233704919827931 157406565744350557379741897)
          ·
            refine ⟨118054924308262918034806423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 157406565744350557379741897 118054924308262918034806423)
            ·
              refine ⟨177082386462394377052209635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 118054924308262918034806423 177082386462394377052209635)
              ·
                refine ⟨265623579693591565578314453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 177082386462394377052209635 265623579693591565578314453)
                ·
                  refine ⟨6225552649068552318241745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 265623579693591565578314453 6225552649068552318241745)
                  ·
                    refine ⟨4669164486801414238681309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6225552649068552318241745 4669164486801414238681309)
                    ·
                      refine ⟨1750936682550530339505491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4669164486801414238681309 1750936682550530339505491)
                      ·
                        rfl

theorem cell23_3409937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 2, 3].length) (baseStart_3409937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3409937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3409937 prefixEnd_3409937 := by exact prefixLift 3409937
  have htrace : WordTrace (prefixWord ++ tailWord_3409937) baseStart_3409937 baseEnd_3409937 := by
    simpa [prefixWord, tailWord_3409937, baseEnd_3409937] using wordTrace_append hprefix tailTrace_3409937
  have hstable : (prefixWord ++ tailWord_3409937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3409937).length < 2 ^ (prefixWord ++ tailWord_3409937).sum := by decide
  have hdescent : baseEnd_3409937 < baseStart_3409937 := by decide
  rcases family_descends (prefixWord ++ tailWord_3409937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3409944 : List Nat := [2, 1, 2, 3, 2, 1, 2, 4, 2, 4]
def baseStart_3409944 : Nat := 118140960795 + 3409944 * 2 ^ 59
def prefixEnd_3409944 : Nat := 4983230072969 + 3 ^ 40 * 3409944 * 2
def baseEnd_3409944 : Nat := 583646758971703937372653

theorem tailTrace_3409944 : CollatzResearch.WordTrace tailWord_3409944 prefixEnd_3409944 583646758971703937372653 := by
  unfold tailWord_3409944
  simp only [CollatzResearch.WordTrace]
  refine ⟨62185437579181367457650443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82913916772241823276867257 62185437579181367457650443)
  ·
    refine ⟨93278156368772051186475665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62185437579181367457650443 93278156368772051186475665)
    ·
      refine ⟨69958617276579038389856749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93278156368772051186475665 69958617276579038389856749)
      ·
        refine ⟨26234481478717139396196281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69958617276579038389856749 26234481478717139396196281)
        ·
          refine ⟨19675861109037854547147211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26234481478717139396196281 19675861109037854547147211)
          ·
            refine ⟨29513791663556781820720817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19675861109037854547147211 29513791663556781820720817)
            ·
              refine ⟨22135343747667586365540613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29513791663556781820720817 22135343747667586365540613)
              ·
                refine ⟨4150376952687672443538865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22135343747667586365540613 4150376952687672443538865)
                ·
                  refine ⟨3112782714515754332654149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4150376952687672443538865 3112782714515754332654149)
                  ·
                    refine ⟨583646758971703937372653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3112782714515754332654149 583646758971703937372653)
                    ·
                      rfl

theorem cell23_3409944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 2, 4, 2, 4].length) (baseStart_3409944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3409944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3409944 prefixEnd_3409944 := by exact prefixLift 3409944
  have htrace : WordTrace (prefixWord ++ tailWord_3409944) baseStart_3409944 baseEnd_3409944 := by
    simpa [prefixWord, tailWord_3409944, baseEnd_3409944] using wordTrace_append hprefix tailTrace_3409944
  have hstable : (prefixWord ++ tailWord_3409944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3409944).length < 2 ^ (prefixWord ++ tailWord_3409944).sum := by decide
  have hdescent : baseEnd_3409944 < baseStart_3409944 := by decide
  rcases family_descends (prefixWord ++ tailWord_3409944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3409954 : List Nat := [3, 3, 1, 1, 1, 2, 2, 2, 3, 2, 3]
def baseStart_3409954 : Nat := 118140960795 + 3409954 * 2 ^ 59
def prefixEnd_3409954 : Nat := 4983230072969 + 3 ^ 40 * 3409954 * 2
def baseEnd_3409954 : Nat := 1750945411721656772992913

theorem tailTrace_3409954 : CollatzResearch.WordTrace tailWord_3409954 prefixEnd_3409954 1750945411721656772992913 := by
  unfold tailWord_3409954
  simp only [CollatzResearch.WordTrace]
  refine ⟨31092809972081626655791229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82914159925551004415443277 31092809972081626655791229)
  ·
    refine ⟨11659803739530609995921711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31092809972081626655791229 11659803739530609995921711)
    ·
      refine ⟨17489705609295914993882567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11659803739530609995921711 17489705609295914993882567)
      ·
        refine ⟨26234558413943872490823851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17489705609295914993882567 26234558413943872490823851)
        ·
          refine ⟨39351837620915808736235777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26234558413943872490823851 39351837620915808736235777)
          ·
            refine ⟨29513878215686856552176833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39351837620915808736235777 29513878215686856552176833)
            ·
              refine ⟨22135408661765142414132625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29513878215686856552176833 22135408661765142414132625)
              ·
                refine ⟨16601556496323856810599469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22135408661765142414132625 16601556496323856810599469)
                ·
                  refine ⟨6225583686121446303974801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16601556496323856810599469 6225583686121446303974801)
                  ·
                    refine ⟨4669187764591084727981101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6225583686121446303974801 4669187764591084727981101)
                    ·
                      refine ⟨1750945411721656772992913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4669187764591084727981101 1750945411721656772992913)
                      ·
                        rfl

theorem cell23_3409954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 2, 2, 3, 2, 3].length) (baseStart_3409954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3409954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3409954 prefixEnd_3409954 := by exact prefixLift 3409954
  have htrace : WordTrace (prefixWord ++ tailWord_3409954) baseStart_3409954 baseEnd_3409954 := by
    simpa [prefixWord, tailWord_3409954, baseEnd_3409954] using wordTrace_append hprefix tailTrace_3409954
  have hstable : (prefixWord ++ tailWord_3409954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3409954).length < 2 ^ (prefixWord ++ tailWord_3409954).sum := by decide
  have hdescent : baseEnd_3409954 < baseStart_3409954 := by decide
  rcases family_descends (prefixWord ++ tailWord_3409954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3409957 : List Nat := [1, 3, 1, 2, 2, 4, 2, 8]
def baseStart_3409957 : Nat := 118140960795 + 3409957 * 2 ^ 59
def prefixEnd_3409957 : Nat := 4983230072969 + 3 ^ 40 * 3409957 * 2
def baseEnd_3409957 : Nat := 64849887117171120787237

theorem tailTrace_3409957 : CollatzResearch.WordTrace tailWord_3409957 prefixEnd_3409957 64849887117171120787237 := by
  unfold tailWord_3409957
  simp only [CollatzResearch.WordTrace]
  refine ⟨124371349307315638135524125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82914232871543758757016083 124371349307315638135524125)
  ·
    refine ⟨46639255990243364300821547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 124371349307315638135524125 46639255990243364300821547)
    ·
      refine ⟨69958883985365046451232321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46639255990243364300821547 69958883985365046451232321)
      ·
        refine ⟨52469162989023784838424241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69958883985365046451232321 52469162989023784838424241)
        ·
          refine ⟨39351872241767838628818181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52469162989023784838424241 39351872241767838628818181)
          ·
            refine ⟨7378476045331469742903409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39351872241767838628818181 7378476045331469742903409)
            ·
              refine ⟨5533857033998602307177557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7378476045331469742903409 5533857033998602307177557)
              ·
                refine ⟨64849887117171120787237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5533857033998602307177557 64849887117171120787237)
                ·
                  rfl

theorem cell23_3409957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 2, 8].length) (baseStart_3409957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3409957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3409957 prefixEnd_3409957 := by exact prefixLift 3409957
  have htrace : WordTrace (prefixWord ++ tailWord_3409957) baseStart_3409957 baseEnd_3409957 := by
    simpa [prefixWord, tailWord_3409957, baseEnd_3409957] using wordTrace_append hprefix tailTrace_3409957
  have hstable : (prefixWord ++ tailWord_3409957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3409957).length < 2 ^ (prefixWord ++ tailWord_3409957).sum := by decide
  have hdescent : baseEnd_3409957 < baseStart_3409957 := by decide
  rcases family_descends (prefixWord ++ tailWord_3409957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3409984 : List Nat := [2, 1, 1, 2, 2, 5, 1, 2, 1, 3, 3]
def baseStart_3409984 : Nat := 118140960795 + 3409984 * 2 ^ 59
def prefixEnd_3409984 : Nat := 4983230072969 + 3 ^ 40 * 3409984 * 2
def baseEnd_3409984 : Nat := 1750960816141291655617775

theorem tailTrace_3409984 : CollatzResearch.WordTrace tailWord_3409984 prefixEnd_3409984 1750960816141291655617775 := by
  unfold tailWord_3409984
  simp only [CollatzResearch.WordTrace]
  refine ⟨62186167039108910873378503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82914889385478547831171337 62186167039108910873378503)
  ·
    refine ⟨93279250558663366310067755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62186167039108910873378503 93279250558663366310067755)
    ·
      refine ⟨139918875837995049465101633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93279250558663366310067755 139918875837995049465101633)
      ·
        refine ⟨104939156878496287098826225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 139918875837995049465101633 104939156878496287098826225)
        ·
          refine ⟨78704367658872215324119669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104939156878496287098826225 78704367658872215324119669)
          ·
            refine ⟨7378534468019270186636219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 78704367658872215324119669 7378534468019270186636219)
            ·
              refine ⟨11067801702028905279954329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7378534468019270186636219 11067801702028905279954329)
              ·
                refine ⟨8300851276521678959965747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11067801702028905279954329 8300851276521678959965747)
                ·
                  refine ⟨12451276914782518439948621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8300851276521678959965747 12451276914782518439948621)
                  ·
                    refine ⟨4669228843043444414980733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12451276914782518439948621 4669228843043444414980733)
                    ·
                      refine ⟨1750960816141291655617775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4669228843043444414980733 1750960816141291655617775)
                      ·
                        rfl

theorem cell23_3409984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 1, 2, 1, 3, 3].length) (baseStart_3409984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3409984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3409984 prefixEnd_3409984 := by exact prefixLift 3409984
  have htrace : WordTrace (prefixWord ++ tailWord_3409984) baseStart_3409984 baseEnd_3409984 := by
    simpa [prefixWord, tailWord_3409984, baseEnd_3409984] using wordTrace_append hprefix tailTrace_3409984
  have hstable : (prefixWord ++ tailWord_3409984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3409984).length < 2 ^ (prefixWord ++ tailWord_3409984).sum := by decide
  have hdescent : baseEnd_3409984 < baseStart_3409984 := by decide
  rcases family_descends (prefixWord ++ tailWord_3409984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3410007 : List Nat := [1, 1, 3, 2, 2, 1, 3, 1, 2, 3, 4]
def baseStart_3410007 : Nat := 118140960795 + 3410007 * 2 ^ 59
def prefixEnd_3410007 : Nat := 4983230072969 + 3 ^ 40 * 3410007 * 2
def baseEnd_3410007 : Nat := 1750972626196345065630169

theorem tailTrace_3410007 : CollatzResearch.WordTrace tailWord_3410007 prefixEnd_3410007 1750972626196345065630169 := by
  unfold tailWord_3410007
  simp only [CollatzResearch.WordTrace]
  refine ⟨124373172957134496674844275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82915448638089664449896183 124373172957134496674844275)
  ·
    refine ⟨186559759435701745012266413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124373172957134496674844275 186559759435701745012266413)
    ·
      refine ⟨69959909788388154379599905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 186559759435701745012266413 69959909788388154379599905)
      ·
        refine ⟨52469932341291115784699929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69959909788388154379599905 52469932341291115784699929)
        ·
          refine ⟨39352449255968336838524947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52469932341291115784699929 39352449255968336838524947)
          ·
            refine ⟨59028673883952505257787421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39352449255968336838524947 59028673883952505257787421)
            ·
              refine ⟨22135752706482189471670283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59028673883952505257787421 22135752706482189471670283)
              ·
                refine ⟨33203629059723284207505425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22135752706482189471670283 33203629059723284207505425)
                ·
                  refine ⟨24902721794792463155629069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33203629059723284207505425 24902721794792463155629069)
                  ·
                    refine ⟨9338520673047173683360901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24902721794792463155629069 9338520673047173683360901)
                    ·
                      refine ⟨1750972626196345065630169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9338520673047173683360901 1750972626196345065630169)
                      ·
                        rfl

theorem cell23_3410007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 3, 1, 2, 3, 4].length) (baseStart_3410007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3410007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3410007 prefixEnd_3410007 := by exact prefixLift 3410007
  have htrace : WordTrace (prefixWord ++ tailWord_3410007) baseStart_3410007 baseEnd_3410007 := by
    simpa [prefixWord, tailWord_3410007, baseEnd_3410007] using wordTrace_append hprefix tailTrace_3410007
  have hstable : (prefixWord ++ tailWord_3410007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3410007).length < 2 ^ (prefixWord ++ tailWord_3410007).sum := by decide
  have hdescent : baseEnd_3410007 < baseStart_3410007 := by decide
  rcases family_descends (prefixWord ++ tailWord_3410007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3410018 : List Nat := [3, 3, 2, 2, 2, 1, 2, 1, 1, 3, 3]
def baseStart_3410018 : Nat := 118140960795 + 3410018 * 2 ^ 59
def prefixEnd_3410018 : Nat := 4983230072969 + 3 ^ 40 * 3410018 * 2
def baseEnd_3410018 : Nat := 1750978274483544522592619

theorem tailTrace_3410018 : CollatzResearch.WordTrace tailWord_3410018 prefixEnd_3410018 1750978274483544522592619 := by
  unfold tailWord_3410018
  simp only [CollatzResearch.WordTrace]
  refine ⟨31093393540023661388373677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82915716106729763702329805 31093393540023661388373677)
  ·
    refine ⟨11660022577508873020640129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31093393540023661388373677 11660022577508873020640129)
    ·
      refine ⟨8745016933131654765480097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11660022577508873020640129 8745016933131654765480097)
      ·
        refine ⟨6558762699848741074110073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8745016933131654765480097 6558762699848741074110073)
        ·
          refine ⟨4919072024886555805582555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6558762699848741074110073 4919072024886555805582555)
          ·
            refine ⟨7378608037329833708373833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4919072024886555805582555 7378608037329833708373833)
            ·
              refine ⟨5533956027997375281280375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7378608037329833708373833 5533956027997375281280375)
              ·
                refine ⟨8300934041996062921920563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5533956027997375281280375 8300934041996062921920563)
                ·
                  refine ⟨12451401062994094382880845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8300934041996062921920563 12451401062994094382880845)
                  ·
                    refine ⟨4669275398622785393580317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12451401062994094382880845 4669275398622785393580317)
                    ·
                      refine ⟨1750978274483544522592619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4669275398622785393580317 1750978274483544522592619)
                      ·
                        rfl

theorem cell23_3410018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 2, 1, 1, 3, 3].length) (baseStart_3410018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3410018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3410018 prefixEnd_3410018 := by exact prefixLift 3410018
  have htrace : WordTrace (prefixWord ++ tailWord_3410018) baseStart_3410018 baseEnd_3410018 := by
    simpa [prefixWord, tailWord_3410018, baseEnd_3410018] using wordTrace_append hprefix tailTrace_3410018
  have hstable : (prefixWord ++ tailWord_3410018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3410018).length < 2 ^ (prefixWord ++ tailWord_3410018).sum := by decide
  have hdescent : baseEnd_3410018 < baseStart_3410018 := by decide
  rcases family_descends (prefixWord ++ tailWord_3410018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3410041 : List Nat := [1, 2, 1, 3, 4, 1, 2, 2, 1, 4, 2]
def baseStart_3410041 : Nat := 118140960795 + 3410041 * 2 ^ 59
def prefixEnd_3410041 : Nat := 4983230072969 + 3 ^ 40 * 3410041 * 2
def baseEnd_3410041 : Nat := 1750990084538597932605013

theorem tailTrace_3410041 : CollatzResearch.WordTrace tailWord_3410041 prefixEnd_3410041 1750990084538597932605013 := by
  unfold tailWord_3410041
  simp only [CollatzResearch.WordTrace]
  refine ⟨124374413039011320481581977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82916275359340880321054651 124374413039011320481581977)
  ·
    refine ⟨93280809779258490361186483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124374413039011320481581977 93280809779258490361186483)
    ·
      refine ⟨139921214668887735541779725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93280809779258490361186483 139921214668887735541779725)
      ·
        refine ⟨52470455500832900828167397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 139921214668887735541779725 52470455500832900828167397)
        ·
          refine ⟨9838210406406168905281387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 52470455500832900828167397 9838210406406168905281387)
          ·
            refine ⟨14757315609609253357922081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9838210406406168905281387 14757315609609253357922081)
            ·
              refine ⟨11067986707206940018441561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14757315609609253357922081 11067986707206940018441561)
              ·
                refine ⟨8300990030405205013831171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11067986707206940018441561 8300990030405205013831171)
                ·
                  refine ⟨12451485045607807520746757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8300990030405205013831171 12451485045607807520746757)
                  ·
                    refine ⟨2334653446051463910140017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12451485045607807520746757 2334653446051463910140017)
                    ·
                      refine ⟨1750990084538597932605013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2334653446051463910140017 1750990084538597932605013)
                      ·
                        rfl

theorem cell23_3410041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 2, 2, 1, 4, 2].length) (baseStart_3410041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3410041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3410041 prefixEnd_3410041 := by exact prefixLift 3410041
  have htrace : WordTrace (prefixWord ++ tailWord_3410041) baseStart_3410041 baseEnd_3410041 := by
    simpa [prefixWord, tailWord_3410041, baseEnd_3410041] using wordTrace_append hprefix tailTrace_3410041
  have hstable : (prefixWord ++ tailWord_3410041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3410041).length < 2 ^ (prefixWord ++ tailWord_3410041).sum := by decide
  have hdescent : baseEnd_3410041 < baseStart_3410041 := by decide
  rcases family_descends (prefixWord ++ tailWord_3410041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3410045 : List Nat := [1, 4, 1, 1, 3, 4, 2, 1, 1, 3, 2]
def baseStart_3410045 : Nat := 118140960795 + 3410045 * 2 ^ 59
def prefixEnd_3410045 : Nat := 4983230072969 + 3 ^ 40 * 3410045 * 2
def baseEnd_3410045 : Nat := 1750992138461215916954995

theorem tailTrace_3410045 : CollatzResearch.WordTrace tailWord_3410045 prefixEnd_3410045 1750992138461215916954995 := by
  unfold tailWord_3410045
  simp only [CollatzResearch.WordTrace]
  refine ⟨124374558930996829164727589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82916372620664552776485059 124374558930996829164727589)
  ·
    refine ⟨23320229799561905468386423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 124374558930996829164727589 23320229799561905468386423)
    ·
      refine ⟨34980344699342858202579635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23320229799561905468386423 34980344699342858202579635)
      ·
        refine ⟨52470517049014287303869453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34980344699342858202579635 52470517049014287303869453)
        ·
          refine ⟨19676443893380357738951045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52470517049014287303869453 19676443893380357738951045)
          ·
            refine ⟨3689333230008817076053321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19676443893380357738951045 3689333230008817076053321)
            ·
              refine ⟨2766999922506612807039991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3689333230008817076053321 2766999922506612807039991)
              ·
                refine ⟨4150499883759919210559987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2766999922506612807039991 4150499883759919210559987)
                ·
                  refine ⟨6225749825639878815839981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4150499883759919210559987 6225749825639878815839981)
                  ·
                    refine ⟨2334656184614954555939993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6225749825639878815839981 2334656184614954555939993)
                    ·
                      refine ⟨1750992138461215916954995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2334656184614954555939993 1750992138461215916954995)
                      ·
                        rfl

theorem cell23_3410045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 4, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 4, 2, 1, 1, 3, 2].length) (baseStart_3410045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3410045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3410045 prefixEnd_3410045 := by exact prefixLift 3410045
  have htrace : WordTrace (prefixWord ++ tailWord_3410045) baseStart_3410045 baseEnd_3410045 := by
    simpa [prefixWord, tailWord_3410045, baseEnd_3410045] using wordTrace_append hprefix tailTrace_3410045
  have hstable : (prefixWord ++ tailWord_3410045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3410045).length < 2 ^ (prefixWord ++ tailWord_3410045).sum := by decide
  have hdescent : baseEnd_3410045 < baseStart_3410045 := by decide
  rcases family_descends (prefixWord ++ tailWord_3410045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3410058 : List Nat := [3, 1, 2, 3, 1, 3, 1, 1, 4, 2, 2]
def baseStart_3410058 : Nat := 118140960795 + 3410058 * 2 ^ 59
def prefixEnd_3410058 : Nat := 4983230072969 + 3 ^ 40 * 3410058 * 2
def baseEnd_3410058 : Nat := 1750998813709724366092435

theorem tailTrace_3410058 : CollatzResearch.WordTrace tailWord_3410058 prefixEnd_3410058 1750998813709724366092435 := by
  unfold tailWord_3410058
  simp only [CollatzResearch.WordTrace]
  refine ⟨31093758269987433096237707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82916688719966488256633885 31093758269987433096237707)
  ·
    refine ⟨46640637404981149644356561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31093758269987433096237707 46640637404981149644356561)
    ·
      refine ⟨34980478053735862233267421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46640637404981149644356561 34980478053735862233267421)
      ·
        refine ⟨13117679270150948337475283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34980478053735862233267421 13117679270150948337475283)
        ·
          refine ⟨19676518905226422506212925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13117679270150948337475283 19676518905226422506212925)
          ·
            refine ⟨7378694589459908439829847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19676518905226422506212925 7378694589459908439829847)
            ·
              refine ⟨11068041884189862659744771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7378694589459908439829847 11068041884189862659744771)
              ·
                refine ⟨16602062826284793989617157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11068041884189862659744771 16602062826284793989617157)
                ·
                  refine ⟨3112886779928398873053217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16602062826284793989617157 3112886779928398873053217)
                  ·
                    refine ⟨2334665084946299154789913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3112886779928398873053217 2334665084946299154789913)
                    ·
                      refine ⟨1750998813709724366092435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2334665084946299154789913 1750998813709724366092435)
                      ·
                        rfl

theorem cell23_3410058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 1, 1, 4, 2, 2].length) (baseStart_3410058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3410058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3410058 prefixEnd_3410058 := by exact prefixLift 3410058
  have htrace : WordTrace (prefixWord ++ tailWord_3410058) baseStart_3410058 baseEnd_3410058 := by
    simpa [prefixWord, tailWord_3410058, baseEnd_3410058] using wordTrace_append hprefix tailTrace_3410058
  have hstable : (prefixWord ++ tailWord_3410058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3410058).length < 2 ^ (prefixWord ++ tailWord_3410058).sum := by decide
  have hdescent : baseEnd_3410058 < baseStart_3410058 := by decide
  rcases family_descends (prefixWord ++ tailWord_3410058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3410064 : List Nat := [2, 1, 1, 1, 1, 1, 5, 6, 5]
def baseStart_3410064 : Nat := 118140960795 + 3410064 * 2 ^ 59
def prefixEnd_3410064 : Nat := 4983230072969 + 3 ^ 40 * 3410064 * 2
def baseEnd_3410064 : Nat := 194555766065961260290823

theorem tailTrace_3410064 : CollatzResearch.WordTrace tailWord_3410064 prefixEnd_3410064 194555766065961260290823 := by
  unfold tailWord_3410064
  simp only [CollatzResearch.WordTrace]
  refine ⟨62187625958963997704834623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82916834611951996939779497 62187625958963997704834623)
  ·
    refine ⟨93281438938445996557251935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62187625958963997704834623 93281438938445996557251935)
    ·
      refine ⟨139922158407668994835877903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93281438938445996557251935 139922158407668994835877903)
      ·
        refine ⟨209883237611503492253816855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139922158407668994835877903 209883237611503492253816855)
        ·
          refine ⟨314824856417255238380725283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 209883237611503492253816855 314824856417255238380725283)
          ·
            refine ⟨472237284625882857571087925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 314824856417255238380725283 472237284625882857571087925)
            ·
              refine ⟨44272245433676517897289493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 472237284625882857571087925 44272245433676517897289493)
              ·
                refine ⟨2075261504703586776435445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 44272245433676517897289493 2075261504703586776435445)
                ·
                  refine ⟨194555766065961260290823, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2075261504703586776435445 194555766065961260290823)
                  ·
                    rfl

theorem cell23_3410064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 6, 5].length) (baseStart_3410064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3410064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3410064 prefixEnd_3410064 := by exact prefixLift 3410064
  have htrace : WordTrace (prefixWord ++ tailWord_3410064) baseStart_3410064 baseEnd_3410064 := by
    simpa [prefixWord, tailWord_3410064, baseEnd_3410064] using wordTrace_append hprefix tailTrace_3410064
  have hstable : (prefixWord ++ tailWord_3410064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3410064).length < 2 ^ (prefixWord ++ tailWord_3410064).sum := by decide
  have hdescent : baseEnd_3410064 < baseStart_3410064 := by decide
  rcases family_descends (prefixWord ++ tailWord_3410064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3410158 : List Nat := [4, 1, 2, 1, 1, 1, 1, 7, 1, 4]
def baseStart_3410158 : Nat := 118140960795 + 3410158 * 2 ^ 59
def prefixEnd_3410158 : Nat := 4983230072969 + 3 ^ 40 * 3410158 * 2
def baseEnd_3410158 : Nat := 583683387258391324947325

theorem tailTrace_3410158 : CollatzResearch.WordTrace tailWord_3410158 prefixEnd_3410158 583683387258391324947325 := by
  unfold tailWord_3410158
  simp only [CollatzResearch.WordTrace]
  refine ⟨15547335047448431182948891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 82919120253058299642394085 15547335047448431182948891)
  ·
    refine ⟨23321002571172646774423337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15547335047448431182948891 23321002571172646774423337)
    ·
      refine ⟨17490751928379485080817503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23321002571172646774423337 17490751928379485080817503)
      ·
        refine ⟨26236127892569227621226255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17490751928379485080817503 26236127892569227621226255)
        ·
          refine ⟨39354191838853841431839383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26236127892569227621226255 39354191838853841431839383)
          ·
            refine ⟨59031287758280762147759075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39354191838853841431839383 59031287758280762147759075)
            ·
              refine ⟨88546931637421143221638613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59031287758280762147759075 88546931637421143221638613)
              ·
                refine ⟨2075318710252058044257155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 88546931637421143221638613 2075318710252058044257155)
                ·
                  refine ⟨3112978065378087066385733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2075318710252058044257155 3112978065378087066385733)
                  ·
                    refine ⟨583683387258391324947325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3112978065378087066385733 583683387258391324947325)
                    ·
                      rfl

theorem cell23_3410158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 7, 1, 4].length) (baseStart_3410158 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3410158 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3410158 prefixEnd_3410158 := by exact prefixLift 3410158
  have htrace : WordTrace (prefixWord ++ tailWord_3410158) baseStart_3410158 baseEnd_3410158 := by
    simpa [prefixWord, tailWord_3410158, baseEnd_3410158] using wordTrace_append hprefix tailTrace_3410158
  have hstable : (prefixWord ++ tailWord_3410158).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3410158).length < 2 ^ (prefixWord ++ tailWord_3410158).sum := by decide
  have hdescent : baseEnd_3410158 < baseStart_3410158 := by decide
  rcases family_descends (prefixWord ++ tailWord_3410158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3410191 : List Nat := [1, 1, 2, 1, 1, 1, 3, 4, 4, 3, 2]
def baseStart_3410191 : Nat := 118140960795 + 3410191 * 2 ^ 59
def prefixEnd_3410191 : Nat := 4983230072969 + 3 ^ 40 * 3410191 * 2
def baseEnd_3410191 : Nat := 1751067106636772345729323

theorem tailTrace_3410191 : CollatzResearch.WordTrace tailWord_3410191 prefixEnd_3410191 1751067106636772345729323 := by
  unfold tailWord_3410191
  simp only [CollatzResearch.WordTrace]
  refine ⟨124379883988467896099542427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82919922658978597399694951 124379883988467896099542427)
  ·
    refine ⟨186569825982701844149313641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124379883988467896099542427 186569825982701844149313641)
    ·
      refine ⟨139927369487026383111985231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 186569825982701844149313641 139927369487026383111985231)
      ·
        refine ⟨209891054230539574667977847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139927369487026383111985231 209891054230539574667977847)
        ·
          refine ⟨314836581345809362001966771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 209891054230539574667977847 314836581345809362001966771)
          ·
            refine ⟨472254872018714043002950157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 314836581345809362001966771 472254872018714043002950157)
            ·
              refine ⟨177095577007017766126106309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 472254872018714043002950157 177095577007017766126106309)
              ·
                refine ⟨33205420688815831148644933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 177095577007017766126106309 33205420688815831148644933)
                ·
                  refine ⟨6226016379152968340370925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33205420688815831148644933 6226016379152968340370925)
                  ·
                    refine ⟨2334756142182363127639097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6226016379152968340370925 2334756142182363127639097)
                    ·
                      refine ⟨1751067106636772345729323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2334756142182363127639097 1751067106636772345729323)
                      ·
                        rfl

theorem cell23_3410191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 4, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 4, 4, 3, 2].length) (baseStart_3410191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3410191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3410191 prefixEnd_3410191 := by exact prefixLift 3410191
  have htrace : WordTrace (prefixWord ++ tailWord_3410191) baseStart_3410191 baseEnd_3410191 := by
    simpa [prefixWord, tailWord_3410191, baseEnd_3410191] using wordTrace_append hprefix tailTrace_3410191
  have hstable : (prefixWord ++ tailWord_3410191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3410191).length < 2 ^ (prefixWord ++ tailWord_3410191).sum := by decide
  have hdescent : baseEnd_3410191 < baseStart_3410191 := by decide
  rcases family_descends (prefixWord ++ tailWord_3410191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3410208 : List Nat := [2, 1, 1, 5, 2, 2, 1, 1, 1, 5, 2]
def baseStart_3410208 : Nat := 118140960795 + 3410208 * 2 ^ 59
def prefixEnd_3410208 : Nat := 4983230072969 + 3 ^ 40 * 3410208 * 2
def baseEnd_3410208 : Nat := 1751075835807898779216745

theorem tailTrace_3410208 : CollatzResearch.WordTrace tailWord_3410208 prefixEnd_3410208 1751075835807898779216745 := by
  unfold tailWord_3410208
  simp only [CollatzResearch.WordTrace]
  refine ⟨62190252014703154001455639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82920336019604205335274185 62190252014703154001455639)
  ·
    refine ⟨93285378022054731002183459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62190252014703154001455639 93285378022054731002183459)
    ·
      refine ⟨139928067033082096503275189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93285378022054731002183459 139928067033082096503275189)
      ·
        refine ⟨13118256284351446547182049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 139928067033082096503275189 13118256284351446547182049)
        ·
          refine ⟨9838692213263584910386537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13118256284351446547182049 9838692213263584910386537)
          ·
            refine ⟨7379019159947688682789903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9838692213263584910386537 7379019159947688682789903)
            ·
              refine ⟨11068528739921533024184855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7379019159947688682789903 11068528739921533024184855)
              ·
                refine ⟨16602793109882299536277283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11068528739921533024184855 16602793109882299536277283)
                ·
                  refine ⟨24904189664823449304415925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16602793109882299536277283 24904189664823449304415925)
                  ·
                    refine ⟨2334767781077198372288993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 24904189664823449304415925 2334767781077198372288993)
                    ·
                      refine ⟨1751075835807898779216745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2334767781077198372288993 1751075835807898779216745)
                      ·
                        rfl

theorem cell23_3410208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 1, 1, 1, 5, 2].length) (baseStart_3410208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3410208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3410208 prefixEnd_3410208 := by exact prefixLift 3410208
  have htrace : WordTrace (prefixWord ++ tailWord_3410208) baseStart_3410208 baseEnd_3410208 := by
    simpa [prefixWord, tailWord_3410208, baseEnd_3410208] using wordTrace_append hprefix tailTrace_3410208
  have hstable : (prefixWord ++ tailWord_3410208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3410208).length < 2 ^ (prefixWord ++ tailWord_3410208).sum := by decide
  have hdescent : baseEnd_3410208 < baseStart_3410208 := by decide
  rcases family_descends (prefixWord ++ tailWord_3410208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3410222 : List Nat := [4, 1, 3, 3, 2, 1, 1, 2, 6]
def baseStart_3410222 : Nat := 118140960795 + 3410222 * 2 ^ 59
def prefixEnd_3410222 : Nat := 4983230072969 + 3 ^ 40 * 3410222 * 2
def baseEnd_3410222 : Nat := 194564780504117969382409

theorem tailTrace_3410222 : CollatzResearch.WordTrace tailWord_3410222 prefixEnd_3410222 194564780504117969382409 := by
  unfold tailWord_3410222
  simp only [CollatzResearch.WordTrace]
  refine ⟨15547626831419448549240115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 82920676434237058929280613 15547626831419448549240115)
  ·
    refine ⟨23321440247129172823860173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15547626831419448549240115 23321440247129172823860173)
    ·
      refine ⟨8745540092673439808947565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23321440247129172823860173 8745540092673439808947565)
      ·
        refine ⟨3279577534752539928355337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8745540092673439808947565 3279577534752539928355337)
        ·
          refine ⟨2459683151064404946266503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3279577534752539928355337 2459683151064404946266503)
          ·
            refine ⟨3689524726596607419399755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2459683151064404946266503 3689524726596607419399755)
            ·
              refine ⟨5534287089894911129099633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3689524726596607419399755 5534287089894911129099633)
              ·
                refine ⟨4150715317421183346824725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5534287089894911129099633 4150715317421183346824725)
                ·
                  refine ⟨194564780504117969382409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4150715317421183346824725 194564780504117969382409)
                  ·
                    rfl

theorem cell23_3410222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 2, 1, 1, 2, 6].length) (baseStart_3410222 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3410222 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3410222 prefixEnd_3410222 := by exact prefixLift 3410222
  have htrace : WordTrace (prefixWord ++ tailWord_3410222) baseStart_3410222 baseEnd_3410222 := by
    simpa [prefixWord, tailWord_3410222, baseEnd_3410222] using wordTrace_append hprefix tailTrace_3410222
  have hstable : (prefixWord ++ tailWord_3410222).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3410222).length < 2 ^ (prefixWord ++ tailWord_3410222).sum := by decide
  have hdescent : baseEnd_3410222 < baseStart_3410222 := by decide
  rcases family_descends (prefixWord ++ tailWord_3410222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3410258 : List Nat := [3, 2, 2, 1, 1, 1, 3, 4, 1, 2, 3]
def baseStart_3410258 : Nat := 118140960795 + 3410258 * 2 ^ 59
def prefixEnd_3410258 : Nat := 4983230072969 + 3 ^ 40 * 3410258 * 2
def baseEnd_3410258 : Nat := 1751101509840623583591515

theorem tailTrace_3410258 : CollatzResearch.WordTrace tailWord_3410258 prefixEnd_3410258 1751101509840623583591515 := by
  unfold tailWord_3410258
  simp only [CollatzResearch.WordTrace]
  refine ⟨31095581919806291635557857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82921551786150111028154285 31095581919806291635557857)
  ·
    refine ⟨23321686439854718726668393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31095581919806291635557857 23321686439854718726668393)
    ·
      refine ⟨17491264829891039045001295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23321686439854718726668393 17491264829891039045001295)
      ·
        refine ⟨26236897244836558567501943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17491264829891039045001295 26236897244836558567501943)
        ·
          refine ⟨39355345867254837851252915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26236897244836558567501943 39355345867254837851252915)
          ·
            refine ⟨59033018800882256776879373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39355345867254837851252915 59033018800882256776879373)
            ·
              refine ⟨22137382050330846291329765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59033018800882256776879373 22137382050330846291329765)
              ·
                refine ⟨4150759134437033679624331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22137382050330846291329765 4150759134437033679624331)
                ·
                  refine ⟨6226138701655550519436497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4150759134437033679624331 6226138701655550519436497)
                  ·
                    refine ⟨4669604026241662889577373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6226138701655550519436497 4669604026241662889577373)
                    ·
                      refine ⟨1751101509840623583591515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4669604026241662889577373 1751101509840623583591515)
                      ·
                        rfl

theorem cell23_3410258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 3, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 3, 4, 1, 2, 3].length) (baseStart_3410258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3410258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3410258 prefixEnd_3410258 := by exact prefixLift 3410258
  have htrace : WordTrace (prefixWord ++ tailWord_3410258) baseStart_3410258 baseEnd_3410258 := by
    simpa [prefixWord, tailWord_3410258, baseEnd_3410258] using wordTrace_append hprefix tailTrace_3410258
  have hstable : (prefixWord ++ tailWord_3410258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3410258).length < 2 ^ (prefixWord ++ tailWord_3410258).sum := by decide
  have hdescent : baseEnd_3410258 < baseStart_3410258 := by decide
  rcases family_descends (prefixWord ++ tailWord_3410258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3410261 : List Nat := [1, 3, 2, 2, 4, 1, 1, 9]
def baseStart_3410261 : Nat := 118140960795 + 3410261 * 2 ^ 59
def prefixEnd_3410261 : Nat := 4983230072969 + 3 ^ 40 * 3410261 * 2
def baseEnd_3410261 : Nat := 64855668528984706364963

theorem tailTrace_3410261 : CollatzResearch.WordTrace tailWord_3410261 prefixEnd_3410261 64855668528984706364963 := by
  unfold tailWord_3410261
  simp only [CollatzResearch.WordTrace]
  refine ⟨124382437098214298054590637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82921624732142865369727091 124382437098214298054590637)
  ·
    refine ⟨46643413911830361770471489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 124382437098214298054590637 46643413911830361770471489)
    ·
      refine ⟨34982560433872771327853617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46643413911830361770471489 34982560433872771327853617)
      ·
        refine ⟨26236920325404578495890213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34982560433872771327853617 26236920325404578495890213)
        ·
          refine ⟨4919422561013358467979415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26236920325404578495890213 4919422561013358467979415)
          ·
            refine ⟨7379133841520037701969123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4919422561013358467979415 7379133841520037701969123)
            ·
              refine ⟨11068700762280056552953685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7379133841520037701969123 11068700762280056552953685)
              ·
                refine ⟨64855668528984706364963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 11068700762280056552953685 64855668528984706364963)
                ·
                  rfl

theorem cell23_3410261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 1, 9].length) (baseStart_3410261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3410261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3410261 prefixEnd_3410261 := by exact prefixLift 3410261
  have htrace : WordTrace (prefixWord ++ tailWord_3410261) baseStart_3410261 baseEnd_3410261 := by
    simpa [prefixWord, tailWord_3410261, baseEnd_3410261] using wordTrace_append hprefix tailTrace_3410261
  have hstable : (prefixWord ++ tailWord_3410261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3410261).length < 2 ^ (prefixWord ++ tailWord_3410261).sum := by decide
  have hdescent : baseEnd_3410261 < baseStart_3410261 := by decide
  rcases family_descends (prefixWord ++ tailWord_3410261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3410271 : List Nat := [1, 1, 2, 3, 1, 2, 2, 4, 1, 3, 3]
def baseStart_3410271 : Nat := 118140960795 + 3410271 * 2 ^ 59
def prefixEnd_3410271 : Nat := 4983230072969 + 3 ^ 40 * 3410271 * 2
def baseEnd_3410271 : Nat := 1751108185089132032728955

theorem tailTrace_3410271 : CollatzResearch.WordTrace tailWord_3410271 prefixEnd_3410271 1751108185089132032728955 := by
  unfold tailWord_3410271
  simp only [CollatzResearch.WordTrace]
  refine ⟨124382801828178069762454667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82921867885452046508303111 124382801828178069762454667)
  ·
    refine ⟨186574202742267104643682001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124382801828178069762454667 186574202742267104643682001)
    ·
      refine ⟨139930652056700328482761501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 186574202742267104643682001 139930652056700328482761501)
      ·
        refine ⟨52473994521262623181035563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 139930652056700328482761501 52473994521262623181035563)
        ·
          refine ⟨78710991781893934771553345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52473994521262623181035563 78710991781893934771553345)
          ·
            refine ⟨59033243836420451078665009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78710991781893934771553345 59033243836420451078665009)
            ·
              refine ⟨44274932877315338308998757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59033243836420451078665009 44274932877315338308998757)
              ·
                refine ⟨8301549914496625932937267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 44274932877315338308998757 8301549914496625932937267)
                ·
                  refine ⟨12452324871744938899405901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8301549914496625932937267 12452324871744938899405901)
                  ·
                    refine ⟨4669621826904352087277213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12452324871744938899405901 4669621826904352087277213)
                    ·
                      refine ⟨1751108185089132032728955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4669621826904352087277213 1751108185089132032728955)
                      ·
                        rfl

theorem cell23_3410271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 4, 1, 3, 3].length) (baseStart_3410271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3410271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3410271 prefixEnd_3410271 := by exact prefixLift 3410271
  have htrace : WordTrace (prefixWord ++ tailWord_3410271) baseStart_3410271 baseEnd_3410271 := by
    simpa [prefixWord, tailWord_3410271, baseEnd_3410271] using wordTrace_append hprefix tailTrace_3410271
  have hstable : (prefixWord ++ tailWord_3410271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3410271).length < 2 ^ (prefixWord ++ tailWord_3410271).sum := by decide
  have hdescent : baseEnd_3410271 < baseStart_3410271 := by decide
  rcases family_descends (prefixWord ++ tailWord_3410271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3410288 : List Nat := [2, 1, 1, 1, 4, 3, 2, 1, 4, 1, 3]
def baseStart_3410288 : Nat := 118140960795 + 3410288 * 2 ^ 59
def prefixEnd_3410288 : Nat := 4983230072969 + 3 ^ 40 * 3410288 * 2
def baseEnd_3410288 : Nat := 1751116914260258466216377

theorem tailTrace_3410288 : CollatzResearch.WordTrace tailWord_3410288 prefixEnd_3410288 1751116914260258466216377 := by
  unfold tailWord_3410288
  simp only [CollatzResearch.WordTrace]
  refine ⟨62191710934558240832911759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82922281246077654443882345 62191710934558240832911759)
  ·
    refine ⟨93287566401837361249367639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62191710934558240832911759 93287566401837361249367639)
    ·
      refine ⟨139931349602756041874051459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93287566401837361249367639 139931349602756041874051459)
      ·
        refine ⟨209897024404134062811077189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139931349602756041874051459 209897024404134062811077189)
        ·
          refine ⟨39355692075775136777076973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 209897024404134062811077189 39355692075775136777076973)
          ·
            refine ⟨14758384528415676291403865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39355692075775136777076973 14758384528415676291403865)
            ·
              refine ⟨11068788396311757218552899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14758384528415676291403865 11068788396311757218552899)
              ·
                refine ⟨16603182594467635827829349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11068788396311757218552899 16603182594467635827829349)
                ·
                  refine ⟨3113096736462681717718003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16603182594467635827829349 3113096736462681717718003)
                  ·
                    refine ⟨4669645104694022576577005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3113096736462681717718003 4669645104694022576577005)
                    ·
                      refine ⟨1751116914260258466216377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4669645104694022576577005 1751116914260258466216377)
                      ·
                        rfl

theorem cell23_3410288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 2, 1, 4, 1, 3].length) (baseStart_3410288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3410288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3410288 prefixEnd_3410288 := by exact prefixLift 3410288
  have htrace : WordTrace (prefixWord ++ tailWord_3410288) baseStart_3410288 baseEnd_3410288 := by
    simpa [prefixWord, tailWord_3410288, baseEnd_3410288] using wordTrace_append hprefix tailTrace_3410288
  have hstable : (prefixWord ++ tailWord_3410288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3410288).length < 2 ^ (prefixWord ++ tailWord_3410288).sum := by decide
  have hdescent : baseEnd_3410288 < baseStart_3410288 := by decide
  rcases family_descends (prefixWord ++ tailWord_3410288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3410315 : List Nat := [1, 1, 1, 1, 4, 4, 3, 2, 1, 3, 2]
def baseStart_3410315 : Nat := 118140960795 + 3410315 * 2 ^ 59
def prefixEnd_3410315 : Nat := 4983230072969 + 3 ^ 40 * 3410315 * 2
def baseEnd_3410315 : Nat := 1751130778237929860578753

theorem tailTrace_3410315 : CollatzResearch.WordTrace tailWord_3410315 prefixEnd_3410315 1751130778237929860578753 := by
  unfold tailWord_3410315
  simp only [CollatzResearch.WordTrace]
  refine ⟨124384406640018665277056399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82922937760012443518037599 124384406640018665277056399)
  ·
    refine ⟨186576609960027997915584599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124384406640018665277056399 186576609960027997915584599)
    ·
      refine ⟨279864914940041996873376899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186576609960027997915584599 279864914940041996873376899)
      ·
        refine ⟨419797372410062995310065349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 279864914940041996873376899 419797372410062995310065349)
        ·
          refine ⟨78712007326886811620637253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 419797372410062995310065349 78712007326886811620637253)
          ·
            refine ⟨14758501373791277178869485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 78712007326886811620637253 14758501373791277178869485)
            ·
              refine ⟨5534438015171728942076057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14758501373791277178869485 5534438015171728942076057)
              ·
                refine ⟨4150828511378796706557043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5534438015171728942076057 4150828511378796706557043)
                ·
                  refine ⟨6226242767068195059835565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4150828511378796706557043 6226242767068195059835565)
                  ·
                    refine ⟨2334841037650573147438337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6226242767068195059835565 2334841037650573147438337)
                    ·
                      refine ⟨1751130778237929860578753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2334841037650573147438337 1751130778237929860578753)
                      ·
                        rfl

theorem cell23_3410315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 3, 2, 1, 3, 2].length) (baseStart_3410315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3410315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3410315 prefixEnd_3410315 := by exact prefixLift 3410315
  have htrace : WordTrace (prefixWord ++ tailWord_3410315) baseStart_3410315 baseEnd_3410315 := by
    simpa [prefixWord, tailWord_3410315, baseEnd_3410315] using wordTrace_append hprefix tailTrace_3410315
  have hstable : (prefixWord ++ tailWord_3410315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3410315).length < 2 ^ (prefixWord ++ tailWord_3410315).sum := by decide
  have hdescent : baseEnd_3410315 < baseStart_3410315 := by decide
  rcases family_descends (prefixWord ++ tailWord_3410315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3410326 : List Nat := [5, 3, 1, 2, 2, 1, 1, 1, 1, 1, 5]
def baseStart_3410326 : Nat := 118140960795 + 3410326 * 2 ^ 59
def prefixEnd_3410326 : Nat := 4983230072969 + 3 ^ 40 * 3410326 * 2
def baseEnd_3410326 : Nat := 1751136426525129317541203

theorem tailTrace_3410326 : CollatzResearch.WordTrace tailWord_3410326 prefixEnd_3410326 1751136426525129317541203 := by
  unfold tailWord_3410326
  simp only [CollatzResearch.WordTrace]
  refine ⟨7774050490186175884731677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 82923205228652542770471221 7774050490186175884731677)
  ·
    refine ⟨2915268933819815956774379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7774050490186175884731677 2915268933819815956774379)
    ·
      refine ⟨4372903400729723935161569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2915268933819815956774379 4372903400729723935161569)
      ·
        refine ⟨3279677550547292951371177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4372903400729723935161569 3279677550547292951371177)
        ·
          refine ⟨2459758162910469713528383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3279677550547292951371177 2459758162910469713528383)
          ·
            refine ⟨3689637244365704570292575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2459758162910469713528383 3689637244365704570292575)
            ·
              refine ⟨5534455866548556855438863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3689637244365704570292575 5534455866548556855438863)
              ·
                refine ⟨8301683799822835283158295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5534455866548556855438863 8301683799822835283158295)
                ·
                  refine ⟨12452525699734252924737443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8301683799822835283158295 12452525699734252924737443)
                  ·
                    refine ⟨18678788549601379387106165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12452525699734252924737443 18678788549601379387106165)
                    ·
                      refine ⟨1751136426525129317541203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18678788549601379387106165 1751136426525129317541203)
                      ·
                        rfl

theorem cell23_3410326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 2, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 2, 1, 1, 1, 1, 1, 5].length) (baseStart_3410326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3410326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3410326 prefixEnd_3410326 := by exact prefixLift 3410326
  have htrace : WordTrace (prefixWord ++ tailWord_3410326) baseStart_3410326 baseEnd_3410326 := by
    simpa [prefixWord, tailWord_3410326, baseEnd_3410326] using wordTrace_append hprefix tailTrace_3410326
  have hstable : (prefixWord ++ tailWord_3410326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3410326).length < 2 ^ (prefixWord ++ tailWord_3410326).sum := by decide
  have hdescent : baseEnd_3410326 < baseStart_3410326 := by decide
  rcases family_descends (prefixWord ++ tailWord_3410326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3410341 : List Nat := [1, 3, 1, 2, 1, 1, 4, 2, 2, 2, 4]
def baseStart_3410341 : Nat := 118140960795 + 3410341 * 2 ^ 59
def prefixEnd_3410341 : Nat := 4983230072969 + 3 ^ 40 * 3410341 * 2
def baseEnd_3410341 : Nat := 1751144128734946758853633

theorem tailTrace_3410341 : CollatzResearch.WordTrace tailWord_3410341 prefixEnd_3410341 1751144128734946758853633 := by
  unfold tailWord_3410341
  simp only [CollatzResearch.WordTrace]
  refine ⟨124385354937924471717502877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82923569958616314478335251 124385354937924471717502877)
  ·
    refine ⟨46644508101721676894063579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 124385354937924471717502877 46644508101721676894063579)
    ·
      refine ⟨69966762152582515341095369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46644508101721676894063579 69966762152582515341095369)
      ·
        refine ⟨52475071614436886505821527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69966762152582515341095369 52475071614436886505821527)
        ·
          refine ⟨78712607421655329758732291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52475071614436886505821527 78712607421655329758732291)
          ·
            refine ⟨118068911132482994638098437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78712607421655329758732291 118068911132482994638098437)
            ·
              refine ⟨22137920837340561494643457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 118068911132482994638098437 22137920837340561494643457)
              ·
                refine ⟨16603440628005421120982593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22137920837340561494643457 16603440628005421120982593)
                ·
                  refine ⟨12452580471004065840736945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16603440628005421120982593 12452580471004065840736945)
                  ·
                    refine ⟨9339435353253049380552709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12452580471004065840736945 9339435353253049380552709)
                    ·
                      refine ⟨1751144128734946758853633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9339435353253049380552709 1751144128734946758853633)
                      ·
                        rfl

theorem cell23_3410341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 4, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 4, 2, 2, 2, 4].length) (baseStart_3410341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3410341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3410341 prefixEnd_3410341 := by exact prefixLift 3410341
  have htrace : WordTrace (prefixWord ++ tailWord_3410341) baseStart_3410341 baseEnd_3410341 := by
    simpa [prefixWord, tailWord_3410341, baseEnd_3410341] using wordTrace_append hprefix tailTrace_3410341
  have hstable : (prefixWord ++ tailWord_3410341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3410341).length < 2 ^ (prefixWord ++ tailWord_3410341).sum := by decide
  have hdescent : baseEnd_3410341 < baseStart_3410341 := by decide
  rcases family_descends (prefixWord ++ tailWord_3410341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3410402 : List Nat := [3, 3, 3, 2, 1, 1, 2, 1, 7]
def baseStart_3410402 : Nat := 118140960795 + 3410402 * 2 ^ 59
def prefixEnd_3410402 : Nat := 4983230072969 + 3 ^ 40 * 3410402 * 2
def baseEnd_3410402 : Nat := 194575050117207891132317

theorem tailTrace_3410402 : CollatzResearch.WordTrace tailWord_3410402 prefixEnd_3410402 194575050117207891132317 := by
  unfold tailWord_3410402
  simp only [CollatzResearch.WordTrace]
  refine ⟨31096894947675869783868365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82925053193802319423648973 31096894947675869783868365)
  ·
    refine ⟨11661335605378451168950637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31096894947675869783868365 11661335605378451168950637)
    ·
      refine ⟨4373000852016919188356489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11661335605378451168950637 4373000852016919188356489)
      ·
        refine ⟨3279750639012689391267367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4373000852016919188356489 3279750639012689391267367)
        ·
          refine ⟨4919625958519034086901051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3279750639012689391267367 4919625958519034086901051)
          ·
            refine ⟨7379438937778551130351577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4919625958519034086901051 7379438937778551130351577)
            ·
              refine ⟨5534579203333913347763683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7379438937778551130351577 5534579203333913347763683)
              ·
                refine ⟨8301868805000870021645525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5534579203333913347763683 8301868805000870021645525)
                ·
                  refine ⟨194575050117207891132317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8301868805000870021645525 194575050117207891132317)
                  ·
                    rfl

theorem cell23_3410402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 2, 1, 7].length) (baseStart_3410402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3410402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3410402 prefixEnd_3410402 := by exact prefixLift 3410402
  have htrace : WordTrace (prefixWord ++ tailWord_3410402) baseStart_3410402 baseEnd_3410402 := by
    simpa [prefixWord, tailWord_3410402, baseEnd_3410402] using wordTrace_append hprefix tailTrace_3410402
  have hstable : (prefixWord ++ tailWord_3410402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3410402).length < 2 ^ (prefixWord ++ tailWord_3410402).sum := by decide
  have hdescent : baseEnd_3410402 < baseStart_3410402 := by decide
  rcases family_descends (prefixWord ++ tailWord_3410402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3410431 : List Nat := [1, 1, 2, 2, 1, 2, 3, 1, 2, 4, 4]
def baseStart_3410431 : Nat := 118140960795 + 3410431 * 2 ^ 59
def prefixEnd_3410431 : Nat := 4983230072969 + 3 ^ 40 * 3410431 * 2
def baseEnd_3410431 : Nat := 1751190341993851406728219

theorem tailTrace_3410431 : CollatzResearch.WordTrace tailWord_3410431 prefixEnd_3410431 1751190341993851406728219 := by
  unfold tailWord_3410431
  simp only [CollatzResearch.WordTrace]
  refine ⟨124388637507598417088279147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82925758338398944725519431 124388637507598417088279147)
  ·
    refine ⟨186582956261397625632418721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124388637507598417088279147 186582956261397625632418721)
    ·
      refine ⟨139937217196048219224314041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 186582956261397625632418721 139937217196048219224314041)
      ·
        refine ⟨104952912897036164418235531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 139937217196048219224314041 104952912897036164418235531)
        ·
          refine ⟨157429369345554246627353297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104952912897036164418235531 157429369345554246627353297)
          ·
            refine ⟨118072027009165684970514973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 157429369345554246627353297 118072027009165684970514973)
            ·
              refine ⟨44277010128437131863943115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 118072027009165684970514973 44277010128437131863943115)
              ·
                refine ⟨66415515192655697795914673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44277010128437131863943115 66415515192655697795914673)
                ·
                  refine ⟨49811636394491773346936005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 66415515192655697795914673 49811636394491773346936005)
                  ·
                    refine ⟨9339681823967207502550501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 49811636394491773346936005 9339681823967207502550501)
                    ·
                      refine ⟨1751190341993851406728219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9339681823967207502550501 1751190341993851406728219)
                      ·
                        rfl

theorem cell23_3410431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 1, 2, 4, 4].length) (baseStart_3410431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3410431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3410431 prefixEnd_3410431 := by exact prefixLift 3410431
  have htrace : WordTrace (prefixWord ++ tailWord_3410431) baseStart_3410431 baseEnd_3410431 := by
    simpa [prefixWord, tailWord_3410431, baseEnd_3410431] using wordTrace_append hprefix tailTrace_3410431
  have hstable : (prefixWord ++ tailWord_3410431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3410431).length < 2 ^ (prefixWord ++ tailWord_3410431).sum := by decide
  have hdescent : baseEnd_3410431 < baseStart_3410431 := by decide
  rcases family_descends (prefixWord ++ tailWord_3410431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3410452 : List Nat := [2, 4, 3, 1, 1, 2, 1, 2, 2, 1, 4]
def baseStart_3410452 : Nat := 118140960795 + 3410452 * 2 ^ 59
def prefixEnd_3410452 : Nat := 4983230072969 + 3 ^ 40 * 3410452 * 2
def baseEnd_3410452 : Nat := 1751201125087595824565623

theorem tailTrace_3410452 : CollatzResearch.WordTrace tailWord_3410452 prefixEnd_3410452 1751201125087595824565623 := by
  unfold tailWord_3410452
  simp only [CollatzResearch.WordTrace]
  refine ⟨62194701720261168837396805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82926268960348225116529073 62194701720261168837396805)
  ·
    refine ⟨11661506572548969157011901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 62194701720261168837396805 11661506572548969157011901)
    ·
      refine ⟨4373064964705863433879463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11661506572548969157011901 4373064964705863433879463)
      ·
        refine ⟨6559597447058795150819195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4373064964705863433879463 6559597447058795150819195)
        ·
          refine ⟨9839396170588192726228793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6559597447058795150819195 9839396170588192726228793)
          ·
            refine ⟨7379547127941144544671595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9839396170588192726228793 7379547127941144544671595)
            ·
              refine ⟨11069320691911716817007393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7379547127941144544671595 11069320691911716817007393)
              ·
                refine ⟨8301990518933787612755545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11069320691911716817007393 8301990518933787612755545)
                ·
                  refine ⟨6226492889200340709566659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8301990518933787612755545 6226492889200340709566659)
                  ·
                    refine ⟨9339739333800511064349989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6226492889200340709566659 9339739333800511064349989)
                    ·
                      refine ⟨1751201125087595824565623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9339739333800511064349989 1751201125087595824565623)
                      ·
                        rfl

theorem cell23_3410452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 1, 2, 2, 1, 4].length) (baseStart_3410452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3410452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3410452 prefixEnd_3410452 := by exact prefixLift 3410452
  have htrace : WordTrace (prefixWord ++ tailWord_3410452) baseStart_3410452 baseEnd_3410452 := by
    simpa [prefixWord, tailWord_3410452, baseEnd_3410452] using wordTrace_append hprefix tailTrace_3410452
  have hstable : (prefixWord ++ tailWord_3410452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3410452).length < 2 ^ (prefixWord ++ tailWord_3410452).sum := by decide
  have hdescent : baseEnd_3410452 < baseStart_3410452 := by decide
  rcases family_descends (prefixWord ++ tailWord_3410452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3410485 : List Nat := [1, 3, 3, 1, 1, 2, 2, 1, 5, 1, 3]
def baseStart_3410485 : Nat := 118140960795 + 3410485 * 2 ^ 59
def prefixEnd_3410485 : Nat := 4983230072969 + 3 ^ 40 * 3410485 * 2
def baseEnd_3410485 : Nat := 1751218069949194195452971

theorem tailTrace_3410485 : CollatzResearch.WordTrace tailWord_3410485 prefixEnd_3410485 1751218069949194195452971 := by
  unfold tailWord_3410485
  simp only [CollatzResearch.WordTrace]
  refine ⟨124390607049402784310744909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82927071366268522873829939 124390607049402784310744909)
  ·
    refine ⟨46646477643526044116529341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 124390607049402784310744909 46646477643526044116529341)
    ·
      refine ⟨17492429116322266543698503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46646477643526044116529341 17492429116322266543698503)
      ·
        refine ⟨26238643674483399815547755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17492429116322266543698503 26238643674483399815547755)
        ·
          refine ⟨39357965511725099723321633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26238643674483399815547755 39357965511725099723321633)
          ·
            refine ⟨29518474133793824792491225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39357965511725099723321633 29518474133793824792491225)
            ·
              refine ⟨22138855600345368594368419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29518474133793824792491225 22138855600345368594368419)
              ·
                refine ⟨33208283400518052891552629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22138855600345368594368419 33208283400518052891552629)
                ·
                  refine ⟨3113276568798567458583059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 33208283400518052891552629 3113276568798567458583059)
                  ·
                    refine ⟨4669914853197851187874589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3113276568798567458583059 4669914853197851187874589)
                    ·
                      refine ⟨1751218069949194195452971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4669914853197851187874589 1751218069949194195452971)
                      ·
                        rfl

theorem cell23_3410485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 2, 1, 5, 1, 3].length) (baseStart_3410485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3410485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3410485 prefixEnd_3410485 := by exact prefixLift 3410485
  have htrace : WordTrace (prefixWord ++ tailWord_3410485) baseStart_3410485 baseEnd_3410485 := by
    simpa [prefixWord, tailWord_3410485, baseEnd_3410485] using wordTrace_append hprefix tailTrace_3410485
  have hstable : (prefixWord ++ tailWord_3410485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3410485).length < 2 ^ (prefixWord ++ tailWord_3410485).sum := by decide
  have hdescent : baseEnd_3410485 < baseStart_3410485 := by decide
  rcases family_descends (prefixWord ++ tailWord_3410485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3410488 : List Nat := [2, 1, 2, 1, 4, 1, 3, 1, 3, 5]
def baseStart_3410488 : Nat := 118140960795 + 3410488 * 2 ^ 59
def prefixEnd_3410488 : Nat := 4983230072969 + 3 ^ 40 * 3410488 * 2
def baseEnd_3410488 : Nat := 583739870130385894571819

theorem tailTrace_3410488 : CollatzResearch.WordTrace tailWord_3410488 prefixEnd_3410488 583739870130385894571819 := by
  unfold tailWord_3410488
  simp only [CollatzResearch.WordTrace]
  refine ⟨62195358234195957911552059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82927144312261277215402745 62195358234195957911552059)
  ·
    refine ⟨93293037351293936867328089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62195358234195957911552059 93293037351293936867328089)
    ·
      refine ⟨69969778013470452650496067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93293037351293936867328089 69969778013470452650496067)
      ·
        refine ⟨104954667020205678975744101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69969778013470452650496067 104954667020205678975744101)
        ·
          refine ⟨19679000066288564807952019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 104954667020205678975744101 19679000066288564807952019)
          ·
            refine ⟨29518500099432847211928029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19679000066288564807952019 29518500099432847211928029)
            ·
              refine ⟨11069437537287317704473011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29518500099432847211928029 11069437537287317704473011)
              ·
                refine ⟨16604156305930976556709517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11069437537287317704473011 16604156305930976556709517)
                ·
                  refine ⟨6226558614724116208766069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16604156305930976556709517 6226558614724116208766069)
                  ·
                    refine ⟨583739870130385894571819, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6226558614724116208766069 583739870130385894571819)
                    ·
                      rfl

theorem cell23_3410488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 3, 1, 3, 5].length) (baseStart_3410488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3410488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3410488 prefixEnd_3410488 := by exact prefixLift 3410488
  have htrace : WordTrace (prefixWord ++ tailWord_3410488) baseStart_3410488 baseEnd_3410488 := by
    simpa [prefixWord, tailWord_3410488, baseEnd_3410488] using wordTrace_append hprefix tailTrace_3410488
  have hstable : (prefixWord ++ tailWord_3410488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3410488).length < 2 ^ (prefixWord ++ tailWord_3410488).sum := by decide
  have hdescent : baseEnd_3410488 < baseStart_3410488 := by decide
  rcases family_descends (prefixWord ++ tailWord_3410488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3410528 : List Nat := [2, 1, 1, 3, 2, 1, 2, 4, 1, 1, 5]
def baseStart_3410528 : Nat := 118140960795 + 3410528 * 2 ^ 59
def prefixEnd_3410528 : Nat := 4983230072969 + 3 ^ 40 * 3410528 * 2
def baseEnd_3410528 : Nat := 1751240149617337527215273

theorem tailTrace_3410528 : CollatzResearch.WordTrace tailWord_3410528 prefixEnd_3410528 1751240149617337527215273 := by
  unfold tailWord_3410528
  simp only [CollatzResearch.WordTrace]
  refine ⟨62196087694123501327280119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82928116925498001769706825 62196087694123501327280119)
  ·
    refine ⟨93294131541185251990920179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62196087694123501327280119 93294131541185251990920179)
    ·
      refine ⟨139941197311777877986380269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93294131541185251990920179 139941197311777877986380269)
      ·
        refine ⟨52477948991916704244892601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 139941197311777877986380269 52477948991916704244892601)
        ·
          refine ⟨39358461743937528183669451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52477948991916704244892601 39358461743937528183669451)
          ·
            refine ⟨59037692615906292275504177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39358461743937528183669451 59037692615906292275504177)
            ·
              refine ⟨44278269461929719206628133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59037692615906292275504177 44278269461929719206628133)
              ·
                refine ⟨8302175524111822351242775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 44278269461929719206628133 8302175524111822351242775)
                ·
                  refine ⟨12453263286167733526864163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8302175524111822351242775 12453263286167733526864163)
                  ·
                    refine ⟨18679894929251600290296245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12453263286167733526864163 18679894929251600290296245)
                    ·
                      refine ⟨1751240149617337527215273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18679894929251600290296245 1751240149617337527215273)
                      ·
                        rfl

theorem cell23_3410528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 4, 1, 1, 5].length) (baseStart_3410528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3410528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3410528 prefixEnd_3410528 := by exact prefixLift 3410528
  have htrace : WordTrace (prefixWord ++ tailWord_3410528) baseStart_3410528 baseEnd_3410528 := by
    simpa [prefixWord, tailWord_3410528, baseEnd_3410528] using wordTrace_append hprefix tailTrace_3410528
  have hstable : (prefixWord ++ tailWord_3410528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3410528).length < 2 ^ (prefixWord ++ tailWord_3410528).sum := by decide
  have hdescent : baseEnd_3410528 < baseStart_3410528 := by decide
  rcases family_descends (prefixWord ++ tailWord_3410528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3410546 : List Nat := [3, 2, 1, 2, 5, 1, 1, 1, 2, 3, 2]
def baseStart_3410546 : Nat := 118140960795 + 3410546 * 2 ^ 59
def prefixEnd_3410546 : Nat := 4983230072969 + 3 ^ 40 * 3410546 * 2
def baseEnd_3410546 : Nat := 1751249392269118456790191

theorem tailTrace_3410546 : CollatzResearch.WordTrace tailWord_3410546 prefixEnd_3410546 1751249392269118456790191 := by
  unfold tailWord_3410546
  simp only [CollatzResearch.WordTrace]
  refine ⟨31098207975545447932178873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82928554601454527819143661 31098207975545447932178873)
  ·
    refine ⟨23323655981659085949134155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31098207975545447932178873 23323655981659085949134155)
    ·
      refine ⟨34985483972488628923701233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23323655981659085949134155 34985483972488628923701233)
      ·
        refine ⟨26239112979366471692775925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34985483972488628923701233 26239112979366471692775925)
        ·
          refine ⟨2459916841815606721197743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 26239112979366471692775925 2459916841815606721197743)
          ·
            refine ⟨3689875262723410081796615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2459916841815606721197743 3689875262723410081796615)
            ·
              refine ⟨5534812894085115122694923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3689875262723410081796615 5534812894085115122694923)
              ·
                refine ⟨8302219341127672684042385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5534812894085115122694923 8302219341127672684042385)
                ·
                  refine ⟨6226664505845754513031789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8302219341127672684042385 6226664505845754513031789)
                  ·
                    refine ⟨2334999189692157942386921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6226664505845754513031789 2334999189692157942386921)
                    ·
                      refine ⟨1751249392269118456790191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2334999189692157942386921 1751249392269118456790191)
                      ·
                        rfl

theorem cell23_3410546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 5, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 5, 1, 1, 1, 2, 3, 2].length) (baseStart_3410546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3410546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3410546 prefixEnd_3410546 := by exact prefixLift 3410546
  have htrace : WordTrace (prefixWord ++ tailWord_3410546) baseStart_3410546 baseEnd_3410546 := by
    simpa [prefixWord, tailWord_3410546, baseEnd_3410546] using wordTrace_append hprefix tailTrace_3410546
  have hstable : (prefixWord ++ tailWord_3410546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3410546).length < 2 ^ (prefixWord ++ tailWord_3410546).sum := by decide
  have hdescent : baseEnd_3410546 < baseStart_3410546 := by decide
  rcases family_descends (prefixWord ++ tailWord_3410546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3410575 : List Nat := [1, 1, 2, 1, 1, 1, 1, 7, 4, 1, 3]
def baseStart_3410575 : Nat := 118140960795 + 3410575 * 2 ^ 59
def prefixEnd_3410575 : Nat := 4983230072969 + 3 ^ 40 * 3410575 * 2
def baseEnd_3410575 : Nat := 1751264283208098843327557

theorem tailTrace_3410575 : CollatzResearch.WordTrace tailWord_3410575 prefixEnd_3410575 1751264283208098843327557 := by
  unfold tailWord_3410575
  simp only [CollatzResearch.WordTrace]
  refine ⟨124393889619076729681521179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82929259746051153121014119 124393889619076729681521179)
  ·
    refine ⟨186590834428615094522281769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124393889619076729681521179 186590834428615094522281769)
    ·
      refine ⟨139943125821461320891711327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 186590834428615094522281769 139943125821461320891711327)
      ·
        refine ⟨209914688732191981337566991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139943125821461320891711327 209914688732191981337566991)
        ·
          refine ⟨314872033098287972006350487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 209914688732191981337566991 314872033098287972006350487)
          ·
            refine ⟨472308049647431958009525731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 314872033098287972006350487 472308049647431958009525731)
            ·
              refine ⟨708462074471147937014288597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 472308049647431958009525731 708462074471147937014288597)
              ·
                refine ⟨16604579870417529773772389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 708462074471147937014288597 16604579870417529773772389)
                ·
                  refine ⟨3113358725703286832582323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16604579870417529773772389 3113358725703286832582323)
                  ·
                    refine ⟨4670038088554930248873485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3113358725703286832582323 4670038088554930248873485)
                    ·
                      refine ⟨1751264283208098843327557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4670038088554930248873485 1751264283208098843327557)
                      ·
                        rfl

theorem cell23_3410575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 7, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 7, 4, 1, 3].length) (baseStart_3410575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3410575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3410575 prefixEnd_3410575 := by exact prefixLift 3410575
  have htrace : WordTrace (prefixWord ++ tailWord_3410575) baseStart_3410575 baseEnd_3410575 := by
    simpa [prefixWord, tailWord_3410575, baseEnd_3410575] using wordTrace_append hprefix tailTrace_3410575
  have hstable : (prefixWord ++ tailWord_3410575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3410575).length < 2 ^ (prefixWord ++ tailWord_3410575).sum := by decide
  have hdescent : baseEnd_3410575 < baseStart_3410575 := by decide
  rcases family_descends (prefixWord ++ tailWord_3410575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3410586 : List Nat := [3, 1, 1, 6, 1, 1, 3, 1, 2, 4]
def baseStart_3410586 : Nat := 118140960795 + 3410586 * 2 ^ 59
def prefixEnd_3410586 : Nat := 4983230072969 + 3 ^ 40 * 3410586 * 2
def baseEnd_3410586 : Nat := 583756643831766100096669

theorem tailTrace_3410586 : CollatzResearch.WordTrace tailWord_3410586 prefixEnd_3410586 583756643831766100096669 := by
  unfold tailWord_3410586
  simp only [CollatzResearch.WordTrace]
  refine ⟨31098572705509219640042903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82929527214691252373447741 31098572705509219640042903)
  ·
    refine ⟨46647859058263829460064355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31098572705509219640042903 46647859058263829460064355)
    ·
      refine ⟨69971788587395744190096533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46647859058263829460064355 69971788587395744190096533)
      ·
        refine ⟨3279927590034175508910775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 69971788587395744190096533 3279927590034175508910775)
        ·
          refine ⟨4919891385051263263366163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3279927590034175508910775 4919891385051263263366163)
          ·
            refine ⟨7379837077576894895049245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4919891385051263263366163 7379837077576894895049245)
            ·
              refine ⟨2767438904091335585643467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7379837077576894895049245 2767438904091335585643467)
              ·
                refine ⟨4151158356137003378465201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2767438904091335585643467 4151158356137003378465201)
                ·
                  refine ⟨3113368767102752533848901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4151158356137003378465201 3113368767102752533848901)
                  ·
                    refine ⟨583756643831766100096669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3113368767102752533848901 583756643831766100096669)
                    ·
                      rfl

theorem cell23_3410586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 3, 1, 2, 4].length) (baseStart_3410586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3410586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3410586 prefixEnd_3410586 := by exact prefixLift 3410586
  have htrace : WordTrace (prefixWord ++ tailWord_3410586) baseStart_3410586 baseEnd_3410586 := by
    simpa [prefixWord, tailWord_3410586, baseEnd_3410586] using wordTrace_append hprefix tailTrace_3410586
  have hstable : (prefixWord ++ tailWord_3410586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3410586).length < 2 ^ (prefixWord ++ tailWord_3410586).sum := by decide
  have hdescent : baseEnd_3410586 < baseStart_3410586 := by decide
  rcases family_descends (prefixWord ++ tailWord_3410586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3410599 : List Nat := [1, 1, 6, 3, 1, 2, 2, 7]
def baseStart_3410599 : Nat := 118140960795 + 3410599 * 2 ^ 59
def prefixEnd_3410599 : Nat := 4983230072969 + 3 ^ 40 * 3410599 * 2
def baseEnd_3410599 : Nat := 64862096546066916645461

theorem tailTrace_3410599 : CollatzResearch.WordTrace tailWord_3410599 prefixEnd_3410599 64862096546066916645461 := by
  unfold tailWord_3410599
  simp only [CollatzResearch.WordTrace]
  refine ⟨124394764970989781780394851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82929843313993187853596567 124394764970989781780394851)
  ·
    refine ⟨186592147456484672670592277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124394764970989781780394851 186592147456484672670592277)
    ·
      refine ⟨8746506912022719031434013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 186592147456484672670592277 8746506912022719031434013)
      ·
        refine ⟨3279940092008519636787755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8746506912022719031434013 3279940092008519636787755)
        ·
          refine ⟨4919910138012779455181633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3279940092008519636787755 4919910138012779455181633)
          ·
            refine ⟨3689932603509584591386225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4919910138012779455181633 3689932603509584591386225)
            ·
              refine ⟨2767449452632188443539669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3689932603509584591386225 2767449452632188443539669)
              ·
                refine ⟨64862096546066916645461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2767449452632188443539669 64862096546066916645461)
                ·
                  rfl

theorem cell23_3410599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 2, 2, 7].length) (baseStart_3410599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3410599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3410599 prefixEnd_3410599 := by exact prefixLift 3410599
  have htrace : WordTrace (prefixWord ++ tailWord_3410599) baseStart_3410599 baseEnd_3410599 := by
    simpa [prefixWord, tailWord_3410599, baseEnd_3410599] using wordTrace_append hprefix tailTrace_3410599
  have hstable : (prefixWord ++ tailWord_3410599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3410599).length < 2 ^ (prefixWord ++ tailWord_3410599).sum := by decide
  have hdescent : baseEnd_3410599 < baseStart_3410599 := by decide
  rcases family_descends (prefixWord ++ tailWord_3410599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3410605 : List Nat := [1, 5, 2, 1, 1, 2, 1, 1, 2, 2, 5]
def baseStart_3410605 : Nat := 118140960795 + 3410605 * 2 ^ 59
def prefixEnd_3410605 : Nat := 4983230072969 + 3 ^ 40 * 3410605 * 2
def baseEnd_3410605 : Nat := 1751279687627733725952419

theorem tailTrace_3410605 : CollatzResearch.WordTrace tailWord_3410605 prefixEnd_3410605 1751279687627733725952419 := by
  unfold tailWord_3410605
  simp only [CollatzResearch.WordTrace]
  refine ⟨124394983808968044805113269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82929989205978696536742179 124394983808968044805113269)
  ·
    refine ⟨11662029732090754200479369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 124394983808968044805113269 11662029732090754200479369)
    ·
      refine ⟨8746522299068065650359527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11662029732090754200479369 8746522299068065650359527)
      ·
        refine ⟨13119783448602098475539291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8746522299068065650359527 13119783448602098475539291)
        ·
          refine ⟨19679675172903147713308937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13119783448602098475539291 19679675172903147713308937)
          ·
            refine ⟨14759756379677360784981703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19679675172903147713308937 14759756379677360784981703)
            ·
              refine ⟨22139634569516041177472555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14759756379677360784981703 22139634569516041177472555)
              ·
                refine ⟨33209451854274061766208833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22139634569516041177472555 33209451854274061766208833)
                ·
                  refine ⟨24907088890705546324656625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33209451854274061766208833 24907088890705546324656625)
                  ·
                    refine ⟨18680316668029159743492469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24907088890705546324656625 18680316668029159743492469)
                    ·
                      refine ⟨1751279687627733725952419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18680316668029159743492469 1751279687627733725952419)
                      ·
                        rfl

theorem cell23_3410605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 1, 1, 2, 2, 5].length) (baseStart_3410605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3410605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3410605 prefixEnd_3410605 := by exact prefixLift 3410605
  have htrace : WordTrace (prefixWord ++ tailWord_3410605) baseStart_3410605 baseEnd_3410605 := by
    simpa [prefixWord, tailWord_3410605, baseEnd_3410605] using wordTrace_append hprefix tailTrace_3410605
  have hstable : (prefixWord ++ tailWord_3410605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3410605).length < 2 ^ (prefixWord ++ tailWord_3410605).sum := by decide
  have hdescent : baseEnd_3410605 < baseStart_3410605 := by decide
  rcases family_descends (prefixWord ++ tailWord_3410605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3410649 : List Nat := [1, 2, 1, 2, 3, 2, 3, 3, 2, 2, 2]
def baseStart_3410649 : Nat := 118140960795 + 3410649 * 2 ^ 59
def prefixEnd_3410649 : Nat := 4983230072969 + 3 ^ 40 * 3410649 * 2
def baseEnd_3410649 : Nat := 1751302280776531553802217

theorem tailTrace_3410649 : CollatzResearch.WordTrace tailWord_3410649 prefixEnd_3410649 1751302280776531553802217 := by
  unfold tailWord_3410649
  simp only [CollatzResearch.WordTrace]
  refine ⟨124396588620808640319715001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82931059080539093546476667 124396588620808640319715001)
  ·
    refine ⟨93297441465606480239786251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124396588620808640319715001 93297441465606480239786251)
    ·
      refine ⟨139946162198409720359679377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93297441465606480239786251 139946162198409720359679377)
      ·
        refine ⟨104959621648807290269759533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 139946162198409720359679377 104959621648807290269759533)
        ·
          refine ⟨39359858118302733851159825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 104959621648807290269759533 39359858118302733851159825)
          ·
            refine ⟨29519893588727050388369869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39359858118302733851159825 29519893588727050388369869)
            ·
              refine ⟨11069960095772643895638701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29519893588727050388369869 11069960095772643895638701)
              ·
                refine ⟨4151235035914741460864513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11069960095772643895638701 4151235035914741460864513)
                ·
                  refine ⟨3113426276936056095648385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4151235035914741460864513 3113426276936056095648385)
                  ·
                    refine ⟨2335069707702042071736289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3113426276936056095648385 2335069707702042071736289)
                    ·
                      refine ⟨1751302280776531553802217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2335069707702042071736289 1751302280776531553802217)
                      ·
                        rfl

theorem cell23_3410649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 3, 3, 2, 2, 2].length) (baseStart_3410649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3410649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3410649 prefixEnd_3410649 := by exact prefixLift 3410649
  have htrace : WordTrace (prefixWord ++ tailWord_3410649) baseStart_3410649 baseEnd_3410649 := by
    simpa [prefixWord, tailWord_3410649, baseEnd_3410649] using wordTrace_append hprefix tailTrace_3410649
  have hstable : (prefixWord ++ tailWord_3410649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3410649).length < 2 ^ (prefixWord ++ tailWord_3410649).sum := by decide
  have hdescent : baseEnd_3410649 < baseStart_3410649 := by decide
  rcases family_descends (prefixWord ++ tailWord_3410649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3410652 : List Nat := [2, 2, 5, 1, 1, 1, 1, 2, 2, 1, 5]
def baseStart_3410652 : Nat := 118140960795 + 3410652 * 2 ^ 59
def prefixEnd_3410652 : Nat := 4983230072969 + 3 ^ 40 * 3410652 * 2
def baseEnd_3410652 : Nat := 1751303821218495042064703

theorem tailTrace_3410652 : CollatzResearch.WordTrace tailWord_3410652 prefixEnd_3410652 1751303821218495042064703 := by
  unfold tailWord_3410652
  simp only [CollatzResearch.WordTrace]
  refine ⟨62198349019898885916037105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82931132026531847888049473 62198349019898885916037105)
  ·
    refine ⟨46648761764924164437027829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62198349019898885916037105 46648761764924164437027829)
    ·
      refine ⟨4373321415461640415971359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 46648761764924164437027829 4373321415461640415971359)
      ·
        refine ⟨6559982123192460623957039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4373321415461640415971359 6559982123192460623957039)
        ·
          refine ⟨9839973184788690935935559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6559982123192460623957039 9839973184788690935935559)
          ·
            refine ⟨14759959777183036403903339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9839973184788690935935559 14759959777183036403903339)
            ·
              refine ⟨22139939665774554605855009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14759959777183036403903339 22139939665774554605855009)
              ·
                refine ⟨16604954749330915954391257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22139939665774554605855009 16604954749330915954391257)
                ·
                  refine ⟨12453716061998186965793443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16604954749330915954391257 12453716061998186965793443)
                  ·
                    refine ⟨18680574092997280448690165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12453716061998186965793443 18680574092997280448690165)
                    ·
                      refine ⟨1751303821218495042064703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18680574092997280448690165 1751303821218495042064703)
                      ·
                        rfl

theorem cell23_3410652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 1, 2, 2, 1, 5].length) (baseStart_3410652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3410652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3410652 prefixEnd_3410652 := by exact prefixLift 3410652
  have htrace : WordTrace (prefixWord ++ tailWord_3410652) baseStart_3410652 baseEnd_3410652 := by
    simpa [prefixWord, tailWord_3410652, baseEnd_3410652] using wordTrace_append hprefix tailTrace_3410652
  have hstable : (prefixWord ++ tailWord_3410652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3410652).length < 2 ^ (prefixWord ++ tailWord_3410652).sum := by decide
  have hdescent : baseEnd_3410652 < baseStart_3410652 := by decide
  rcases family_descends (prefixWord ++ tailWord_3410652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3410685 : List Nat := [1, 4, 1, 1, 1, 1, 3, 4, 2, 5]
def baseStart_3410685 : Nat := 118140960795 + 3410685 * 2 ^ 59
def prefixEnd_3410685 : Nat := 4983230072969 + 3 ^ 40 * 3410685 * 2
def baseEnd_3410685 : Nat := 583773588693364470984017

theorem tailTrace_3410685 : CollatzResearch.WordTrace tailWord_3410685 prefixEnd_3410685 583773588693364470984017 := by
  unfold tailWord_3410685
  simp only [CollatzResearch.WordTrace]
  refine ⟨124397901648678218468025509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82931934432452145645350339 124397901648678218468025509)
  ·
    refine ⟨23324606559127165962754783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 124397901648678218468025509 23324606559127165962754783)
    ·
      refine ⟨34986909838690748944132175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23324606559127165962754783 34986909838690748944132175)
      ·
        refine ⟨52480364758036123416198263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34986909838690748944132175 52480364758036123416198263)
        ·
          refine ⟨78720547137054185124297395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52480364758036123416198263 78720547137054185124297395)
          ·
            refine ⟨118080820705581277686446093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78720547137054185124297395 118080820705581277686446093)
            ·
              refine ⟨44280307764592979132417285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 118080820705581277686446093 44280307764592979132417285)
              ·
                refine ⟨8302557705861183587328241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 44280307764592979132417285 8302557705861183587328241)
                ·
                  refine ⟨6226918279395887690496181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8302557705861183587328241 6226918279395887690496181)
                  ·
                    refine ⟨583773588693364470984017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6226918279395887690496181 583773588693364470984017)
                    ·
                      rfl

theorem cell23_3410685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 4, 2, 5].length) (baseStart_3410685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3410685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3410685 prefixEnd_3410685 := by exact prefixLift 3410685
  have htrace : WordTrace (prefixWord ++ tailWord_3410685) baseStart_3410685 baseEnd_3410685 := by
    simpa [prefixWord, tailWord_3410685, baseEnd_3410685] using wordTrace_append hprefix tailTrace_3410685
  have hstable : (prefixWord ++ tailWord_3410685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3410685).length < 2 ^ (prefixWord ++ tailWord_3410685).sum := by decide
  have hdescent : baseEnd_3410685 < baseStart_3410685 := by decide
  rcases family_descends (prefixWord ++ tailWord_3410685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3410688 : List Nat := [2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 8]
def baseStart_3410688 : Nat := 118140960795 + 3410688 * 2 ^ 59
def prefixEnd_3410688 : Nat := 4983230072969 + 3 ^ 40 * 3410688 * 2
def baseEnd_3410688 : Nat := 1751322306522056901214537

theorem tailTrace_3410688 : CollatzResearch.WordTrace tailWord_3410688 prefixEnd_3410688 1751322306522056901214537 := by
  unfold tailWord_3410688
  simp only [CollatzResearch.WordTrace]
  refine ⟨62199005533833674990192359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82932007378444899986923145 62199005533833674990192359)
  ·
    refine ⟨93298508300750512485288539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62199005533833674990192359 93298508300750512485288539)
    ·
      refine ⟨139947762451125768727932809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93298508300750512485288539 139947762451125768727932809)
      ·
        refine ⟨104960821838344326545949607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 139947762451125768727932809 104960821838344326545949607)
        ·
          refine ⟨157441232757516489818924411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104960821838344326545949607 157441232757516489818924411)
          ·
            refine ⟨236161849136274734728386617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 157441232757516489818924411 236161849136274734728386617)
            ·
              refine ⟨177121386852206051046289963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 236161849136274734728386617 177121386852206051046289963)
              ·
                refine ⟨265682080278309076569434945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 177121386852206051046289963 265682080278309076569434945)
                ·
                  refine ⟨199261560208731807427076209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 265682080278309076569434945 199261560208731807427076209)
                  ·
                    refine ⟨149446170156548855570307157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 199261560208731807427076209 149446170156548855570307157)
                    ·
                      refine ⟨1751322306522056901214537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 149446170156548855570307157 1751322306522056901214537)
                      ·
                        rfl

theorem cell23_3410688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 8].length) (baseStart_3410688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3410688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3410688 prefixEnd_3410688 := by exact prefixLift 3410688
  have htrace : WordTrace (prefixWord ++ tailWord_3410688) baseStart_3410688 baseEnd_3410688 := by
    simpa [prefixWord, tailWord_3410688, baseEnd_3410688] using wordTrace_append hprefix tailTrace_3410688
  have hstable : (prefixWord ++ tailWord_3410688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3410688).length < 2 ^ (prefixWord ++ tailWord_3410688).sum := by decide
  have hdescent : baseEnd_3410688 < baseStart_3410688 := by decide
  rcases family_descends (prefixWord ++ tailWord_3410688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3410692 : List Nat := [2, 3, 2, 2, 1, 1, 1, 1, 1, 7, 2]
def baseStart_3410692 : Nat := 118140960795 + 3410692 * 2 ^ 59
def prefixEnd_3410692 : Nat := 4983230072969 + 3 ^ 40 * 3410692 * 2
def baseEnd_3410692 : Nat := 1751324360444674885564519

theorem tailTrace_3410692 : CollatzResearch.WordTrace tailWord_3410692 prefixEnd_3410692 1751324360444674885564519 := by
  unfold tailWord_3410692
  simp only [CollatzResearch.WordTrace]
  refine ⟨62199078479826429331765165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82932104639768572442353553 62199078479826429331765165)
  ·
    refine ⟨23324654429934910999411937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62199078479826429331765165 23324654429934910999411937)
    ·
      refine ⟨17493490822451183249558953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23324654429934910999411937 17493490822451183249558953)
      ·
        refine ⟨13120118116838387437169215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17493490822451183249558953 13120118116838387437169215)
        ·
          refine ⟨19680177175257581155753823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13120118116838387437169215 19680177175257581155753823)
          ·
            refine ⟨29520265762886371733630735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19680177175257581155753823 29520265762886371733630735)
            ·
              refine ⟨44280398644329557600446103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29520265762886371733630735 44280398644329557600446103)
              ·
                refine ⟨66420597966494336400669155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44280398644329557600446103 66420597966494336400669155)
                ·
                  refine ⟨99630896949741504601003733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 66420597966494336400669155 99630896949741504601003733)
                  ·
                    refine ⟨2335099147259566514086025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 99630896949741504601003733 2335099147259566514086025)
                    ·
                      refine ⟨1751324360444674885564519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2335099147259566514086025 1751324360444674885564519)
                      ·
                        rfl

theorem cell23_3410692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 1, 1, 7, 2].length) (baseStart_3410692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3410692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3410692 prefixEnd_3410692 := by exact prefixLift 3410692
  have htrace : WordTrace (prefixWord ++ tailWord_3410692) baseStart_3410692 baseEnd_3410692 := by
    simpa [prefixWord, tailWord_3410692, baseEnd_3410692] using wordTrace_append hprefix tailTrace_3410692
  have hstable : (prefixWord ++ tailWord_3410692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3410692).length < 2 ^ (prefixWord ++ tailWord_3410692).sum := by decide
  have hdescent : baseEnd_3410692 < baseStart_3410692 := by decide
  rcases family_descends (prefixWord ++ tailWord_3410692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3410705 : List Nat := [1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 4]
def baseStart_3410705 : Nat := 118140960795 + 3410705 * 2 ^ 59
def prefixEnd_3410705 : Nat := 4983230072969 + 3 ^ 40 * 3410705 * 2
def baseEnd_3410705 : Nat := 1751331035693183334701959

theorem tailTrace_3410705 : CollatzResearch.WordTrace tailWord_3410705 prefixEnd_3410705 1751331035693183334701959 := by
  unfold tailWord_3410705
  simp only [CollatzResearch.WordTrace]
  refine ⟨124398631108605761883753569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82932420739070507922502379 124398631108605761883753569)
  ·
    refine ⟨93298973331454321412815177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124398631108605761883753569 93298973331454321412815177)
    ·
      refine ⟨69974229998590741059611383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93298973331454321412815177 69974229998590741059611383)
      ·
        refine ⟨104961344997886111589417075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69974229998590741059611383 104961344997886111589417075)
        ·
          refine ⟨157442017496829167384125613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104961344997886111589417075 157442017496829167384125613)
          ·
            refine ⟨59040756561310937769047105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 157442017496829167384125613 59040756561310937769047105)
            ·
              refine ⟨44280567420983203326785329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59040756561310937769047105 44280567420983203326785329)
              ·
                refine ⟨33210425565737402495088997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44280567420983203326785329 33210425565737402495088997)
                ·
                  refine ⟨6226954793575762967829187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33210425565737402495088997 6226954793575762967829187)
                  ·
                    refine ⟨9340432190363644451743781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6226954793575762967829187 9340432190363644451743781)
                    ·
                      refine ⟨1751331035693183334701959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9340432190363644451743781 1751331035693183334701959)
                      ·
                        rfl

theorem cell23_3410705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 4].length) (baseStart_3410705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3410705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3410705 prefixEnd_3410705 := by exact prefixLift 3410705
  have htrace : WordTrace (prefixWord ++ tailWord_3410705) baseStart_3410705 baseEnd_3410705 := by
    simpa [prefixWord, tailWord_3410705, baseEnd_3410705] using wordTrace_append hprefix tailTrace_3410705
  have hstable : (prefixWord ++ tailWord_3410705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3410705).length < 2 ^ (prefixWord ++ tailWord_3410705).sum := by decide
  have hdescent : baseEnd_3410705 < baseStart_3410705 := by decide
  rcases family_descends (prefixWord ++ tailWord_3410705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3410722 : List Nat := [3, 3, 1, 1, 2, 3, 1, 1, 1, 3, 4]
def baseStart_3410722 : Nat := 118140960795 + 3410722 * 2 ^ 59
def prefixEnd_3410722 : Nat := 4983230072969 + 3 ^ 40 * 3410722 * 2
def baseEnd_3410722 : Nat := 1751339764864309768189381

theorem tailTrace_3410722 : CollatzResearch.WordTrace tailWord_3410722 prefixEnd_3410722 1751339764864309768189381 := by
  unfold tailWord_3410722
  simp only [CollatzResearch.WordTrace]
  refine ⟨31099812787386043446780605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82932834099696115858081613 31099812787386043446780605)
  ·
    refine ⟨11662429795269766292542727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31099812787386043446780605 11662429795269766292542727)
    ·
      refine ⟨17493644692904649438814091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11662429795269766292542727 17493644692904649438814091)
      ·
        refine ⟨26240467039356974158221137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17493644692904649438814091 26240467039356974158221137)
        ·
          refine ⟨19680350279517730618665853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26240467039356974158221137 19680350279517730618665853)
          ·
            refine ⟨7380131354819148981999695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19680350279517730618665853 7380131354819148981999695)
            ·
              refine ⟨11070197032228723472999543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7380131354819148981999695 11070197032228723472999543)
              ·
                refine ⟨16605295548343085209499315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11070197032228723472999543 16605295548343085209499315)
                ·
                  refine ⟨24907943322514627814248973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16605295548343085209499315 24907943322514627814248973)
                  ·
                    refine ⟨9340478745942985430343365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24907943322514627814248973 9340478745942985430343365)
                    ·
                      refine ⟨1751339764864309768189381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9340478745942985430343365 1751339764864309768189381)
                      ·
                        rfl

theorem cell23_3410722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 1, 1, 1, 3, 4].length) (baseStart_3410722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3410722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3410722 prefixEnd_3410722 := by exact prefixLift 3410722
  have htrace : WordTrace (prefixWord ++ tailWord_3410722) baseStart_3410722 baseEnd_3410722 := by
    simpa [prefixWord, tailWord_3410722, baseEnd_3410722] using wordTrace_append hprefix tailTrace_3410722
  have hstable : (prefixWord ++ tailWord_3410722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3410722).length < 2 ^ (prefixWord ++ tailWord_3410722).sum := by decide
  have hdescent : baseEnd_3410722 < baseStart_3410722 := by decide
  rcases family_descends (prefixWord ++ tailWord_3410722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3410826 : List Nat := [3, 1, 2, 4, 1, 3, 1, 2, 1, 5]
def baseStart_3410826 : Nat := 118140960795 + 3410826 * 2 ^ 59
def prefixEnd_3410826 : Nat := 4983230072969 + 3 ^ 40 * 3410826 * 2
def baseEnd_3410826 : Nat := 583797722284125787096301

theorem tailTrace_3410826 : CollatzResearch.WordTrace tailWord_3410826 prefixEnd_3410826 583797722284125787096301 := by
  unfold tailWord_3410826
  simp only [CollatzResearch.WordTrace]
  refine ⟨31100761085291849887227083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82935362894111599699272221 31100761085291849887227083)
  ·
    refine ⟨46651141627937774830840625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31100761085291849887227083 46651141627937774830840625)
    ·
      refine ⟨34988356220953331123130469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46651141627937774830840625 34988356220953331123130469)
      ·
        refine ⟨6560316791428749585586963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34988356220953331123130469 6560316791428749585586963)
        ·
          refine ⟨9840475187143124378380445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6560316791428749585586963 9840475187143124378380445)
          ·
            refine ⟨3690178195178671641892667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9840475187143124378380445 3690178195178671641892667)
            ·
              refine ⟨5535267292768007462839001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3690178195178671641892667 5535267292768007462839001)
              ·
                refine ⟨4151450469576005597129251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5535267292768007462839001 4151450469576005597129251)
                ·
                  refine ⟨6227175704364008395693877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4151450469576005597129251 6227175704364008395693877)
                  ·
                    refine ⟨583797722284125787096301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6227175704364008395693877 583797722284125787096301)
                    ·
                      rfl

theorem cell23_3410826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 3, 1, 2, 1, 5].length) (baseStart_3410826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3410826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3410826 prefixEnd_3410826 := by exact prefixLift 3410826
  have htrace : WordTrace (prefixWord ++ tailWord_3410826) baseStart_3410826 baseEnd_3410826 := by
    simpa [prefixWord, tailWord_3410826, baseEnd_3410826] using wordTrace_append hprefix tailTrace_3410826
  have hstable : (prefixWord ++ tailWord_3410826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3410826).length < 2 ^ (prefixWord ++ tailWord_3410826).sum := by decide
  have hdescent : baseEnd_3410826 < baseStart_3410826 := by decide
  rcases family_descends (prefixWord ++ tailWord_3410826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3410849 : List Nat := [1, 2, 3, 4, 1, 1, 3, 1, 1, 1, 5]
def baseStart_3410849 : Nat := 118140960795 + 3410849 * 2 ^ 59
def prefixEnd_3410849 : Nat := 4983230072969 + 3 ^ 40 * 3410849 * 2
def baseEnd_3410849 : Nat := 1751404976907430771301297

theorem tailTrace_3410849 : CollatzResearch.WordTrace tailWord_3410849 prefixEnd_3410849 1751404976907430771301297 := by
  unfold tailWord_3410849
  simp only [CollatzResearch.WordTrace]
  refine ⟨124403883220084074476995601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82935922146722716317997067 124403883220084074476995601)
  ·
    refine ⟨93302912415063055857746701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124403883220084074476995601 93302912415063055857746701)
    ·
      refine ⟨34988592155648645946655013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93302912415063055857746701 34988592155648645946655013)
      ·
        refine ⟨6560361029184121114997815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34988592155648645946655013 6560361029184121114997815)
        ·
          refine ⟨9840541543776181672496723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6560361029184121114997815 9840541543776181672496723)
          ·
            refine ⟨14760812315664272508745085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9840541543776181672496723 14760812315664272508745085)
            ·
              refine ⟨5535304618374102190779407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14760812315664272508745085 5535304618374102190779407)
              ·
                refine ⟨8302956927561153286169111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5535304618374102190779407 8302956927561153286169111)
                ·
                  refine ⟨12454435391341729929253667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8302956927561153286169111 12454435391341729929253667)
                  ·
                    refine ⟨18681653087012594893880501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12454435391341729929253667 18681653087012594893880501)
                    ·
                      refine ⟨1751404976907430771301297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18681653087012594893880501 1751404976907430771301297)
                      ·
                        rfl

theorem cell23_3410849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 3, 1, 1, 1, 5].length) (baseStart_3410849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3410849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3410849 prefixEnd_3410849 := by exact prefixLift 3410849
  have htrace : WordTrace (prefixWord ++ tailWord_3410849) baseStart_3410849 baseEnd_3410849 := by
    simpa [prefixWord, tailWord_3410849, baseEnd_3410849] using wordTrace_append hprefix tailTrace_3410849
  have hstable : (prefixWord ++ tailWord_3410849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3410849).length < 2 ^ (prefixWord ++ tailWord_3410849).sum := by decide
  have hdescent : baseEnd_3410849 < baseStart_3410849 := by decide
  rcases family_descends (prefixWord ++ tailWord_3410849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3410892 : List Nat := [2, 2, 1, 4, 1, 1, 2, 1, 2, 2, 5]
def baseStart_3410892 : Nat := 118140960795 + 3410892 * 2 ^ 59
def prefixEnd_3410892 : Nat := 4983230072969 + 3 ^ 40 * 3410892 * 2
def baseEnd_3410892 : Nat := 1751427056575574103063599

theorem tailTrace_3410892 : CollatzResearch.WordTrace tailWord_3410892 prefixEnd_3410892 1751427056575574103063599 := by
  unfold tailWord_3410892
  simp only [CollatzResearch.WordTrace]
  refine ⟨62202725779464146410405465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82936967705952195213873953 62202725779464146410405465)
  ·
    refine ⟨46652044334598109807804099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62202725779464146410405465 46652044334598109807804099)
    ·
      refine ⟨69978066501897164711706149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46652044334598109807804099 69978066501897164711706149)
      ·
        refine ⟨13120887469105718383444903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 69978066501897164711706149 13120887469105718383444903)
        ·
          refine ⟨19681331203658577575167355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13120887469105718383444903 19681331203658577575167355)
          ·
            refine ⟨29521996805487866362751033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19681331203658577575167355 29521996805487866362751033)
            ·
              refine ⟨22141497604115899772063275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29521996805487866362751033 22141497604115899772063275)
              ·
                refine ⟨33212246406173849658094913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22141497604115899772063275 33212246406173849658094913)
                ·
                  refine ⟨24909184804630387243571185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33212246406173849658094913 24909184804630387243571185)
                  ·
                    refine ⟨18681888603472790432678389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24909184804630387243571185 18681888603472790432678389)
                    ·
                      refine ⟨1751427056575574103063599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18681888603472790432678389 1751427056575574103063599)
                      ·
                        rfl

theorem cell23_3410892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 2, 1, 2, 2, 5].length) (baseStart_3410892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3410892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3410892 prefixEnd_3410892 := by exact prefixLift 3410892
  have htrace : WordTrace (prefixWord ++ tailWord_3410892) baseStart_3410892 baseEnd_3410892 := by
    simpa [prefixWord, tailWord_3410892, baseEnd_3410892] using wordTrace_append hprefix tailTrace_3410892
  have hstable : (prefixWord ++ tailWord_3410892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3410892).length < 2 ^ (prefixWord ++ tailWord_3410892).sum := by decide
  have hdescent : baseEnd_3410892 < baseStart_3410892 := by decide
  rcases family_descends (prefixWord ++ tailWord_3410892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3410930 : List Nat := [3, 2, 1, 5, 2, 1, 1, 1, 1, 3, 3]
def baseStart_3410930 : Nat := 118140960795 + 3410930 * 2 ^ 59
def prefixEnd_3410930 : Nat := 4983230072969 + 3 ^ 40 * 3410930 * 2
def baseEnd_3410930 : Nat := 1751446568840444954388425

theorem tailTrace_3410930 : CollatzResearch.WordTrace tailWord_3410930 prefixEnd_3410930 1751446568840444954388425 := by
  unfold tailWord_3410930
  simp only [CollatzResearch.WordTrace]
  refine ⟨31101709383197656327673561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82937891688527083540462829 31101709383197656327673561)
  ·
    refine ⟨23326282037398242245755171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31101709383197656327673561 23326282037398242245755171)
    ·
      refine ⟨34989423056097363368632757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23326282037398242245755171 34989423056097363368632757)
      ·
        refine ⟨3280258411509127815809321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 34989423056097363368632757 3280258411509127815809321)
        ·
          refine ⟨2460193808631845861856991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3280258411509127815809321 2460193808631845861856991)
          ·
            refine ⟨3690290712947768792785487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2460193808631845861856991 3690290712947768792785487)
            ·
              refine ⟨5535436069421653189178231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3690290712947768792785487 5535436069421653189178231)
              ·
                refine ⟨8303154104132479783767347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5535436069421653189178231 8303154104132479783767347)
                ·
                  refine ⟨12454731156198719675651021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8303154104132479783767347 12454731156198719675651021)
                  ·
                    refine ⟨4670524183574519878369133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12454731156198719675651021 4670524183574519878369133)
                    ·
                      refine ⟨1751446568840444954388425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4670524183574519878369133 1751446568840444954388425)
                      ·
                        rfl

theorem cell23_3410930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 2, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 2, 1, 1, 1, 1, 3, 3].length) (baseStart_3410930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3410930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3410930 prefixEnd_3410930 := by exact prefixLift 3410930
  have htrace : WordTrace (prefixWord ++ tailWord_3410930) baseStart_3410930 baseEnd_3410930 := by
    simpa [prefixWord, tailWord_3410930, baseEnd_3410930] using wordTrace_append hprefix tailTrace_3410930
  have hstable : (prefixWord ++ tailWord_3410930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3410930).length < 2 ^ (prefixWord ++ tailWord_3410930).sum := by decide
  have hdescent : baseEnd_3410930 < baseStart_3410930 := by decide
  rcases family_descends (prefixWord ++ tailWord_3410930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3411002 : List Nat := [3, 1, 1, 1, 3, 1, 2, 1, 2, 8]
def baseStart_3411002 : Nat := 118140960795 + 3411002 * 2 ^ 59
def prefixEnd_3411002 : Nat := 4983230072969 + 3 ^ 40 * 3411002 * 2
def baseEnd_3411002 : Nat := 583827846482522890896031

theorem tailTrace_3411002 : CollatzResearch.WordTrace tailWord_3411002 prefixEnd_3411002 583827846482522890896031 := by
  unfold tailWord_3411002
  simp only [CollatzResearch.WordTrace]
  refine ⟨31102365897132445401828815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82939642392353187738210173 31102365897132445401828815)
  ·
    refine ⟨46653548845698668102743223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31102365897132445401828815 46653548845698668102743223)
    ·
      refine ⟨69980323268548002154114835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46653548845698668102743223 69980323268548002154114835)
      ·
        refine ⟨104970484902822003231172253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69980323268548002154114835 104970484902822003231172253)
        ·
          refine ⟨39363931838558251211689595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 104970484902822003231172253 39363931838558251211689595)
          ·
            refine ⟨59045897757837376817534393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39363931838558251211689595 59045897757837376817534393)
            ·
              refine ⟨44284423318378032613150795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59045897757837376817534393 44284423318378032613150795)
              ·
                refine ⟨66426634977567048919726193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44284423318378032613150795 66426634977567048919726193)
                ·
                  refine ⟨49819976233175286689794645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 66426634977567048919726193 49819976233175286689794645)
                  ·
                    refine ⟨583827846482522890896031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 49819976233175286689794645 583827846482522890896031)
                    ·
                      rfl

theorem cell23_3411002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 1, 2, 8].length) (baseStart_3411002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3411002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3411002 prefixEnd_3411002 := by exact prefixLift 3411002
  have htrace : WordTrace (prefixWord ++ tailWord_3411002) baseStart_3411002 baseEnd_3411002 := by
    simpa [prefixWord, tailWord_3411002, baseEnd_3411002] using wordTrace_append hprefix tailTrace_3411002
  have hstable : (prefixWord ++ tailWord_3411002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3411002).length < 2 ^ (prefixWord ++ tailWord_3411002).sum := by decide
  have hdescent : baseEnd_3411002 < baseStart_3411002 := by decide
  rcases family_descends (prefixWord ++ tailWord_3411002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3411006 : List Nat := [4, 2, 1, 3, 1, 1, 1, 3, 2, 5]
def baseStart_3411006 : Nat := 118140960795 + 3411006 * 2 ^ 59
def prefixEnd_3411006 : Nat := 4983230072969 + 3 ^ 40 * 3411006 * 2
def baseEnd_3411006 : Nat := 583828531123395552346025

theorem tailTrace_3411006 : CollatzResearch.WordTrace tailWord_3411006 prefixEnd_3411006 583828531123395552346025 := by
  unfold tailWord_3411006
  simp only [CollatzResearch.WordTrace]
  refine ⟨15551201185064411286307609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 82939739653676860193640581 15551201185064411286307609)
  ·
    refine ⟨11663400888798308464730707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15551201185064411286307609 11663400888798308464730707)
    ·
      refine ⟨17495101333197462697096061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11663400888798308464730707 17495101333197462697096061)
      ·
        refine ⟨6560662999949048511411023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17495101333197462697096061 6560662999949048511411023)
        ·
          refine ⟨9840994499923572767116535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6560662999949048511411023 9840994499923572767116535)
          ·
            refine ⟨14761491749885359150674803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9840994499923572767116535 14761491749885359150674803)
            ·
              refine ⟨22142237624828038726012205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14761491749885359150674803 22142237624828038726012205)
              ·
                refine ⟨8303339109310514522254577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22142237624828038726012205 8303339109310514522254577)
                ·
                  refine ⟨6227504331982885891690933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8303339109310514522254577 6227504331982885891690933)
                  ·
                    refine ⟨583828531123395552346025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6227504331982885891690933 583828531123395552346025)
                    ·
                      rfl

theorem cell23_3411006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 1, 3, 2, 5].length) (baseStart_3411006 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3411006 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3411006 prefixEnd_3411006 := by exact prefixLift 3411006
  have htrace : WordTrace (prefixWord ++ tailWord_3411006) baseStart_3411006 baseEnd_3411006 := by
    simpa [prefixWord, tailWord_3411006, baseEnd_3411006] using wordTrace_append hprefix tailTrace_3411006
  have hstable : (prefixWord ++ tailWord_3411006).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3411006).length < 2 ^ (prefixWord ++ tailWord_3411006).sum := by decide
  have hdescent : baseEnd_3411006 < baseStart_3411006 := by decide
  rcases family_descends (prefixWord ++ tailWord_3411006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3411026 : List Nat := [3, 2, 2, 1, 3, 1, 2, 2, 2, 1, 4]
def baseStart_3411026 : Nat := 118140960795 + 3411026 * 2 ^ 59
def prefixEnd_3411026 : Nat := 4983230072969 + 3 ^ 40 * 3411026 * 2
def baseEnd_3411026 : Nat := 1751495862983276578787983

theorem tailTrace_3411026 : CollatzResearch.WordTrace tailWord_3411026 prefixEnd_3411026 1751495862983276578787983 := by
  unfold tailWord_3411026
  simp only [CollatzResearch.WordTrace]
  refine ⟨31102584735110708426547233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82940225960295222470792621 31102584735110708426547233)
  ·
    refine ⟨23326938551333031319910425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31102584735110708426547233 23326938551333031319910425)
    ·
      refine ⟨17495203913499773489932819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23326938551333031319910425 17495203913499773489932819)
      ·
        refine ⟨26242805870249660234899229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17495203913499773489932819 26242805870249660234899229)
        ·
          refine ⟨9841052201343622588087211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26242805870249660234899229 9841052201343622588087211)
          ·
            refine ⟨14761578302015433882130817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9841052201343622588087211 14761578302015433882130817)
            ·
              refine ⟨11071183726511575411598113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14761578302015433882130817 11071183726511575411598113)
              ·
                refine ⟨8303387794883681558698585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11071183726511575411598113 8303387794883681558698585)
                ·
                  refine ⟨6227540846162761169023939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8303387794883681558698585 6227540846162761169023939)
                  ·
                    refine ⟨9341311269244141753535909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6227540846162761169023939 9341311269244141753535909)
                    ·
                      refine ⟨1751495862983276578787983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9341311269244141753535909 1751495862983276578787983)
                      ·
                        rfl

theorem cell23_3411026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 2, 2, 2, 1, 4].length) (baseStart_3411026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3411026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3411026 prefixEnd_3411026 := by exact prefixLift 3411026
  have htrace : WordTrace (prefixWord ++ tailWord_3411026) baseStart_3411026 baseEnd_3411026 := by
    simpa [prefixWord, tailWord_3411026, baseEnd_3411026] using wordTrace_append hprefix tailTrace_3411026
  have hstable : (prefixWord ++ tailWord_3411026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3411026).length < 2 ^ (prefixWord ++ tailWord_3411026).sum := by decide
  have hdescent : baseEnd_3411026 < baseStart_3411026 := by decide
  rcases family_descends (prefixWord ++ tailWord_3411026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3411036 : List Nat := [2, 2, 4, 1, 1, 1, 2, 3, 3, 4]
def baseStart_3411036 : Nat := 118140960795 + 3411036 * 2 ^ 59
def prefixEnd_3411036 : Nat := 4983230072969 + 3 ^ 40 * 3411036 * 2
def baseEnd_3411036 : Nat := 583833665929940513220979

theorem tailTrace_3411036 : CollatzResearch.WordTrace tailWord_3411036 prefixEnd_3411036 583833665929940513220979 := by
  unfold tailWord_3411036
  simp only [CollatzResearch.WordTrace]
  refine ⟨62205351835203302707026481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82940469113604403609368641 62205351835203302707026481)
  ·
    refine ⟨46654013876402477030269861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62205351835203302707026481 46654013876402477030269861)
    ·
      refine ⟨8747627601825464443175599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 46654013876402477030269861 8747627601825464443175599)
      ·
        refine ⟨13121441402738196664763399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8747627601825464443175599 13121441402738196664763399)
        ·
          refine ⟨19682162104107294997145099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13121441402738196664763399 19682162104107294997145099)
          ·
            refine ⟨29523243156160942495717649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19682162104107294997145099 29523243156160942495717649)
            ·
              refine ⟨22142432367120706871788237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29523243156160942495717649 22142432367120706871788237)
              ·
                refine ⟨8303412137670265076920589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22142432367120706871788237 8303412137670265076920589)
                ·
                  refine ⟨3113779551626349403845221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8303412137670265076920589 3113779551626349403845221)
                  ·
                    refine ⟨583833665929940513220979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3113779551626349403845221 583833665929940513220979)
                    ·
                      rfl

theorem cell23_3411036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 2, 3, 3, 4].length) (baseStart_3411036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3411036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3411036 prefixEnd_3411036 := by exact prefixLift 3411036
  have htrace : WordTrace (prefixWord ++ tailWord_3411036) baseStart_3411036 baseEnd_3411036 := by
    simpa [prefixWord, tailWord_3411036, baseEnd_3411036] using wordTrace_append hprefix tailTrace_3411036
  have hstable : (prefixWord ++ tailWord_3411036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3411036).length < 2 ^ (prefixWord ++ tailWord_3411036).sum := by decide
  have hdescent : baseEnd_3411036 < baseStart_3411036 := by decide
  rcases family_descends (prefixWord ++ tailWord_3411036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3411049 : List Nat := [1, 2, 1, 1, 1, 6, 2, 3, 6]
def baseStart_3411049 : Nat := 118140960795 + 3411049 * 2 ^ 59
def prefixEnd_3411049 : Nat := 4983230072969 + 3 ^ 40 * 3411049 * 2
def baseEnd_3411049 : Nat := 194611963670925554311153

theorem tailTrace_3411049 : CollatzResearch.WordTrace tailWord_3411049 prefixEnd_3411049 194611963670925554311153 := by
  unfold tailWord_3411049
  simp only [CollatzResearch.WordTrace]
  refine ⟨124411177819359508634276201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82940785212906339089517467 124411177819359508634276201)
  ·
    refine ⟨93308383364519631475707151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124411177819359508634276201 93308383364519631475707151)
    ·
      refine ⟨139962575046779447213560727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93308383364519631475707151 139962575046779447213560727)
      ·
        refine ⟨209943862570169170820341091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139962575046779447213560727 209943862570169170820341091)
        ·
          refine ⟨314915793855253756230511637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 209943862570169170820341091 314915793855253756230511637)
          ·
            refine ⟨14761677836965019823305233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 314915793855253756230511637 14761677836965019823305233)
            ·
              refine ⟨11071258377723764867478925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14761677836965019823305233 11071258377723764867478925)
              ·
                refine ⟨4151721891646411825304597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11071258377723764867478925 4151721891646411825304597)
                ·
                  refine ⟨194611963670925554311153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4151721891646411825304597 194611963670925554311153)
                  ·
                    rfl

theorem cell23_3411049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 2, 3, 6].length) (baseStart_3411049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3411049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3411049 prefixEnd_3411049 := by exact prefixLift 3411049
  have htrace : WordTrace (prefixWord ++ tailWord_3411049) baseStart_3411049 baseEnd_3411049 := by
    simpa [prefixWord, tailWord_3411049, baseEnd_3411049] using wordTrace_append hprefix tailTrace_3411049
  have hstable : (prefixWord ++ tailWord_3411049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3411049).length < 2 ^ (prefixWord ++ tailWord_3411049).sum := by decide
  have hdescent : baseEnd_3411049 < baseStart_3411049 := by decide
  rcases family_descends (prefixWord ++ tailWord_3411049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3411133 : List Nat := [1, 4, 1, 2, 1, 1, 2, 2, 5, 2, 2]
def baseStart_3411133 : Nat := 118140960795 + 3411133 * 2 ^ 59
def prefixEnd_3411133 : Nat := 4983230072969 + 3 ^ 40 * 3411133 * 2
def baseEnd_3411133 : Nat := 1751550805413307660149991

theorem tailTrace_3411133 : CollatzResearch.WordTrace tailWord_3411133 prefixEnd_3411133 1751550805413307660149991 := by
  unfold tailWord_3411133
  simp only [CollatzResearch.WordTrace]
  refine ⟨124414241551055190980334053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82942827700703460653556035 124414241551055190980334053)
  ·
    refine ⟨23327670290822848308812635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 124414241551055190980334053 23327670290822848308812635)
    ·
      refine ⟨34991505436234272463218953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23327670290822848308812635 34991505436234272463218953)
      ·
        refine ⟨26243629077175704347414215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34991505436234272463218953 26243629077175704347414215)
        ·
          refine ⟨39365443615763556521121323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26243629077175704347414215 39365443615763556521121323)
          ·
            refine ⟨59048165423645334781681985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39365443615763556521121323 59048165423645334781681985)
            ·
              refine ⟨44286124067734001086261489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59048165423645334781681985 44286124067734001086261489)
              ·
                refine ⟨33214593050800500814696117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44286124067734001086261489 33214593050800500814696117)
                ·
                  refine ⟨3113868098512546951377761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 33214593050800500814696117 3113868098512546951377761)
                  ·
                    refine ⟨2335401073884410213533321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3113868098512546951377761 2335401073884410213533321)
                    ·
                      refine ⟨1751550805413307660149991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2335401073884410213533321 1751550805413307660149991)
                      ·
                        rfl

theorem cell23_3411133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 2, 5, 2, 2].length) (baseStart_3411133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3411133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3411133 prefixEnd_3411133 := by exact prefixLift 3411133
  have htrace : WordTrace (prefixWord ++ tailWord_3411133) baseStart_3411133 baseEnd_3411133 := by
    simpa [prefixWord, tailWord_3411133, baseEnd_3411133] using wordTrace_append hprefix tailTrace_3411133
  have hstable : (prefixWord ++ tailWord_3411133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3411133).length < 2 ^ (prefixWord ++ tailWord_3411133).sum := by decide
  have hdescent : baseEnd_3411133 < baseStart_3411133 := by decide
  rcases family_descends (prefixWord ++ tailWord_3411133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3411183 : List Nat := [1, 1, 2, 1, 7, 1, 1, 2, 1, 3, 3]
def baseStart_3411183 : Nat := 118140960795 + 3411183 * 2 ^ 59
def prefixEnd_3411183 : Nat := 4983230072969 + 3 ^ 40 * 3411183 * 2
def baseEnd_3411183 : Nat := 1751576479446032464524761

theorem tailTrace_3411183 : CollatzResearch.WordTrace tailWord_3411183 prefixEnd_3411183 1751576479446032464524761 := by
  unfold tailWord_3411183
  simp only [CollatzResearch.WordTrace]
  refine ⟨124416065200874049519654203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82944043467249366346436135 124416065200874049519654203)
  ·
    refine ⟨186624097801311074279481305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124416065200874049519654203 186624097801311074279481305)
    ·
      refine ⟨139968073350983305709610979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 186624097801311074279481305 139968073350983305709610979)
      ·
        refine ⟨209952110026474958564416469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139968073350983305709610979 209952110026474958564416469)
        ·
          refine ⟨4920752578745506841353511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 209952110026474958564416469 4920752578745506841353511)
          ·
            refine ⟨7381128868118260262030267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4920752578745506841353511 7381128868118260262030267)
            ·
              refine ⟨11071693302177390393045401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7381128868118260262030267 11071693302177390393045401)
              ·
                refine ⟨8303769976633042794784051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11071693302177390393045401 8303769976633042794784051)
                ·
                  refine ⟨12455654964949564192176077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8303769976633042794784051 12455654964949564192176077)
                  ·
                    refine ⟨4670870611856086572066029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12455654964949564192176077 4670870611856086572066029)
                    ·
                      refine ⟨1751576479446032464524761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4670870611856086572066029 1751576479446032464524761)
                      ·
                        rfl

theorem cell23_3411183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 1, 2, 1, 3, 3].length) (baseStart_3411183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3411183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3411183 prefixEnd_3411183 := by exact prefixLift 3411183
  have htrace : WordTrace (prefixWord ++ tailWord_3411183) baseStart_3411183 baseEnd_3411183 := by
    simpa [prefixWord, tailWord_3411183, baseEnd_3411183] using wordTrace_append hprefix tailTrace_3411183
  have hstable : (prefixWord ++ tailWord_3411183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3411183).length < 2 ^ (prefixWord ++ tailWord_3411183).sum := by decide
  have hdescent : baseEnd_3411183 < baseStart_3411183 := by decide
  rcases family_descends (prefixWord ++ tailWord_3411183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3411236 : List Nat := [2, 3, 1, 3, 1, 1, 1, 2, 1, 4, 4]
def baseStart_3411236 : Nat := 118140960795 + 3411236 * 2 ^ 59
def prefixEnd_3411236 : Nat := 4983230072969 + 3 ^ 40 * 3411236 * 2
def baseEnd_3411236 : Nat := 1751603693920720757162017

theorem tailTrace_3411236 : CollatzResearch.WordTrace tailWord_3411236 prefixEnd_3411236 1751603693920720757162017 := by
  unfold tailWord_3411236
  simp only [CollatzResearch.WordTrace]
  refine ⟨62208999134841019785666781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82945332179788026380889041 62208999134841019785666781)
  ·
    refine ⟨23328374675565382419625043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62208999134841019785666781 23328374675565382419625043)
    ·
      refine ⟨34992562013348073629437565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23328374675565382419625043 34992562013348073629437565)
      ·
        refine ⟨13122210755005527611039087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34992562013348073629437565 13122210755005527611039087)
        ·
          refine ⟨19683316132508291416558631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13122210755005527611039087 19683316132508291416558631)
          ·
            refine ⟨29524974198762437124837947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19683316132508291416558631 29524974198762437124837947)
            ·
              refine ⟨44287461298143655687256921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29524974198762437124837947 44287461298143655687256921)
              ·
                refine ⟨33215595973607741765442691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44287461298143655687256921 33215595973607741765442691)
                ·
                  refine ⟨49823393960411612648164037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33215595973607741765442691 49823393960411612648164037)
                  ·
                    refine ⟨9341886367577177371530757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 49823393960411612648164037 9341886367577177371530757)
                    ·
                      refine ⟨1751603693920720757162017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9341886367577177371530757 1751603693920720757162017)
                      ·
                        rfl

theorem cell23_3411236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 2, 1, 4, 4].length) (baseStart_3411236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3411236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3411236 prefixEnd_3411236 := by exact prefixLift 3411236
  have htrace : WordTrace (prefixWord ++ tailWord_3411236) baseStart_3411236 baseEnd_3411236 := by
    simpa [prefixWord, tailWord_3411236, baseEnd_3411236] using wordTrace_append hprefix tailTrace_3411236
  have hstable : (prefixWord ++ tailWord_3411236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3411236).length < 2 ^ (prefixWord ++ tailWord_3411236).sum := by decide
  have hdescent : baseEnd_3411236 < baseStart_3411236 := by decide
  rcases family_descends (prefixWord ++ tailWord_3411236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3411240 : List Nat := [2, 1, 5, 1, 2, 1, 2, 2, 1, 4, 2]
def baseStart_3411240 : Nat := 118140960795 + 3411240 * 2 ^ 59
def prefixEnd_3411240 : Nat := 4983230072969 + 3 ^ 40 * 3411240 * 2
def baseEnd_3411240 : Nat := 1751605747843338741511999

theorem tailTrace_3411240 : CollatzResearch.WordTrace tailWord_3411240 prefixEnd_3411240 1751605747843338741511999 := by
  unfold tailWord_3411240
  simp only [CollatzResearch.WordTrace]
  refine ⟨62209072080833774127239587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82945429441111698836319449 62209072080833774127239587)
  ·
    refine ⟨93313608121250661190859381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62209072080833774127239587 93313608121250661190859381)
    ·
      refine ⟨8748150761367249486643067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 93313608121250661190859381 8748150761367249486643067)
      ·
        refine ⟨13122226142050874229964601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8748150761367249486643067 13122226142050874229964601)
        ·
          refine ⟨9841669606538155672473451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13122226142050874229964601 9841669606538155672473451)
          ·
            refine ⟨14762504409807233508710177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9841669606538155672473451 14762504409807233508710177)
            ·
              refine ⟨11071878307355425131532633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14762504409807233508710177 11071878307355425131532633)
              ·
                refine ⟨8303908730516568848649475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11071878307355425131532633 8303908730516568848649475)
                ·
                  refine ⟨12455863095774853272974213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8303908730516568848649475 12455863095774853272974213)
                  ·
                    refine ⟨2335474330457784988682665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12455863095774853272974213 2335474330457784988682665)
                    ·
                      refine ⟨1751605747843338741511999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2335474330457784988682665 1751605747843338741511999)
                      ·
                        rfl

theorem cell23_3411240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 2, 2, 1, 4, 2].length) (baseStart_3411240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3411240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3411240 prefixEnd_3411240 := by exact prefixLift 3411240
  have htrace : WordTrace (prefixWord ++ tailWord_3411240) baseStart_3411240 baseEnd_3411240 := by
    simpa [prefixWord, tailWord_3411240, baseEnd_3411240] using wordTrace_append hprefix tailTrace_3411240
  have hstable : (prefixWord ++ tailWord_3411240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3411240).length < 2 ^ (prefixWord ++ tailWord_3411240).sum := by decide
  have hdescent : baseEnd_3411240 < baseStart_3411240 := by decide
  rcases family_descends (prefixWord ++ tailWord_3411240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3411257 : List Nat := [1, 2, 1, 6, 2, 1, 1, 1, 4, 2, 2]
def baseStart_3411257 : Nat := 118140960795 + 3411257 * 2 ^ 59
def prefixEnd_3411257 : Nat := 4983230072969 + 3 ^ 40 * 3411257 * 2
def baseEnd_3411257 : Nat := 1751614477014465174999421

theorem tailTrace_3411257 : CollatzResearch.WordTrace tailWord_3411257 prefixEnd_3411257 1751614477014465174999421 := by
  unfold tailWord_3411257
  simp only [CollatzResearch.WordTrace]
  refine ⟨124418764202605960157848025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82945842801737306771898683 124418764202605960157848025)
  ·
    refine ⟨93314073151954470118386019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124418764202605960157848025 93314073151954470118386019)
    ·
      refine ⟨139971109727931705177579029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93314073151954470118386019 139971109727931705177579029)
      ·
        refine ⟨6561145768496798680199017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 139971109727931705177579029 6561145768496798680199017)
        ·
          refine ⟨4920859326372599010149263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6561145768496798680199017 4920859326372599010149263)
          ·
            refine ⟨7381288989558898515223895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4920859326372599010149263 7381288989558898515223895)
            ·
              refine ⟨11071933484338347772835843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7381288989558898515223895 11071933484338347772835843)
              ·
                refine ⟨16607900226507521659253765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11071933484338347772835843 16607900226507521659253765)
                ·
                  refine ⟨3113981292470160311110081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16607900226507521659253765 3113981292470160311110081)
                  ·
                    refine ⟨2335485969352620233332561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3113981292470160311110081 2335485969352620233332561)
                    ·
                      refine ⟨1751614477014465174999421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2335485969352620233332561 1751614477014465174999421)
                      ·
                        rfl

theorem cell23_3411257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 1, 1, 4, 2, 2].length) (baseStart_3411257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3411257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3411257 prefixEnd_3411257 := by exact prefixLift 3411257
  have htrace : WordTrace (prefixWord ++ tailWord_3411257) baseStart_3411257 baseEnd_3411257 := by
    simpa [prefixWord, tailWord_3411257, baseEnd_3411257] using wordTrace_append hprefix tailTrace_3411257
  have hstable : (prefixWord ++ tailWord_3411257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3411257).length < 2 ^ (prefixWord ++ tailWord_3411257).sum := by decide
  have hdescent : baseEnd_3411257 < baseStart_3411257 := by decide
  rcases family_descends (prefixWord ++ tailWord_3411257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3411263 : List Nat := [1, 1, 2, 2, 4, 2, 2, 4, 5]
def baseStart_3411263 : Nat := 118140960795 + 3411263 * 2 ^ 59
def prefixEnd_3411263 : Nat := 4983230072969 + 3 ^ 40 * 3411263 * 2
def baseEnd_3411263 : Nat := 194624173099821350169377

theorem tailTrace_3411263 : CollatzResearch.WordTrace tailWord_3411263 prefixEnd_3411263 194624173099821350169377 := by
  unfold tailWord_3411263
  simp only [CollatzResearch.WordTrace]
  refine ⟨124418983040584223182566443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82945988693722815455044295 124418983040584223182566443)
  ·
    refine ⟨186628474560876334773849665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124418983040584223182566443 186628474560876334773849665)
    ·
      refine ⟨139971355920657251080387249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 186628474560876334773849665 139971355920657251080387249)
      ·
        refine ⟨104978516940492938310290437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 139971355920657251080387249 104978516940492938310290437)
        ·
          refine ⟨19683471926342425933179457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 104978516940492938310290437 19683471926342425933179457)
          ·
            refine ⟨14762603944756819449884593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19683471926342425933179457 14762603944756819449884593)
            ·
              refine ⟨11071952958567614587413445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14762603944756819449884593 11071952958567614587413445)
              ·
                refine ⟨2075991179731427735140021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11071952958567614587413445 2075991179731427735140021)
                ·
                  refine ⟨194624173099821350169377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2075991179731427735140021 194624173099821350169377)
                  ·
                    rfl

theorem cell23_3411263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 2, 4, 5].length) (baseStart_3411263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3411263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3411263 prefixEnd_3411263 := by exact prefixLift 3411263
  have htrace : WordTrace (prefixWord ++ tailWord_3411263) baseStart_3411263 baseEnd_3411263 := by
    simpa [prefixWord, tailWord_3411263, baseEnd_3411263] using wordTrace_append hprefix tailTrace_3411263
  have hstable : (prefixWord ++ tailWord_3411263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3411263).length < 2 ^ (prefixWord ++ tailWord_3411263).sum := by decide
  have hdescent : baseEnd_3411263 < baseStart_3411263 := by decide
  rcases family_descends (prefixWord ++ tailWord_3411263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3411276 : List Nat := [2, 2, 1, 3, 2, 2, 1, 2, 1, 7]
def baseStart_3411276 : Nat := 118140960795 + 3411276 * 2 ^ 59
def prefixEnd_3411276 : Nat := 4983230072969 + 3 ^ 40 * 3411276 * 2
def baseEnd_3411276 : Nat := 583874744382300200220611

theorem tailTrace_3411276 : CollatzResearch.WordTrace tailWord_3411276 prefixEnd_3411276 583874744382300200220611 := by
  unfold tailWord_3411276
  simp only [CollatzResearch.WordTrace]
  refine ⟨62209728594768563201394841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82946304793024750935193121 62209728594768563201394841)
  ·
    refine ⟨46657296446076422401046131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62209728594768563201394841 46657296446076422401046131)
    ·
      refine ⟨69985944669114633601569197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46657296446076422401046131 69985944669114633601569197)
      ·
        refine ⟨26244729250917987600588449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69985944669114633601569197 26244729250917987600588449)
        ·
          refine ⟨19683546938188490700441337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26244729250917987600588449 19683546938188490700441337)
          ·
            refine ⟨14762660203641368025331003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19683546938188490700441337 14762660203641368025331003)
            ·
              refine ⟨22143990305462052037996505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14762660203641368025331003 22143990305462052037996505)
              ·
                refine ⟨16607992729096539028497379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22143990305462052037996505 16607992729096539028497379)
                ·
                  refine ⟨24911989093644808542746069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16607992729096539028497379 24911989093644808542746069)
                  ·
                    refine ⟨583874744382300200220611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 24911989093644808542746069 583874744382300200220611)
                    ·
                      rfl

theorem cell23_3411276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 1, 2, 1, 7].length) (baseStart_3411276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3411276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3411276 prefixEnd_3411276 := by exact prefixLift 3411276
  have htrace : WordTrace (prefixWord ++ tailWord_3411276) baseStart_3411276 baseEnd_3411276 := by
    simpa [prefixWord, tailWord_3411276, baseEnd_3411276] using wordTrace_append hprefix tailTrace_3411276
  have hstable : (prefixWord ++ tailWord_3411276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3411276).length < 2 ^ (prefixWord ++ tailWord_3411276).sum := by decide
  have hdescent : baseEnd_3411276 < baseStart_3411276 := by decide
  rcases family_descends (prefixWord ++ tailWord_3411276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3411313 : List Nat := [1, 2, 2, 2, 1, 2, 2, 1, 4, 4, 2]
def baseStart_3411313 : Nat := 118140960795 + 3411313 * 2 ^ 59
def prefixEnd_3411313 : Nat := 4983230072969 + 3 ^ 40 * 3411313 * 2
def baseEnd_3411313 : Nat := 1751643231931116955899163

theorem tailTrace_3411313 : CollatzResearch.WordTrace tailWord_3411313 prefixEnd_3411313 1751643231931116955899163 := by
  unfold tailWord_3411313
  simp only [CollatzResearch.WordTrace]
  refine ⟨124420806690403081721886593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82947204460268721147924395 124420806690403081721886593)
  ·
    refine ⟨93315605017802311291414945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124420806690403081721886593 93315605017802311291414945)
    ·
      refine ⟨69986703763351733468561209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93315605017802311291414945 69986703763351733468561209)
      ·
        refine ⟨52490027822513800101420907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69986703763351733468561209 52490027822513800101420907)
        ·
          refine ⟨78735041733770700152131361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52490027822513800101420907 78735041733770700152131361)
          ·
            refine ⟨59051281300328025114098521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78735041733770700152131361 59051281300328025114098521)
            ·
              refine ⟨44288460975246018835573891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59051281300328025114098521 44288460975246018835573891)
              ·
                refine ⟨66432691462869028253360837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44288460975246018835573891 66432691462869028253360837)
                ·
                  refine ⟨12456129649287942797505157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 66432691462869028253360837 12456129649287942797505157)
                  ·
                    refine ⟨2335524309241489274532217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12456129649287942797505157 2335524309241489274532217)
                    ·
                      refine ⟨1751643231931116955899163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2335524309241489274532217 1751643231931116955899163)
                      ·
                        rfl

theorem cell23_3411313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 1, 4, 4, 2].length) (baseStart_3411313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3411313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3411313 prefixEnd_3411313 := by exact prefixLift 3411313
  have htrace : WordTrace (prefixWord ++ tailWord_3411313) baseStart_3411313 baseEnd_3411313 := by
    simpa [prefixWord, tailWord_3411313, baseEnd_3411313] using wordTrace_append hprefix tailTrace_3411313
  have hstable : (prefixWord ++ tailWord_3411313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3411313).length < 2 ^ (prefixWord ++ tailWord_3411313).sum := by decide
  have hdescent : baseEnd_3411313 < baseStart_3411313 := by decide
  rcases family_descends (prefixWord ++ tailWord_3411313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3411390 : List Nat := [4, 2, 1, 1, 1, 1, 1, 4, 1, 5, 2]
def baseStart_3411390 : Nat := 118140960795 + 3411390 * 2 ^ 59
def prefixEnd_3411390 : Nat := 4983230072969 + 3 ^ 40 * 3411390 * 2
def baseEnd_3411390 : Nat := 1751682769941513154636309

theorem tailTrace_3411390 : CollatzResearch.WordTrace tailWord_3411390 prefixEnd_3411390 1751682769941513154636309 := by
  unfold tailWord_3411390
  simp only [CollatzResearch.WordTrace]
  refine ⟨15552951888890515484054953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 82949076740749415914959749 15552951888890515484054953)
  ·
    refine ⟨11664713916667886613041215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15552951888890515484054953 11664713916667886613041215)
    ·
      refine ⟨17497070875001829919561823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11664713916667886613041215 17497070875001829919561823)
      ·
        refine ⟨26245606312502744879342735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17497070875001829919561823 26245606312502744879342735)
        ·
          refine ⟨39368409468754117319014103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26245606312502744879342735 39368409468754117319014103)
          ·
            refine ⟨59052614203131175978521155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39368409468754117319014103 59052614203131175978521155)
            ·
              refine ⟨88578921304696763967781733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59052614203131175978521155 88578921304696763967781733)
              ·
                refine ⟨16608547744630643243959075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 88578921304696763967781733 16608547744630643243959075)
                ·
                  refine ⟨24912821616945964865938613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16608547744630643243959075 24912821616945964865938613)
                  ·
                    refine ⟨2335577026588684206181745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 24912821616945964865938613 2335577026588684206181745)
                    ·
                      refine ⟨1751682769941513154636309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2335577026588684206181745 1751682769941513154636309)
                      ·
                        rfl

theorem cell23_3411390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 4, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 4, 1, 5, 2].length) (baseStart_3411390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3411390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3411390 prefixEnd_3411390 := by exact prefixLift 3411390
  have htrace : WordTrace (prefixWord ++ tailWord_3411390) baseStart_3411390 baseEnd_3411390 := by
    simpa [prefixWord, tailWord_3411390, baseEnd_3411390] using wordTrace_append hprefix tailTrace_3411390
  have hstable : (prefixWord ++ tailWord_3411390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3411390).length < 2 ^ (prefixWord ++ tailWord_3411390).sum := by decide
  have hdescent : baseEnd_3411390 < baseStart_3411390 := by decide
  rcases family_descends (prefixWord ++ tailWord_3411390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3411403 : List Nat := [1, 1, 1, 1, 3, 3, 4, 1, 3, 1, 4]
def baseStart_3411403 : Nat := 118140960795 + 3411403 * 2 ^ 59
def prefixEnd_3411403 : Nat := 4983230072969 + 3 ^ 40 * 3411403 * 2
def baseEnd_3411403 : Nat := 1751689445190021603773749

theorem tailTrace_3411403 : CollatzResearch.WordTrace tailWord_3411403 prefixEnd_3411403 1751689445190021603773749 := by
  unfold tailWord_3411403
  simp only [CollatzResearch.WordTrace]
  refine ⟨124424089260077027092662863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82949392840051351395108575 124424089260077027092662863)
  ·
    refine ⟨186636133890115540638994295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124424089260077027092662863 186636133890115540638994295)
    ·
      refine ⟨279954200835173310958491443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186636133890115540638994295 279954200835173310958491443)
      ·
        refine ⟨419931301252759966437737165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 279954200835173310958491443 419931301252759966437737165)
        ·
          refine ⟨157474237969784987414151437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 419931301252759966437737165 157474237969784987414151437)
          ·
            refine ⟨59052839238669370280306789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 157474237969784987414151437 59052839238669370280306789)
            ·
              refine ⟨11072407357250506927557523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 59052839238669370280306789 11072407357250506927557523)
              ·
                refine ⟨16608611035875760391336285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11072407357250506927557523 16608611035875760391336285)
                ·
                  refine ⟨6228229138453410146751107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16608611035875760391336285 6228229138453410146751107)
                  ·
                    refine ⟨9342343707680115220126661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6228229138453410146751107 9342343707680115220126661)
                    ·
                      refine ⟨1751689445190021603773749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9342343707680115220126661 1751689445190021603773749)
                      ·
                        rfl

theorem cell23_3411403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 4, 1, 3, 1, 4].length) (baseStart_3411403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3411403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3411403 prefixEnd_3411403 := by exact prefixLift 3411403
  have htrace : WordTrace (prefixWord ++ tailWord_3411403) baseStart_3411403 baseEnd_3411403 := by
    simpa [prefixWord, tailWord_3411403, baseEnd_3411403] using wordTrace_append hprefix tailTrace_3411403
  have hstable : (prefixWord ++ tailWord_3411403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3411403).length < 2 ^ (prefixWord ++ tailWord_3411403).sum := by decide
  have hdescent : baseEnd_3411403 < baseStart_3411403 := by decide
  rcases family_descends (prefixWord ++ tailWord_3411403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3411413 : List Nat := [1, 3, 2, 3, 1, 1, 1, 4, 1, 6]
def baseStart_3411413 : Nat := 118140960795 + 3411413 * 2 ^ 59
def prefixEnd_3411413 : Nat := 4983230072969 + 3 ^ 40 * 3411413 * 2
def baseEnd_3411413 : Nat := 583898193332188854882901

theorem tailTrace_3411413 : CollatzResearch.WordTrace tailWord_3411413 prefixEnd_3411413 583898193332188854882901 := by
  unfold tailWord_3411413
  simp only [CollatzResearch.WordTrace]
  refine ⟨124424453990040798800526893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82949635993360532533684595 124424453990040798800526893)
  ·
    refine ⟨46659170246265299550197585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 124424453990040798800526893 46659170246265299550197585)
    ·
      refine ⟨34994377684698974662648189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46659170246265299550197585 34994377684698974662648189)
      ·
        refine ⟨13122891631762115498493071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34994377684698974662648189 13122891631762115498493071)
        ·
          refine ⟨19684337447643173247739607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13122891631762115498493071 19684337447643173247739607)
          ·
            refine ⟨29526506171464759871609411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19684337447643173247739607 29526506171464759871609411)
            ·
              refine ⟨44289759257197139807414117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29526506171464759871609411 44289759257197139807414117)
              ·
                refine ⟨8304329860724463713890147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 44289759257197139807414117 8304329860724463713890147)
                ·
                  refine ⟨12456494791086695570835221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8304329860724463713890147 12456494791086695570835221)
                  ·
                    refine ⟨583898193332188854882901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12456494791086695570835221 583898193332188854882901)
                    ·
                      rfl

theorem cell23_3411413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 4, 1, 6].length) (baseStart_3411413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3411413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3411413 prefixEnd_3411413 := by exact prefixLift 3411413
  have htrace : WordTrace (prefixWord ++ tailWord_3411413) baseStart_3411413 baseEnd_3411413 := by
    simpa [prefixWord, tailWord_3411413, baseEnd_3411413] using wordTrace_append hprefix tailTrace_3411413
  have hstable : (prefixWord ++ tailWord_3411413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3411413).length < 2 ^ (prefixWord ++ tailWord_3411413).sum := by decide
  have hdescent : baseEnd_3411413 < baseStart_3411413 := by decide
  rcases family_descends (prefixWord ++ tailWord_3411413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3411417 : List Nat := [1, 2, 1, 2, 4, 4, 2, 1, 1, 5]
def baseStart_3411417 : Nat := 118140960795 + 3411417 * 2 ^ 59
def prefixEnd_3411417 : Nat := 4983230072969 + 3 ^ 40 * 3411417 * 2
def baseEnd_3411417 : Nat := 583898877973061516332895

theorem tailTrace_3411417 : CollatzResearch.WordTrace tailWord_3411417 prefixEnd_3411417 583898877973061516332895 := by
  unfold tailWord_3411417
  simp only [CollatzResearch.WordTrace]
  refine ⟨124424599882026307483672505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82949733254684204989115003 124424599882026307483672505)
  ·
    refine ⟨93318449911519730612754379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124424599882026307483672505 93318449911519730612754379)
    ·
      refine ⟨139977674867279595919131569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93318449911519730612754379 139977674867279595919131569)
      ·
        refine ⟨104983256150459696939348677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 139977674867279595919131569 104983256150459696939348677)
        ·
          refine ⟨19684360528211193176127877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 104983256150459696939348677 19684360528211193176127877)
          ·
            refine ⟨3690817599039598720523977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19684360528211193176127877 3690817599039598720523977)
            ·
              refine ⟨2768113199279699040392983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3690817599039598720523977 2768113199279699040392983)
              ·
                refine ⟨4152169798919548560589475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2768113199279699040392983 4152169798919548560589475)
                ·
                  refine ⟨6228254698379322840884213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4152169798919548560589475 6228254698379322840884213)
                  ·
                    refine ⟨583898877973061516332895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6228254698379322840884213 583898877973061516332895)
                    ·
                      rfl

theorem cell23_3411417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 4, 2, 1, 1, 5].length) (baseStart_3411417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3411417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3411417 prefixEnd_3411417 := by exact prefixLift 3411417
  have htrace : WordTrace (prefixWord ++ tailWord_3411417) baseStart_3411417 baseEnd_3411417 := by
    simpa [prefixWord, tailWord_3411417, baseEnd_3411417] using wordTrace_append hprefix tailTrace_3411417
  have hstable : (prefixWord ++ tailWord_3411417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3411417).length < 2 ^ (prefixWord ++ tailWord_3411417).sum := by decide
  have hdescent : baseEnd_3411417 < baseStart_3411417 := by decide
  rcases family_descends (prefixWord ++ tailWord_3411417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3411423 : List Nat := [1, 1, 2, 3, 3, 1, 2, 3, 1, 1, 5]
def baseStart_3411423 : Nat := 118140960795 + 3411423 * 2 ^ 59
def prefixEnd_3411423 : Nat := 4983230072969 + 3 ^ 40 * 3411423 * 2
def baseEnd_3411423 : Nat := 1751699714803111525523657

theorem tailTrace_3411423 : CollatzResearch.WordTrace tailWord_3411423 prefixEnd_3411423 1751699714803111525523657 := by
  unfold tailWord_3411423
  simp only [CollatzResearch.WordTrace]
  refine ⟨124424818720004570508390923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82949879146669713672260615 124424818720004570508390923)
  ·
    refine ⟨186637228080006855762586385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124424818720004570508390923 186637228080006855762586385)
    ·
      refine ⟨139977921060005141821939789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 186637228080006855762586385 139977921060005141821939789)
      ·
        refine ⟨52491720397501928183227421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 139977921060005141821939789 52491720397501928183227421)
        ·
          refine ⟨19684395149063223068710283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52491720397501928183227421 19684395149063223068710283)
          ·
            refine ⟨29526592723594834603065425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19684395149063223068710283 29526592723594834603065425)
            ·
              refine ⟨22144944542696125952299069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29526592723594834603065425 22144944542696125952299069)
              ·
                refine ⟨8304354203511047232112151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22144944542696125952299069 8304354203511047232112151)
                ·
                  refine ⟨12456531305266570848168227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8304354203511047232112151 12456531305266570848168227)
                  ·
                    refine ⟨18684796957899856272252341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12456531305266570848168227 18684796957899856272252341)
                    ·
                      refine ⟨1751699714803111525523657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18684796957899856272252341 1751699714803111525523657)
                      ·
                        rfl

theorem cell23_3411423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 2, 3, 1, 1, 5].length) (baseStart_3411423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3411423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3411423 prefixEnd_3411423 := by exact prefixLift 3411423
  have htrace : WordTrace (prefixWord ++ tailWord_3411423) baseStart_3411423 baseEnd_3411423 := by
    simpa [prefixWord, tailWord_3411423, baseEnd_3411423] using wordTrace_append hprefix tailTrace_3411423
  have hstable : (prefixWord ++ tailWord_3411423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3411423).length < 2 ^ (prefixWord ++ tailWord_3411423).sum := by decide
  have hdescent : baseEnd_3411423 < baseStart_3411423 := by decide
  rcases family_descends (prefixWord ++ tailWord_3411423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3411460 : List Nat := [2, 3, 2, 3, 2, 1, 1, 9]
def baseStart_3411460 : Nat := 118140960795 + 3411460 * 2 ^ 59
def prefixEnd_3411460 : Nat := 4983230072969 + 3 ^ 40 * 3411460 * 2
def baseEnd_3411460 : Nat := 64878470873604736324481

theorem tailTrace_3411460 : CollatzResearch.WordTrace tailWord_3411460 prefixEnd_3411460 64878470873604736324481 := by
  unfold tailWord_3411460
  simp only [CollatzResearch.WordTrace]
  refine ⟨62213084110435262913743917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82950778813913683884991889 62213084110435262913743917)
  ·
    refine ⟨23329906541413223592653969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62213084110435262913743917 23329906541413223592653969)
    ·
      refine ⟨17497429906059917694490477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23329906541413223592653969 17497429906059917694490477)
      ·
        refine ⟨6561536214772469135433929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17497429906059917694490477 6561536214772469135433929)
        ·
          refine ⟨4921152161079351851575447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6561536214772469135433929 4921152161079351851575447)
          ·
            refine ⟨7381728241619027777363171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4921152161079351851575447 7381728241619027777363171)
            ·
              refine ⟨11072592362428541666044757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7381728241619027777363171 11072592362428541666044757)
              ·
                refine ⟨64878470873604736324481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 11072592362428541666044757 64878470873604736324481)
                ·
                  rfl

theorem cell23_3411460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 1, 9].length) (baseStart_3411460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3411460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3411460 prefixEnd_3411460 := by exact prefixLift 3411460
  have htrace : WordTrace (prefixWord ++ tailWord_3411460) baseStart_3411460 baseEnd_3411460 := by
    simpa [prefixWord, tailWord_3411460, baseEnd_3411460] using wordTrace_append hprefix tailTrace_3411460
  have hstable : (prefixWord ++ tailWord_3411460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3411460).length < 2 ^ (prefixWord ++ tailWord_3411460).sum := by decide
  have hdescent : baseEnd_3411460 < baseStart_3411460 := by decide
  rcases family_descends (prefixWord ++ tailWord_3411460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3411488 : List Nat := [2, 1, 1, 6, 1, 2, 3, 2, 1, 2, 2]
def baseStart_3411488 : Nat := 118140960795 + 3411488 * 2 ^ 59
def prefixEnd_3411488 : Nat := 4983230072969 + 3 ^ 40 * 3411488 * 2
def baseEnd_3411488 : Nat := 1751733091045653771210859

theorem tailTrace_3411488 : CollatzResearch.WordTrace tailWord_3411488 prefixEnd_3411488 1751733091045653771210859 := by
  unfold tailWord_3411488
  simp only [CollatzResearch.WordTrace]
  refine ⟨62213594732384543304753559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82951459643179391073004745 62213594732384543304753559)
  ·
    refine ⟨93320392098576814957130339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62213594732384543304753559 93320392098576814957130339)
    ·
      refine ⟨139980588147865222435695509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93320392098576814957130339 139980588147865222435695509)
      ·
        refine ⟨6561590069431182301673227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 139980588147865222435695509 6561590069431182301673227)
        ·
          refine ⟨9842385104146773452509841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6561590069431182301673227 9842385104146773452509841)
          ·
            refine ⟨7381788828110080089382381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9842385104146773452509841 7381788828110080089382381)
            ·
              refine ⟨2768170810541280033518393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7381788828110080089382381 2768170810541280033518393)
              ·
                refine ⟨2076128107905960025138795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2768170810541280033518393 2076128107905960025138795)
                ·
                  refine ⟨3114192161858940037708193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2076128107905960025138795 3114192161858940037708193)
                  ·
                    refine ⟨2335644121394205028281145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3114192161858940037708193 2335644121394205028281145)
                    ·
                      refine ⟨1751733091045653771210859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2335644121394205028281145 1751733091045653771210859)
                      ·
                        rfl

theorem cell23_3411488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 3, 2, 1, 2, 2].length) (baseStart_3411488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3411488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3411488 prefixEnd_3411488 := by exact prefixLift 3411488
  have htrace : WordTrace (prefixWord ++ tailWord_3411488) baseStart_3411488 baseEnd_3411488 := by
    simpa [prefixWord, tailWord_3411488, baseEnd_3411488] using wordTrace_append hprefix tailTrace_3411488
  have hstable : (prefixWord ++ tailWord_3411488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3411488).length < 2 ^ (prefixWord ++ tailWord_3411488).sum := by decide
  have hdescent : baseEnd_3411488 < baseStart_3411488 := by decide
  rcases family_descends (prefixWord ++ tailWord_3411488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3411493 : List Nat := [1, 3, 1, 2, 2, 1, 1, 3, 2, 3, 4]
def baseStart_3411493 : Nat := 118140960795 + 3411493 * 2 ^ 59
def prefixEnd_3411493 : Nat := 4983230072969 + 3 ^ 40 * 3411493 * 2
def baseEnd_3411493 : Nat := 1751735658448926251648335

theorem tailTrace_3411493 : CollatzResearch.WordTrace tailWord_3411493 prefixEnd_3411493 1751735658448926251648335 := by
  unfold tailWord_3411493
  simp only [CollatzResearch.WordTrace]
  refine ⟨124427371829750972463439133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82951581219833981642292755 124427371829750972463439133)
  ·
    refine ⟨46660264436156614673789675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 124427371829750972463439133 46660264436156614673789675)
    ·
      refine ⟨69990396654234922010684513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46660264436156614673789675 69990396654234922010684513)
      ·
        refine ⟨52492797490676191508013385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69990396654234922010684513 52492797490676191508013385)
        ·
          refine ⟨39369598118007143631010039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52492797490676191508013385 39369598118007143631010039)
          ·
            refine ⟨59054397177010715446515059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39369598118007143631010039 59054397177010715446515059)
            ·
              refine ⟨88581595765516073169772589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59054397177010715446515059 88581595765516073169772589)
              ·
                refine ⟨33218098412068527438664721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 88581595765516073169772589 33218098412068527438664721)
                ·
                  refine ⟨24913573809051395578998541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33218098412068527438664721 24913573809051395578998541)
                  ·
                    refine ⟨9342590178394273342124453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24913573809051395578998541 9342590178394273342124453)
                    ·
                      refine ⟨1751735658448926251648335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9342590178394273342124453 1751735658448926251648335)
                      ·
                        rfl

theorem cell23_3411493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 3, 2, 3, 4].length) (baseStart_3411493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3411493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3411493 prefixEnd_3411493 := by exact prefixLift 3411493
  have htrace : WordTrace (prefixWord ++ tailWord_3411493) baseStart_3411493 baseEnd_3411493 := by
    simpa [prefixWord, tailWord_3411493, baseEnd_3411493] using wordTrace_append hprefix tailTrace_3411493
  have hstable : (prefixWord ++ tailWord_3411493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3411493).length < 2 ^ (prefixWord ++ tailWord_3411493).sum := by decide
  have hdescent : baseEnd_3411493 < baseStart_3411493 := by decide
  rcases family_descends (prefixWord ++ tailWord_3411493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3411523 : List Nat := [1, 1, 1, 3, 1, 2, 1, 1, 6, 2, 4]
def baseStart_3411523 : Nat := 118140960795 + 3411523 * 2 ^ 59
def prefixEnd_3411523 : Nat := 4983230072969 + 3 ^ 40 * 3411523 * 2
def baseEnd_3411523 : Nat := 1751751062868561134273197

theorem tailTrace_3411523 : CollatzResearch.WordTrace tailWord_3411523 prefixEnd_3411523 1751751062868561134273197 := by
  unfold tailWord_3411523
  simp only [CollatzResearch.WordTrace]
  refine ⟨124428466019642287587031223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82952310679761525058020815 124428466019642287587031223)
  ·
    refine ⟨186642699029463431380546835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124428466019642287587031223 186642699029463431380546835)
    ·
      refine ⟨279964048544195147070820253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186642699029463431380546835 279964048544195147070820253)
      ·
        refine ⟨104986518204073180151557595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 279964048544195147070820253 104986518204073180151557595)
        ·
          refine ⟨157479777306109770227336393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104986518204073180151557595 157479777306109770227336393)
          ·
            refine ⟨118109832979582327670502295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 157479777306109770227336393 118109832979582327670502295)
            ·
              refine ⟨177164749469373491505753443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 118109832979582327670502295 177164749469373491505753443)
              ·
                refine ⟨265747124204060237258630165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 177164749469373491505753443 265747124204060237258630165)
                ·
                  refine ⟨12456896447065323621498289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 265747124204060237258630165 12456896447065323621498289)
                  ·
                    refine ⟨9342672335298992716123717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12456896447065323621498289 9342672335298992716123717)
                    ·
                      refine ⟨1751751062868561134273197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9342672335298992716123717 1751751062868561134273197)
                      ·
                        rfl

theorem cell23_3411523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 6, 2, 4].length) (baseStart_3411523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3411523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3411523 prefixEnd_3411523 := by exact prefixLift 3411523
  have htrace : WordTrace (prefixWord ++ tailWord_3411523) baseStart_3411523 baseEnd_3411523 := by
    simpa [prefixWord, tailWord_3411523, baseEnd_3411523] using wordTrace_append hprefix tailTrace_3411523
  have hstable : (prefixWord ++ tailWord_3411523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3411523).length < 2 ^ (prefixWord ++ tailWord_3411523).sum := by decide
  have hdescent : baseEnd_3411523 < baseStart_3411523 := by decide
  rcases family_descends (prefixWord ++ tailWord_3411523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3411540 : List Nat := [2, 4, 1, 1, 1, 2, 2, 2, 2, 2, 4]
def baseStart_3411540 : Nat := 118140960795 + 3411540 * 2 ^ 59
def prefixEnd_3411540 : Nat := 4983230072969 + 3 ^ 40 * 3411540 * 2
def baseEnd_3411540 : Nat := 1751759792039687567760619

theorem tailTrace_3411540 : CollatzResearch.WordTrace tailWord_3411540 prefixEnd_3411540 1751759792039687567760619 := by
  unfold tailWord_3411540
  simp only [CollatzResearch.WordTrace]
  refine ⟨62214543030290349745200037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82952724040387132993600049 62214543030290349745200037)
  ·
    refine ⟨11665226818179440577225007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 62214543030290349745200037 11665226818179440577225007)
    ·
      refine ⟨17497840227269160865837511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11665226818179440577225007 17497840227269160865837511)
      ·
        refine ⟨26246760340903741298756267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17497840227269160865837511 26246760340903741298756267)
        ·
          refine ⟨39370140511355611948134401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26246760340903741298756267 39370140511355611948134401)
          ·
            refine ⟨29527605383516708961100801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39370140511355611948134401 29527605383516708961100801)
            ·
              refine ⟨22145704037637531720825601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29527605383516708961100801 22145704037637531720825601)
              ·
                refine ⟨16609278028228148790619201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22145704037637531720825601 16609278028228148790619201)
                ·
                  refine ⟨12456958521171111592964401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16609278028228148790619201 12456958521171111592964401)
                  ·
                    refine ⟨9342718890878333694723301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12456958521171111592964401 9342718890878333694723301)
                    ·
                      refine ⟨1751759792039687567760619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9342718890878333694723301 1751759792039687567760619)
                      ·
                        rfl

theorem cell23_3411540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 2, 2, 2, 2, 4].length) (baseStart_3411540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3411540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3411540 prefixEnd_3411540 := by exact prefixLift 3411540
  have htrace : WordTrace (prefixWord ++ tailWord_3411540) baseStart_3411540 baseEnd_3411540 := by
    simpa [prefixWord, tailWord_3411540, baseEnd_3411540] using wordTrace_append hprefix tailTrace_3411540
  have hstable : (prefixWord ++ tailWord_3411540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3411540).length < 2 ^ (prefixWord ++ tailWord_3411540).sum := by decide
  have hdescent : baseEnd_3411540 < baseStart_3411540 := by decide
  rcases family_descends (prefixWord ++ tailWord_3411540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3411600 : List Nat := [2, 1, 1, 1, 1, 1, 3, 6, 2, 1, 4]
def baseStart_3411600 : Nat := 118140960795 + 3411600 * 2 ^ 59
def prefixEnd_3411600 : Nat := 4983230072969 + 3 ^ 40 * 3411600 * 2
def baseEnd_3411600 : Nat := 1751790600878957333010343

theorem tailTrace_3411600 : CollatzResearch.WordTrace tailWord_3411600 prefixEnd_3411600 1751790600878957333010343 := by
  unfold tailWord_3411600
  simp only [CollatzResearch.WordTrace]
  refine ⟨62215637220181664868792127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82954182960242219825056169 62215637220181664868792127)
  ·
    refine ⟨93323455830272497303188191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62215637220181664868792127 93323455830272497303188191)
    ·
      refine ⟨139985183745408745954782287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93323455830272497303188191 139985183745408745954782287)
      ·
        refine ⟨209977775618113118932173431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139985183745408745954782287 209977775618113118932173431)
        ·
          refine ⟨314966663427169678398260147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 209977775618113118932173431 314966663427169678398260147)
          ·
            refine ⟨472449995140754517597390221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 314966663427169678398260147 472449995140754517597390221)
            ·
              refine ⟨177168748177782944099021333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 472449995140754517597390221 177168748177782944099021333)
              ·
                refine ⟨8304785070833575504641625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 177168748177782944099021333 8304785070833575504641625)
                ·
                  refine ⟨6228588803125181628481219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8304785070833575504641625 6228588803125181628481219)
                  ·
                    refine ⟨9342883204687772442721829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6228588803125181628481219 9342883204687772442721829)
                    ·
                      refine ⟨1751790600878957333010343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9342883204687772442721829 1751790600878957333010343)
                      ·
                        rfl

theorem cell23_3411600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 6, 2, 1, 4].length) (baseStart_3411600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3411600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3411600 prefixEnd_3411600 := by exact prefixLift 3411600
  have htrace : WordTrace (prefixWord ++ tailWord_3411600) baseStart_3411600 baseEnd_3411600 := by
    simpa [prefixWord, tailWord_3411600, baseEnd_3411600] using wordTrace_append hprefix tailTrace_3411600
  have hstable : (prefixWord ++ tailWord_3411600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3411600).length < 2 ^ (prefixWord ++ tailWord_3411600).sum := by decide
  have hdescent : baseEnd_3411600 < baseStart_3411600 := by decide
  rcases family_descends (prefixWord ++ tailWord_3411600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3411661 : List Nat := [1, 6, 2, 1, 1, 1, 3, 1, 3, 4]
def baseStart_3411661 : Nat := 118140960795 + 3411661 * 2 ^ 59
def prefixEnd_3411661 : Nat := 4983230072969 + 3 ^ 40 * 3411661 * 2
def baseEnd_3411661 : Nat := 583940641066293864782521

theorem tailTrace_3411661 : CollatzResearch.WordTrace tailWord_3411661 prefixEnd_3411661 583940641066293864782521 := by
  unfold tailWord_3411661
  simp only [CollatzResearch.WordTrace]
  refine ⟨124433499293142337155554837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82955666195428224770369891 124433499293142337155554837)
  ·
    refine ⟨5832820279366047054166633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 124433499293142337155554837 5832820279366047054166633)
    ·
      refine ⟨4374615209524535290624975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5832820279366047054166633 4374615209524535290624975)
      ·
        refine ⟨6561922814286802935937463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4374615209524535290624975 6561922814286802935937463)
        ·
          refine ⟨9842884221430204403906195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6561922814286802935937463 9842884221430204403906195)
          ·
            refine ⟨14764326332145306605859293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9842884221430204403906195 14764326332145306605859293)
            ·
              refine ⟨5536622374554489977197235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14764326332145306605859293 5536622374554489977197235)
              ·
                refine ⟨8304933561831734965795853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5536622374554489977197235 8304933561831734965795853)
                ·
                  refine ⟨3114350085686900612173445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8304933561831734965795853 3114350085686900612173445)
                  ·
                    refine ⟨583940641066293864782521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3114350085686900612173445 583940641066293864782521)
                    ·
                      rfl

theorem cell23_3411661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 3, 1, 3, 4].length) (baseStart_3411661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3411661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3411661 prefixEnd_3411661 := by exact prefixLift 3411661
  have htrace : WordTrace (prefixWord ++ tailWord_3411661) baseStart_3411661 baseEnd_3411661 := by
    simpa [prefixWord, tailWord_3411661, baseEnd_3411661] using wordTrace_append hprefix tailTrace_3411661
  have hstable : (prefixWord ++ tailWord_3411661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3411661).length < 2 ^ (prefixWord ++ tailWord_3411661).sum := by decide
  have hdescent : baseEnd_3411661 < baseStart_3411661 := by decide
  rcases family_descends (prefixWord ++ tailWord_3411661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3411674 : List Nat := [3, 1, 1, 2, 2, 5, 2, 1, 6]
def baseStart_3411674 : Nat := 118140960795 + 3411674 * 2 ^ 59
def prefixEnd_3411674 : Nat := 4983230072969 + 3 ^ 40 * 3411674 * 2
def baseEnd_3411674 : Nat := 194647622049710004831667

theorem tailTrace_3411674 : CollatzResearch.WordTrace tailWord_3411674 prefixEnd_3411674 194647622049710004831667 := by
  unfold tailWord_3411674
  simp only [CollatzResearch.WordTrace]
  refine ⟨31108493360523810093944519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82955982294730160250518717 31108493360523810093944519)
  ·
    refine ⟨46662740040785715140916779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31108493360523810093944519 46662740040785715140916779)
    ·
      refine ⟨69994110061178572711375169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46662740040785715140916779 69994110061178572711375169)
      ·
        refine ⟨52495582545883929533531377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69994110061178572711375169 52495582545883929533531377)
        ·
          refine ⟨39371686909412947150148533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52495582545883929533531377 39371686909412947150148533)
          ·
            refine ⟨3691095647757463795326425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 39371686909412947150148533 3691095647757463795326425)
            ·
              refine ⟨2768321735818097846494819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3691095647757463795326425 2768321735818097846494819)
              ·
                refine ⟨4152482603727146769742229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2768321735818097846494819 4152482603727146769742229)
                ·
                  refine ⟨194647622049710004831667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4152482603727146769742229 194647622049710004831667)
                  ·
                    rfl

theorem cell23_3411674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 5, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 5, 2, 1, 6].length) (baseStart_3411674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3411674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3411674 prefixEnd_3411674 := by exact prefixLift 3411674
  have htrace : WordTrace (prefixWord ++ tailWord_3411674) baseStart_3411674 baseEnd_3411674 := by
    simpa [prefixWord, tailWord_3411674, baseEnd_3411674] using wordTrace_append hprefix tailTrace_3411674
  have hstable : (prefixWord ++ tailWord_3411674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3411674).length < 2 ^ (prefixWord ++ tailWord_3411674).sum := by decide
  have hdescent : baseEnd_3411674 < baseStart_3411674 := by decide
  rcases family_descends (prefixWord ++ tailWord_3411674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3411744 : List Nat := [2, 1, 1, 5, 1, 1, 2, 4, 1, 2, 3]
def baseStart_3411744 : Nat := 118140960795 + 3411744 * 2 ^ 59
def prefixEnd_3411744 : Nat := 4983230072969 + 3 ^ 40 * 3411744 * 2
def baseEnd_3411744 : Nat := 1751864542093204769609681

theorem tailTrace_3411744 : CollatzResearch.WordTrace tailWord_3411744 prefixEnd_3411744 1751864542093204769609681 := by
  unfold tailWord_3411744
  simp only [CollatzResearch.WordTrace]
  refine ⟨62218263275920821165413143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82957684367894428220550857 62218263275920821165413143)
  ·
    refine ⟨93327394913881231748119715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62218263275920821165413143 93327394913881231748119715)
    ·
      refine ⟨139991092370821847622179573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93327394913881231748119715 139991092370821847622179573)
      ·
        refine ⟨13124164909764548214579335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 139991092370821847622179573 13124164909764548214579335)
        ·
          refine ⟨19686247364646822321869003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13124164909764548214579335 19686247364646822321869003)
          ·
            refine ⟨29529371046970233482803505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19686247364646822321869003 29529371046970233482803505)
            ·
              refine ⟨22147028285227675112102629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29529371046970233482803505 22147028285227675112102629)
              ·
                refine ⟨4152567803480189083519243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22147028285227675112102629 4152567803480189083519243)
                ·
                  refine ⟨6228851705220283625278865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4152567803480189083519243 6228851705220283625278865)
                  ·
                    refine ⟨4671638778915212718959149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6228851705220283625278865 4671638778915212718959149)
                    ·
                      refine ⟨1751864542093204769609681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4671638778915212718959149 1751864542093204769609681)
                      ·
                        rfl

theorem cell23_3411744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 2, 4, 1, 2, 3].length) (baseStart_3411744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3411744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3411744 prefixEnd_3411744 := by exact prefixLift 3411744
  have htrace : WordTrace (prefixWord ++ tailWord_3411744) baseStart_3411744 baseEnd_3411744 := by
    simpa [prefixWord, tailWord_3411744, baseEnd_3411744] using wordTrace_append hprefix tailTrace_3411744
  have hstable : (prefixWord ++ tailWord_3411744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3411744).length < 2 ^ (prefixWord ++ tailWord_3411744).sum := by decide
  have hdescent : baseEnd_3411744 < baseStart_3411744 := by decide
  rcases family_descends (prefixWord ++ tailWord_3411744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3411761 : List Nat := [1, 2, 2, 3, 2, 2, 4, 1, 1, 2, 3]
def baseStart_3411761 : Nat := 118140960795 + 3411761 * 2 ^ 59
def prefixEnd_3411761 : Nat := 4983230072969 + 3 ^ 40 * 3411761 * 2
def baseEnd_3411761 : Nat := 1751873271264331203097103

theorem tailTrace_3411761 : CollatzResearch.WordTrace tailWord_3411761 prefixEnd_3411761 1751873271264331203097103 := by
  unfold tailWord_3411761
  simp only [CollatzResearch.WordTrace]
  refine ⟨124437146592780054234195137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82958097728520036156130091 124437146592780054234195137)
  ·
    refine ⟨93327859944585040675646353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124437146592780054234195137 93327859944585040675646353)
    ·
      refine ⟨69995894958438780506734765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93327859944585040675646353 69995894958438780506734765)
      ·
        refine ⟨26248460609414542690025537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69995894958438780506734765 26248460609414542690025537)
        ·
          refine ⟨19686345457060907017519153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26248460609414542690025537 19686345457060907017519153)
          ·
            refine ⟨14764759092795680263139365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19686345457060907017519153 14764759092795680263139365)
            ·
              refine ⟨2768392329899190049338631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14764759092795680263139365 2768392329899190049338631)
              ·
                refine ⟨4152588494848785074007947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2768392329899190049338631 4152588494848785074007947)
                ·
                  refine ⟨6228882742273177611011921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4152588494848785074007947 6228882742273177611011921)
                  ·
                    refine ⟨4671662056704883208258941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6228882742273177611011921 4671662056704883208258941)
                    ·
                      refine ⟨1751873271264331203097103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4671662056704883208258941 1751873271264331203097103)
                      ·
                        rfl

theorem cell23_3411761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 4, 1, 1, 2, 3].length) (baseStart_3411761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3411761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3411761 prefixEnd_3411761 := by exact prefixLift 3411761
  have htrace : WordTrace (prefixWord ++ tailWord_3411761) baseStart_3411761 baseEnd_3411761 := by
    simpa [prefixWord, tailWord_3411761, baseEnd_3411761] using wordTrace_append hprefix tailTrace_3411761
  have hstable : (prefixWord ++ tailWord_3411761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3411761).length < 2 ^ (prefixWord ++ tailWord_3411761).sum := by decide
  have hdescent : baseEnd_3411761 < baseStart_3411761 := by decide
  rcases family_descends (prefixWord ++ tailWord_3411761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3411801 : List Nat := [1, 2, 1, 2, 2, 3, 4, 2, 1, 3, 2]
def baseStart_3411801 : Nat := 118140960795 + 3411801 * 2 ^ 59
def prefixEnd_3411801 : Nat := 4983230072969 + 3 ^ 40 * 3411801 * 2
def baseEnd_3411801 : Nat := 1751893810490511046596919

theorem tailTrace_3411801 : CollatzResearch.WordTrace tailWord_3411801 prefixEnd_3411801 1751893810490511046596919 := by
  unfold tailWord_3411801
  simp only [CollatzResearch.WordTrace]
  refine ⟨124438605512635141065651257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82959070341756760710434171 124438605512635141065651257)
  ·
    refine ⟨93328954134476355799238443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124438605512635141065651257 93328954134476355799238443)
    ·
      refine ⟨139993431201714533698857665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93328954134476355799238443 139993431201714533698857665)
      ·
        refine ⟨104995073401285900274143249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 139993431201714533698857665 104995073401285900274143249)
        ·
          refine ⟨78746305050964425205607437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104995073401285900274143249 78746305050964425205607437)
          ·
            refine ⟨29529864394111659452102789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 78746305050964425205607437 29529864394111659452102789)
            ·
              refine ⟨5536849573895936147269273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29529864394111659452102789 5536849573895936147269273)
              ·
                refine ⟨4152637180421952110451955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5536849573895936147269273 4152637180421952110451955)
                ·
                  refine ⟨6228955770632928165677933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4152637180421952110451955 6228955770632928165677933)
                  ·
                    refine ⟨2335858413987348062129225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6228955770632928165677933 2335858413987348062129225)
                    ·
                      refine ⟨1751893810490511046596919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2335858413987348062129225 1751893810490511046596919)
                      ·
                        rfl

theorem cell23_3411801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 4, 2, 1, 3, 2].length) (baseStart_3411801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3411801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3411801 prefixEnd_3411801 := by exact prefixLift 3411801
  have htrace : WordTrace (prefixWord ++ tailWord_3411801) baseStart_3411801 baseEnd_3411801 := by
    simpa [prefixWord, tailWord_3411801, baseEnd_3411801] using wordTrace_append hprefix tailTrace_3411801
  have hstable : (prefixWord ++ tailWord_3411801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3411801).length < 2 ^ (prefixWord ++ tailWord_3411801).sum := by decide
  have hdescent : baseEnd_3411801 < baseStart_3411801 := by decide
  rcases family_descends (prefixWord ++ tailWord_3411801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3411914 : List Nat := [3, 1, 2, 1, 2, 1, 3, 1, 5, 4]
def baseStart_3411914 : Nat := 118140960795 + 3411914 * 2 ^ 59
def prefixEnd_3411914 : Nat := 4983230072969 + 3 ^ 40 * 3411914 * 2
def baseEnd_3411914 : Nat := 583983944601489701494633

theorem tailTrace_3411914 : CollatzResearch.WordTrace tailWord_3411914 prefixEnd_3411914 583983944601489701494633 := by
  unfold tailWord_3411914
  simp only [CollatzResearch.WordTrace]
  refine ⟨31110681740306440341128699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82961817974150507576343197 31110681740306440341128699)
  ·
    refine ⟨46666022610459660511693049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31110681740306440341128699 46666022610459660511693049)
    ·
      refine ⟨34999516957844745383769787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46666022610459660511693049 34999516957844745383769787)
      ·
        refine ⟨52499275436767118075654681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34999516957844745383769787 52499275436767118075654681)
        ·
          refine ⟨39374456577575338556741011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52499275436767118075654681 39374456577575338556741011)
          ·
            refine ⟨59061684866363007835111517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39374456577575338556741011 59061684866363007835111517)
            ·
              refine ⟨22148131824886127938166819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59061684866363007835111517 22148131824886127938166819)
              ·
                refine ⟨33222197737329191907250229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22148131824886127938166819 33222197737329191907250229)
                ·
                  refine ⟨3114581037874611741304709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 33222197737329191907250229 3114581037874611741304709)
                  ·
                    refine ⟨583983944601489701494633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3114581037874611741304709 583983944601489701494633)
                    ·
                      rfl

theorem cell23_3411914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 3, 1, 5, 4].length) (baseStart_3411914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3411914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3411914 prefixEnd_3411914 := by exact prefixLift 3411914
  have htrace : WordTrace (prefixWord ++ tailWord_3411914) baseStart_3411914 baseEnd_3411914 := by
    simpa [prefixWord, tailWord_3411914, baseEnd_3411914] using wordTrace_append hprefix tailTrace_3411914
  have hstable : (prefixWord ++ tailWord_3411914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3411914).length < 2 ^ (prefixWord ++ tailWord_3411914).sum := by decide
  have hdescent : baseEnd_3411914 < baseStart_3411914 := by decide
  rcases family_descends (prefixWord ++ tailWord_3411914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3411927 : List Nat := [1, 1, 3, 2, 1, 1, 4, 2, 8]
def baseStart_3411927 : Nat := 118140960795 + 3411927 * 2 ^ 59
def prefixEnd_3411927 : Nat := 4983230072969 + 3 ^ 40 * 3411927 * 2
def baseEnd_3411927 : Nat := 194662056561441950402371

theorem tailTrace_3411927 : CollatzResearch.WordTrace tailWord_3411927 prefixEnd_3411927 194662056561441950402371 := by
  unfold tailWord_3411927
  simp only [CollatzResearch.WordTrace]
  refine ⟨124443201110178664584738035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82962134073452443056492023 124443201110178664584738035)
  ·
    refine ⟨186664801665267996877107053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124443201110178664584738035 186664801665267996877107053)
    ·
      refine ⟨69999300624475498828915145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 186664801665267996877107053 69999300624475498828915145)
      ·
        refine ⟨52499475468356624121686359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69999300624475498828915145 52499475468356624121686359)
        ·
          refine ⟨78749213202534936182529539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52499475468356624121686359 78749213202534936182529539)
          ·
            refine ⟨118123819803802404273794309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78749213202534936182529539 118123819803802404273794309)
            ·
              refine ⟨22148216213212950801336433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 118123819803802404273794309 22148216213212950801336433)
              ·
                refine ⟨16611162159909713101002325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22148216213212950801336433 16611162159909713101002325)
                ·
                  refine ⟨194662056561441950402371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 16611162159909713101002325 194662056561441950402371)
                  ·
                    rfl

theorem cell23_3411927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 4, 2, 8].length) (baseStart_3411927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3411927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3411927 prefixEnd_3411927 := by exact prefixLift 3411927
  have htrace : WordTrace (prefixWord ++ tailWord_3411927) baseStart_3411927 baseEnd_3411927 := by
    simpa [prefixWord, tailWord_3411927, baseEnd_3411927] using wordTrace_append hprefix tailTrace_3411927
  have hstable : (prefixWord ++ tailWord_3411927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3411927).length < 2 ^ (prefixWord ++ tailWord_3411927).sum := by decide
  have hdescent : baseEnd_3411927 < baseStart_3411927 := by decide
  rcases family_descends (prefixWord ++ tailWord_3411927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3411961 : List Nat := [1, 2, 1, 3, 1, 5, 3, 1, 6]
def baseStart_3411961 : Nat := 118140960795 + 3411961 * 2 ^ 59
def prefixEnd_3411961 : Nat := 4983230072969 + 3 ^ 40 * 3411961 * 2
def baseEnd_3411961 : Nat := 194663996377247824510687

theorem tailTrace_3411961 : CollatzResearch.WordTrace tailWord_3411961 prefixEnd_3411961 194663996377247824510687 := by
  unfold tailWord_3411961
  simp only [CollatzResearch.WordTrace]
  refine ⟨124444441192055488391475737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82962960794703658927650491 124444441192055488391475737)
  ·
    refine ⟨93333330894041616293606803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124444441192055488391475737 93333330894041616293606803)
    ·
      refine ⟨139999996341062424440410205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93333330894041616293606803 139999996341062424440410205)
      ·
        refine ⟨52499998627898409165153827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 139999996341062424440410205 52499998627898409165153827)
        ·
          refine ⟨78749997941847613747730741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52499998627898409165153827 78749997941847613747730741)
          ·
            refine ⟨7382812307048213788849757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 78749997941847613747730741 7382812307048213788849757)
            ·
              refine ⟨2768554615143080170818659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7382812307048213788849757 2768554615143080170818659)
              ·
                refine ⟨4152831922714620256227989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2768554615143080170818659 4152831922714620256227989)
                ·
                  refine ⟨194663996377247824510687, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4152831922714620256227989 194663996377247824510687)
                  ·
                    rfl

theorem cell23_3411961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 3, 1, 6].length) (baseStart_3411961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3411961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3411961 prefixEnd_3411961 := by exact prefixLift 3411961
  have htrace : WordTrace (prefixWord ++ tailWord_3411961) baseStart_3411961 baseEnd_3411961 := by
    simpa [prefixWord, tailWord_3411961, baseEnd_3411961] using wordTrace_append hprefix tailTrace_3411961
  have hstable : (prefixWord ++ tailWord_3411961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3411961).length < 2 ^ (prefixWord ++ tailWord_3411961).sum := by decide
  have hdescent : baseEnd_3411961 < baseStart_3411961 := by decide
  rcases family_descends (prefixWord ++ tailWord_3411961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3411967 : List Nat := [1, 1, 2, 2, 1, 2, 1, 3, 2, 1, 7]
def baseStart_3411967 : Nat := 118140960795 + 3411967 * 2 ^ 59
def prefixEnd_3411967 : Nat := 4983230072969 + 3 ^ 40 * 3411967 * 2
def baseEnd_3411967 : Nat := 1751979048279157397121155

theorem tailTrace_3411967 : CollatzResearch.WordTrace tailWord_3411967 prefixEnd_3411967 1751979048279157397121155 := by
  unfold tailWord_3411967
  simp only [CollatzResearch.WordTrace]
  refine ⟨124444660030033751416194155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82963106686689167610796103 124444660030033751416194155)
  ·
    refine ⟨186666990045050627124291233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124444660030033751416194155 186666990045050627124291233)
    ·
      refine ⟨140000242533787970343218425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 186666990045050627124291233 140000242533787970343218425)
      ·
        refine ⟨105000181900340977757413819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 140000242533787970343218425 105000181900340977757413819)
        ·
          refine ⟨157500272850511466636120729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105000181900340977757413819 157500272850511466636120729)
          ·
            refine ⟨118125204637883599977090547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 157500272850511466636120729 118125204637883599977090547)
            ·
              refine ⟨177187806956825399965635821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 118125204637883599977090547 177187806956825399965635821)
              ·
                refine ⟨66445427608809524987113433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 177187806956825399965635821 66445427608809524987113433)
                ·
                  refine ⟨49834070706607143740335075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 66445427608809524987113433 49834070706607143740335075)
                  ·
                    refine ⟨74751106059910715610502613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 49834070706607143740335075 74751106059910715610502613)
                    ·
                      refine ⟨1751979048279157397121155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 74751106059910715610502613 1751979048279157397121155)
                      ·
                        rfl

theorem cell23_3411967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 3, 2, 1, 7].length) (baseStart_3411967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3411967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3411967 prefixEnd_3411967 := by exact prefixLift 3411967
  have htrace : WordTrace (prefixWord ++ tailWord_3411967) baseStart_3411967 baseEnd_3411967 := by
    simpa [prefixWord, tailWord_3411967, baseEnd_3411967] using wordTrace_append hprefix tailTrace_3411967
  have hstable : (prefixWord ++ tailWord_3411967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3411967).length < 2 ^ (prefixWord ++ tailWord_3411967).sum := by decide
  have hdescent : baseEnd_3411967 < baseStart_3411967 := by decide
  rcases family_descends (prefixWord ++ tailWord_3411967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3412025 : List Nat := [1, 2, 1, 5, 4, 1, 1, 2, 1, 5]
def baseStart_3412025 : Nat := 118140960795 + 3412025 * 2 ^ 59
def prefixEnd_3412025 : Nat := 4983230072969 + 3 ^ 40 * 3412025 * 2
def baseEnd_3412025 : Nat := 584002943385706056731963

theorem tailTrace_3412025 : CollatzResearch.WordTrace tailWord_3412025 prefixEnd_3412025 584002943385706056731963 := by
  unfold tailWord_3412025
  simp only [CollatzResearch.WordTrace]
  refine ⟨124446775463823627321805529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82964516975882418214537019 124446775463823627321805529)
  ·
    refine ⟨93335081597867720491354147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124446775463823627321805529 93335081597867720491354147)
    ·
      refine ⟨140002622396801580737031221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93335081597867720491354147 140002622396801580737031221)
      ·
        refine ⟨13125245849700148194096677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 140002622396801580737031221 13125245849700148194096677)
        ·
          refine ⟨2460983596818777786393127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13125245849700148194096677 2460983596818777786393127)
          ·
            refine ⟨3691475395228166679589691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2460983596818777786393127 3691475395228166679589691)
            ·
              refine ⟨5537213092842250019384537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3691475395228166679589691 5537213092842250019384537)
              ·
                refine ⟨4152909819631687514538403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5537213092842250019384537 4152909819631687514538403)
                ·
                  refine ⟨6229364729447531271807605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4152909819631687514538403 6229364729447531271807605)
                  ·
                    refine ⟨584002943385706056731963, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6229364729447531271807605 584002943385706056731963)
                    ·
                      rfl

theorem cell23_3412025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 4, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 4, 1, 1, 2, 1, 5].length) (baseStart_3412025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3412025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3412025 prefixEnd_3412025 := by exact prefixLift 3412025
  have htrace : WordTrace (prefixWord ++ tailWord_3412025) baseStart_3412025 baseEnd_3412025 := by
    simpa [prefixWord, tailWord_3412025, baseEnd_3412025] using wordTrace_append hprefix tailTrace_3412025
  have hstable : (prefixWord ++ tailWord_3412025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3412025).length < 2 ^ (prefixWord ++ tailWord_3412025).sum := by decide
  have hdescent : baseEnd_3412025 < baseStart_3412025 := by decide
  rcases family_descends (prefixWord ++ tailWord_3412025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3412028 : List Nat := [2, 2, 2, 2, 2, 1, 2, 1, 5, 2, 2]
def baseStart_3412028 : Nat := 118140960795 + 3412028 * 2 ^ 59
def prefixEnd_3412028 : Nat := 4983230072969 + 3 ^ 40 * 3412028 * 2
def baseEnd_3412028 : Nat := 1752010370599081658458375

theorem tailTrace_3412028 : CollatzResearch.WordTrace tailWord_3412028 prefixEnd_3412028 1752010370599081658458375 := by
  unfold tailWord_3412028
  simp only [CollatzResearch.WordTrace]
  refine ⟨62223442441406379417082369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82964589921875172556109825 62223442441406379417082369)
  ·
    refine ⟨46667581831054784562811777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62223442441406379417082369 46667581831054784562811777)
    ·
      refine ⟨35000686373291088422108833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46667581831054784562811777 35000686373291088422108833)
      ·
        refine ⟨26250514779968316316581625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35000686373291088422108833 26250514779968316316581625)
        ·
          refine ⟨19687886084976237237436219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26250514779968316316581625 19687886084976237237436219)
          ·
            refine ⟨29531829127464355856154329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19687886084976237237436219 29531829127464355856154329)
            ·
              refine ⟨22148871845598266892115747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29531829127464355856154329 22148871845598266892115747)
              ·
                refine ⟨33223307768397400338173621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22148871845598266892115747 33223307768397400338173621)
                ·
                  refine ⟨3114685103287256281703777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 33223307768397400338173621 3114685103287256281703777)
                  ·
                    refine ⟨2336013827465442211277833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3114685103287256281703777 2336013827465442211277833)
                    ·
                      refine ⟨1752010370599081658458375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2336013827465442211277833 1752010370599081658458375)
                      ·
                        rfl

theorem cell23_3412028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 2, 1, 5, 2, 2].length) (baseStart_3412028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3412028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3412028 prefixEnd_3412028 := by exact prefixLift 3412028
  have htrace : WordTrace (prefixWord ++ tailWord_3412028) baseStart_3412028 baseEnd_3412028 := by
    simpa [prefixWord, tailWord_3412028, baseEnd_3412028] using wordTrace_append hprefix tailTrace_3412028
  have hstable : (prefixWord ++ tailWord_3412028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3412028).length < 2 ^ (prefixWord ++ tailWord_3412028).sum := by decide
  have hdescent : baseEnd_3412028 < baseStart_3412028 := by decide
  rcases family_descends (prefixWord ++ tailWord_3412028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3412038 : List Nat := [6, 1, 1, 1, 1, 1, 3, 2, 1, 6]
def baseStart_3412038 : Nat := 118140960795 + 3412038 * 2 ^ 59
def prefixEnd_3412038 : Nat := 4983230072969 + 3 ^ 40 * 3412038 * 2
def baseEnd_3412038 : Nat := 584005168468542206444443

theorem tailTrace_3412038 : CollatzResearch.WordTrace tailWord_3412038 prefixEnd_3412038 584005168468542206444443 := by
  unfold tailWord_3412038
  simp only [CollatzResearch.WordTrace]
  refine ⟨3888976550399266579438399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 82964833075184353694685845 3888976550399266579438399)
  ·
    refine ⟨5833464825598899869157599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3888976550399266579438399 5833464825598899869157599)
    ·
      refine ⟨8750197238398349803736399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5833464825598899869157599 8750197238398349803736399)
      ·
        refine ⟨13125295857597524705604599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8750197238398349803736399 13125295857597524705604599)
        ·
          refine ⟨19687943786396287058406899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13125295857597524705604599 19687943786396287058406899)
          ·
            refine ⟨29531915679594430587610349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19687943786396287058406899 29531915679594430587610349)
            ·
              refine ⟨11074468379847911470353881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29531915679594430587610349 11074468379847911470353881)
              ·
                refine ⟨8305851284885933602765411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11074468379847911470353881 8305851284885933602765411)
                ·
                  refine ⟨12458776927328900404148117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8305851284885933602765411 12458776927328900404148117)
                  ·
                    refine ⟨584005168468542206444443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12458776927328900404148117 584005168468542206444443)
                    ·
                      rfl

theorem cell23_3412038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 3, 2, 1, 6].length) (baseStart_3412038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3412038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3412038 prefixEnd_3412038 := by exact prefixLift 3412038
  have htrace : WordTrace (prefixWord ++ tailWord_3412038) baseStart_3412038 baseEnd_3412038 := by
    simpa [prefixWord, tailWord_3412038, baseEnd_3412038] using wordTrace_append hprefix tailTrace_3412038
  have hstable : (prefixWord ++ tailWord_3412038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3412038).length < 2 ^ (prefixWord ++ tailWord_3412038).sum := by decide
  have hdescent : baseEnd_3412038 < baseStart_3412038 := by decide
  rcases family_descends (prefixWord ++ tailWord_3412038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3412045 : List Nat := [1, 6, 1, 1, 1, 1, 5, 1, 1, 1, 4]
def baseStart_3412045 : Nat := 118140960795 + 3412045 * 2 ^ 59
def prefixEnd_3412045 : Nat := 4983230072969 + 3 ^ 40 * 3412045 * 2
def baseEnd_3412045 : Nat := 1752019099770208091945797

theorem tailTrace_3412045 : CollatzResearch.WordTrace tailWord_3412045 prefixEnd_3412045 1752019099770208091945797 := by
  unfold tailWord_3412045
  simp only [CollatzResearch.WordTrace]
  refine ⟨124447504923751170737533589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82965003282500780491689059 124447504923751170737533589)
  ·
    refine ⟨5833476793300836128321887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 124447504923751170737533589 5833476793300836128321887)
    ·
      refine ⟨8750215189951254192482831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5833476793300836128321887 8750215189951254192482831)
      ·
        refine ⟨13125322784926881288724247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8750215189951254192482831 13125322784926881288724247)
        ·
          refine ⟨19687984177390321933086371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13125322784926881288724247 19687984177390321933086371)
          ·
            refine ⟨29531976266085482899629557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19687984177390321933086371 29531976266085482899629557)
            ·
              refine ⟨2768622774945514021840271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 29531976266085482899629557 2768622774945514021840271)
              ·
                refine ⟨4152934162418271032760407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2768622774945514021840271 4152934162418271032760407)
                ·
                  refine ⟨6229401243627406549140611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4152934162418271032760407 6229401243627406549140611)
                  ·
                    refine ⟨9344101865441109823710917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6229401243627406549140611 9344101865441109823710917)
                    ·
                      refine ⟨1752019099770208091945797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9344101865441109823710917 1752019099770208091945797)
                      ·
                        rfl

theorem cell23_3412045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 5, 1, 1, 1, 4].length) (baseStart_3412045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3412045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3412045 prefixEnd_3412045 := by exact prefixLift 3412045
  have htrace : WordTrace (prefixWord ++ tailWord_3412045) baseStart_3412045 baseEnd_3412045 := by
    simpa [prefixWord, tailWord_3412045, baseEnd_3412045] using wordTrace_append hprefix tailTrace_3412045
  have hstable : (prefixWord ++ tailWord_3412045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3412045).length < 2 ^ (prefixWord ++ tailWord_3412045).sum := by decide
  have hdescent : baseEnd_3412045 < baseStart_3412045 := by decide
  rcases family_descends (prefixWord ++ tailWord_3412045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3412064 : List Nat := [2, 1, 1, 3, 2, 3, 1, 1, 2, 7]
def baseStart_3412064 : Nat := 118140960795 + 3412064 * 2 ^ 59
def prefixEnd_3412064 : Nat := 4983230072969 + 3 ^ 40 * 3412064 * 2
def baseEnd_3412064 : Nat := 584009618634214505869403

theorem tailTrace_3412064 : CollatzResearch.WordTrace tailWord_3412064 prefixEnd_3412064 584009618634214505869403 := by
  unfold tailWord_3412064
  simp only [CollatzResearch.WordTrace]
  refine ⟨62224098955341168491237623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82965465273788224654983497 62224098955341168491237623)
  ·
    refine ⟨93336148433011752736856435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62224098955341168491237623 93336148433011752736856435)
    ·
      refine ⟨140004222649517629105284653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93336148433011752736856435 140004222649517629105284653)
      ·
        refine ⟨52501583493569110914481745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 140004222649517629105284653 52501583493569110914481745)
        ·
          refine ⟨39376187620176833185861309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52501583493569110914481745 39376187620176833185861309)
          ·
            refine ⟨14766070357566312444697991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39376187620176833185861309 14766070357566312444697991)
            ·
              refine ⟨22149105536349468667046987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14766070357566312444697991 22149105536349468667046987)
              ·
                refine ⟨33223658304524203000570481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22149105536349468667046987 33223658304524203000570481)
                ·
                  refine ⟨24917743728393152250427861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33223658304524203000570481 24917743728393152250427861)
                  ·
                    refine ⟨584009618634214505869403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 24917743728393152250427861 584009618634214505869403)
                    ·
                      rfl

theorem cell23_3412064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 1, 1, 2, 7].length) (baseStart_3412064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3412064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3412064 prefixEnd_3412064 := by exact prefixLift 3412064
  have htrace : WordTrace (prefixWord ++ tailWord_3412064) baseStart_3412064 baseEnd_3412064 := by
    simpa [prefixWord, tailWord_3412064, baseEnd_3412064] using wordTrace_append hprefix tailTrace_3412064
  have hstable : (prefixWord ++ tailWord_3412064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3412064).length < 2 ^ (prefixWord ++ tailWord_3412064).sum := by decide
  have hdescent : baseEnd_3412064 < baseStart_3412064 := by decide
  rcases family_descends (prefixWord ++ tailWord_3412064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
