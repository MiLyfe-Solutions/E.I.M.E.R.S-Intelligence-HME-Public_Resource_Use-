import V185TrunkScan23Chunk0611

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_3618698 : List Nat := [3, 1, 2, 4, 2, 1, 1, 3, 1, 5]
def baseStart_3618698 : Nat := 118140960795 + 3618698 * 2 ^ 59
def prefixEnd_3618698 : Nat := 4983230072969 + 3 ^ 40 * 3618698 * 2
def baseEnd_3618698 : Nat := 619377139154596020377639

theorem tailTrace_3618698 : CollatzResearch.WordTrace tailWord_3618698 prefixEnd_3618698 619377139154596020377639 := by
  unfold tailWord_3618698
  simp only [CollatzResearch.WordTrace]
  refine ⟨32996189761020661315018187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87989839362721763506715165 32996189761020661315018187)
  ·
    refine ⟨49494284641530991972527281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32996189761020661315018187 49494284641530991972527281)
    ·
      refine ⟨37120713481148243979395461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49494284641530991972527281 37120713481148243979395461)
      ·
        refine ⟨6960133777715295746136649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37120713481148243979395461 6960133777715295746136649)
        ·
          refine ⟨5220100333286471809602487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6960133777715295746136649 5220100333286471809602487)
          ·
            refine ⟨7830150499929707714403731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5220100333286471809602487 7830150499929707714403731)
            ·
              refine ⟨11745225749894561571605597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7830150499929707714403731 11745225749894561571605597)
              ·
                refine ⟨4404459656210460589352099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11745225749894561571605597 4404459656210460589352099)
                ·
                  refine ⟨6606689484315690884028149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4404459656210460589352099 6606689484315690884028149)
                  ·
                    refine ⟨619377139154596020377639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6606689484315690884028149 619377139154596020377639)
                    ·
                      rfl

theorem cell23_3618698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 1, 3, 1, 5].length) (baseStart_3618698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3618698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3618698 prefixEnd_3618698 := by exact prefixLift 3618698
  have htrace : WordTrace (prefixWord ++ tailWord_3618698) baseStart_3618698 baseEnd_3618698 := by
    simpa [prefixWord, tailWord_3618698, baseEnd_3618698] using wordTrace_append hprefix tailTrace_3618698
  have hstable : (prefixWord ++ tailWord_3618698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3618698).length < 2 ^ (prefixWord ++ tailWord_3618698).sum := by decide
  have hdescent : baseEnd_3618698 < baseStart_3618698 := by decide
  rcases family_descends (prefixWord ++ tailWord_3618698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3618711 : List Nat := [1, 1, 3, 3, 1, 4, 1, 1, 4, 4]
def baseStart_3618711 : Nat := 118140960795 + 3618711 * 2 ^ 59
def prefixEnd_3618711 : Nat := 4983230072969 + 3 ^ 40 * 3618711 * 2
def baseEnd_3618711 : Nat := 619379364237432170090119

theorem tailTrace_3618711 : CollatzResearch.WordTrace tailWord_3618711 prefixEnd_3618711 619379364237432170090119 := by
  unfold tailWord_3618711
  simp only [CollatzResearch.WordTrace]
  refine ⟨131985233193035548480295987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87990155462023698986863991 131985233193035548480295987)
  ·
    refine ⟨197977849789553322720443981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131985233193035548480295987 197977849789553322720443981)
    ·
      refine ⟨74241693671082496020166493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 197977849789553322720443981 74241693671082496020166493)
      ·
        refine ⟨27840635126655936007562435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74241693671082496020166493 27840635126655936007562435)
        ·
          refine ⟨41760952689983904011343653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27840635126655936007562435 41760952689983904011343653)
          ·
            refine ⟨7830178629371982002126935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41760952689983904011343653 7830178629371982002126935)
            ·
              refine ⟨11745267944057973003190403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7830178629371982002126935 11745267944057973003190403)
              ·
                refine ⟨17617901916086959504785605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11745267944057973003190403 17617901916086959504785605)
                ·
                  refine ⟨3303356609266304907147301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17617901916086959504785605 3303356609266304907147301)
                  ·
                    refine ⟨619379364237432170090119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3303356609266304907147301 619379364237432170090119)
                    ·
                      rfl

theorem cell23_3618711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 1, 1, 4, 4].length) (baseStart_3618711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3618711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3618711 prefixEnd_3618711 := by exact prefixLift 3618711
  have htrace : WordTrace (prefixWord ++ tailWord_3618711) baseStart_3618711 baseEnd_3618711 := by
    simpa [prefixWord, tailWord_3618711, baseEnd_3618711] using wordTrace_append hprefix tailTrace_3618711
  have hstable : (prefixWord ++ tailWord_3618711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3618711).length < 2 ^ (prefixWord ++ tailWord_3618711).sum := by decide
  have hdescent : baseEnd_3618711 < baseStart_3618711 := by decide
  rcases family_descends (prefixWord ++ tailWord_3618711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3618741 : List Nat := [1, 3, 3, 2, 1, 2, 4, 7]
def baseStart_3618741 : Nat := 118140960795 + 3618741 * 2 ^ 59
def prefixEnd_3618741 : Nat := 4983230072969 + 3 ^ 40 * 3618741 * 2
def baseEnd_3618741 : Nat := 68820499893775236773897

theorem tailTrace_3618741 : CollatzResearch.WordTrace tailWord_3618741 prefixEnd_3618741 68820499893775236773897 := by
  unfold tailWord_3618741
  simp only [CollatzResearch.WordTrace]
  refine ⟨131986327382926863603888077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87990884921951242402592051 131986327382926863603888077)
  ·
    refine ⟨49494872768597573851458029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 131986327382926863603888077 49494872768597573851458029)
    ·
      refine ⟨18560577288224090194296761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49494872768597573851458029 18560577288224090194296761)
      ·
        refine ⟨13920432966168067645722571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18560577288224090194296761 13920432966168067645722571)
        ·
          refine ⟨20880649449252101468583857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13920432966168067645722571 20880649449252101468583857)
          ·
            refine ⟨15660487086939076101437893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20880649449252101468583857 15660487086939076101437893)
            ·
              refine ⟨2936341328801076769019605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15660487086939076101437893 2936341328801076769019605)
              ·
                refine ⟨68820499893775236773897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2936341328801076769019605 68820499893775236773897)
                ·
                  rfl

theorem cell23_3618741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 4, 7].length) (baseStart_3618741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3618741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3618741 prefixEnd_3618741 := by exact prefixLift 3618741
  have htrace : WordTrace (prefixWord ++ tailWord_3618741) baseStart_3618741 baseEnd_3618741 := by
    simpa [prefixWord, tailWord_3618741, baseEnd_3618741] using wordTrace_append hprefix tailTrace_3618741
  have hstable : (prefixWord ++ tailWord_3618741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3618741).length < 2 ^ (prefixWord ++ tailWord_3618741).sum := by decide
  have hdescent : baseEnd_3618741 < baseStart_3618741 := by decide
  rcases family_descends (prefixWord ++ tailWord_3618741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3618751 : List Nat := [1, 1, 2, 2, 2, 1, 3, 1, 6, 1, 3]
def baseStart_3618751 : Nat := 118140960795 + 3618751 * 2 ^ 59
def prefixEnd_3618751 : Nat := 4983230072969 + 3 ^ 40 * 3618751 * 2
def baseEnd_3618751 : Nat := 1858158631938476353770173

theorem tailTrace_3618751 : CollatzResearch.WordTrace tailWord_3618751 prefixEnd_3618751 1858158631938476353770173 := by
  unfold tailWord_3618751
  simp only [CollatzResearch.WordTrace]
  refine ⟨131986692112890635311752107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87991128075260423541168071 131986692112890635311752107)
  ·
    refine ⟨197980038169335952967628161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131986692112890635311752107 197980038169335952967628161)
    ·
      refine ⟨148485028627001964725721121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 197980038169335952967628161 148485028627001964725721121)
      ·
        refine ⟨111363771470251473544290841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 148485028627001964725721121 111363771470251473544290841)
        ·
          refine ⟨83522828602688605158218131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 111363771470251473544290841 83522828602688605158218131)
          ·
            refine ⟨125284242904032907737327197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83522828602688605158218131 125284242904032907737327197)
            ·
              refine ⟨46981591089012340401497699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 125284242904032907737327197 46981591089012340401497699)
              ·
                refine ⟨70472386633518510602246549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46981591089012340401497699 70472386633518510602246549)
                ·
                  refine ⟨3303393123446180184480307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 70472386633518510602246549 3303393123446180184480307)
                  ·
                    refine ⟨4955089685169270276720461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3303393123446180184480307 4955089685169270276720461)
                    ·
                      refine ⟨1858158631938476353770173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4955089685169270276720461 1858158631938476353770173)
                      ·
                        rfl

theorem cell23_3618751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 1, 6, 1, 3].length) (baseStart_3618751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3618751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3618751 prefixEnd_3618751 := by exact prefixLift 3618751
  have htrace : WordTrace (prefixWord ++ tailWord_3618751) baseStart_3618751 baseEnd_3618751 := by
    simpa [prefixWord, tailWord_3618751, baseEnd_3618751] using wordTrace_append hprefix tailTrace_3618751
  have hstable : (prefixWord ++ tailWord_3618751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3618751).length < 2 ^ (prefixWord ++ tailWord_3618751).sum := by decide
  have hdescent : baseEnd_3618751 < baseStart_3618751 := by decide
  rcases family_descends (prefixWord ++ tailWord_3618751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3618784 : List Nat := [2, 1, 1, 3, 1, 1, 1, 5, 2, 6]
def baseStart_3618784 : Nat := 118140960795 + 3618784 * 2 ^ 59
def prefixEnd_3618784 : Nat := 4983230072969 + 3 ^ 40 * 3618784 * 2
def baseEnd_3618784 : Nat := 619391858933358241552507

theorem tailTrace_3618784 : CollatzResearch.WordTrace tailWord_3618784 prefixEnd_3618784 619391858933358241552507 := by
  unfold tailWord_3618784
  simp only [CollatzResearch.WordTrace]
  refine ⟨65993947860885540973851703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87991930481180721298468937 65993947860885540973851703)
  ·
    refine ⟨98990921791328311460777555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65993947860885540973851703 98990921791328311460777555)
    ·
      refine ⟨148486382686992467191166333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98990921791328311460777555 148486382686992467191166333)
      ·
        refine ⟨55682393507622175196687375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 148486382686992467191166333 55682393507622175196687375)
        ·
          refine ⟨83523590261433262795031063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55682393507622175196687375 83523590261433262795031063)
          ·
            refine ⟨125285385392149894192546595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83523590261433262795031063 125285385392149894192546595)
            ·
              refine ⟨187928078088224841288819893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 125285385392149894192546595 187928078088224841288819893)
              ·
                refine ⟨17618257320771078870826865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 187928078088224841288819893 17618257320771078870826865)
                ·
                  refine ⟨13213692990578309153120149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17618257320771078870826865 13213692990578309153120149)
                  ·
                    refine ⟨619391858933358241552507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13213692990578309153120149 619391858933358241552507)
                    ·
                      rfl

theorem cell23_3618784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 5, 2, 6].length) (baseStart_3618784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3618784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3618784 prefixEnd_3618784 := by exact prefixLift 3618784
  have htrace : WordTrace (prefixWord ++ tailWord_3618784) baseStart_3618784 baseEnd_3618784 := by
    simpa [prefixWord, tailWord_3618784, baseEnd_3618784] using wordTrace_append hprefix tailTrace_3618784
  have hstable : (prefixWord ++ tailWord_3618784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3618784).length < 2 ^ (prefixWord ++ tailWord_3618784).sum := by decide
  have hdescent : baseEnd_3618784 < baseStart_3618784 := by decide
  rcases family_descends (prefixWord ++ tailWord_3618784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3618785 : List Nat := [1, 2, 3, 1, 2, 1, 6, 1, 2, 1, 3]
def baseStart_3618785 : Nat := 118140960795 + 3618785 * 2 ^ 59
def prefixEnd_3618785 : Nat := 4983230072969 + 3 ^ 40 * 3618785 * 2
def baseEnd_3618785 : Nat := 1858176090280729220745017

theorem tailTrace_3618785 : CollatzResearch.WordTrace tailWord_3618785 prefixEnd_3618785 1858176090280729220745017 := by
  unfold tailWord_3618785
  simp only [CollatzResearch.WordTrace]
  refine ⟨131987932194767459118489809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87991954796511639412326539 131987932194767459118489809)
  ·
    refine ⟨98990949146075594338867357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131987932194767459118489809 98990949146075594338867357)
    ·
      refine ⟨37121605929778347877075259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 98990949146075594338867357 37121605929778347877075259)
      ·
        refine ⟨55682408894667521815612889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37121605929778347877075259 55682408894667521815612889)
        ·
          refine ⟨41761806671000641361709667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55682408894667521815612889 41761806671000641361709667)
          ·
            refine ⟨62642710006500962042564501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41761806671000641361709667 62642710006500962042564501)
            ·
              refine ⟨2936377031554732595745211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 62642710006500962042564501 2936377031554732595745211)
              ·
                refine ⟨4404565547332098893617817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2936377031554732595745211 4404565547332098893617817)
                ·
                  refine ⟨3303424160499074170213363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4404565547332098893617817 3303424160499074170213363)
                  ·
                    refine ⟨4955136240748611255320045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3303424160499074170213363 4955136240748611255320045)
                    ·
                      refine ⟨1858176090280729220745017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4955136240748611255320045 1858176090280729220745017)
                      ·
                        rfl

theorem cell23_3618785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 6, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 6, 1, 2, 1, 3].length) (baseStart_3618785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3618785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3618785 prefixEnd_3618785 := by exact prefixLift 3618785
  have htrace : WordTrace (prefixWord ++ tailWord_3618785) baseStart_3618785 baseEnd_3618785 := by
    simpa [prefixWord, tailWord_3618785, baseEnd_3618785] using wordTrace_append hprefix tailTrace_3618785
  have hstable : (prefixWord ++ tailWord_3618785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3618785).length < 2 ^ (prefixWord ++ tailWord_3618785).sum := by decide
  have hdescent : baseEnd_3618785 < baseStart_3618785 := by decide
  rcases family_descends (prefixWord ++ tailWord_3618785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3618808 : List Nat := [2, 1, 2, 1, 1, 3, 2, 1, 6, 2, 2]
def baseStart_3618808 : Nat := 118140960795 + 3618808 * 2 ^ 59
def prefixEnd_3618808 : Nat := 4983230072969 + 3 ^ 40 * 3618808 * 2
def baseEnd_3618808 : Nat := 1858187900335782630757411

theorem tailTrace_3618808 : CollatzResearch.WordTrace tailWord_3618808 prefixEnd_3618808 1858187900335782630757411 := by
  unfold tailWord_3618808
  simp only [CollatzResearch.WordTrace]
  refine ⟨65994385536842067023288539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87992514049122756031051385 65994385536842067023288539)
  ·
    refine ⟨98991578305263100534932809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65994385536842067023288539 98991578305263100534932809)
    ·
      refine ⟨74243683728947325401199607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98991578305263100534932809 74243683728947325401199607)
      ·
        refine ⟨111365525593420988101799411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74243683728947325401199607 111365525593420988101799411)
        ·
          refine ⟨167048288390131482152699117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111365525593420988101799411 167048288390131482152699117)
          ·
            refine ⟨62643108146299305807262169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 167048288390131482152699117 62643108146299305807262169)
            ·
              refine ⟨46982331109724479355446627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62643108146299305807262169 46982331109724479355446627)
              ·
                refine ⟨70473496664586719033169941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46982331109724479355446627 70473496664586719033169941)
                ·
                  refine ⟨3303445156152502454679841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 70473496664586719033169941 3303445156152502454679841)
                  ·
                    refine ⟨2477583867114376841009881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3303445156152502454679841 2477583867114376841009881)
                    ·
                      refine ⟨1858187900335782630757411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2477583867114376841009881 1858187900335782630757411)
                      ·
                        rfl

theorem cell23_3618808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 1, 6, 2, 2].length) (baseStart_3618808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3618808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3618808 prefixEnd_3618808 := by exact prefixLift 3618808
  have htrace : WordTrace (prefixWord ++ tailWord_3618808) baseStart_3618808 baseEnd_3618808 := by
    simpa [prefixWord, tailWord_3618808, baseEnd_3618808] using wordTrace_append hprefix tailTrace_3618808
  have hstable : (prefixWord ++ tailWord_3618808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3618808).length < 2 ^ (prefixWord ++ tailWord_3618808).sum := by decide
  have hdescent : baseEnd_3618808 < baseStart_3618808 := by decide
  rcases family_descends (prefixWord ++ tailWord_3618808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3618891 : List Nat := [1, 1, 1, 1, 3, 1, 2, 2, 7, 4]
def baseStart_3618891 : Nat := 118140960795 + 3618891 * 2 ^ 59
def prefixEnd_3618891 : Nat := 4983230072969 + 3 ^ 40 * 3618891 * 2
def baseEnd_3618891 : Nat := 619410173076701935339843

theorem tailTrace_3618891 : CollatzResearch.WordTrace tailWord_3618891 prefixEnd_3618891 619410173076701935339843 := by
  unfold tailWord_3618891
  simp only [CollatzResearch.WordTrace]
  refine ⟨131991798332383439221848527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87994532221588959481232351 131991798332383439221848527)
  ·
    refine ⟨197987697498575158832772791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131991798332383439221848527 197987697498575158832772791)
    ·
      refine ⟨296981546247862738249159187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197987697498575158832772791 296981546247862738249159187)
      ·
        refine ⟨445472319371794107373738781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 296981546247862738249159187 445472319371794107373738781)
        ·
          refine ⟨167052119764422790265152043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 445472319371794107373738781 167052119764422790265152043)
          ·
            refine ⟨250578179646634185397728065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 167052119764422790265152043 250578179646634185397728065)
            ·
              refine ⟨187933634734975639048296049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 250578179646634185397728065 187933634734975639048296049)
              ·
                refine ⟨140950226051231729286222037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 187933634734975639048296049 140950226051231729286222037)
                ·
                  refine ⟨3303520923075743655145829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 140950226051231729286222037 3303520923075743655145829)
                  ·
                    refine ⟨619410173076701935339843, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3303520923075743655145829 619410173076701935339843)
                    ·
                      rfl

theorem cell23_3618891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 2, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 2, 7, 4].length) (baseStart_3618891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3618891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3618891 prefixEnd_3618891 := by exact prefixLift 3618891
  have htrace : WordTrace (prefixWord ++ tailWord_3618891) baseStart_3618891 baseEnd_3618891 := by
    simpa [prefixWord, tailWord_3618891, baseEnd_3618891] using wordTrace_append hprefix tailTrace_3618891
  have hstable : (prefixWord ++ tailWord_3618891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3618891).length < 2 ^ (prefixWord ++ tailWord_3618891).sum := by decide
  have hdescent : baseEnd_3618891 < baseStart_3618891 := by decide
  rcases family_descends (prefixWord ++ tailWord_3618891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3618988 : List Nat := [2, 2, 1, 1, 1, 1, 1, 2, 4, 6, 2]
def baseStart_3618988 : Nat := 118140960795 + 3618988 * 2 ^ 59
def prefixEnd_3618988 : Nat := 4983230072969 + 3 ^ 40 * 3618988 * 2
def baseEnd_3618988 : Nat := 1858280326853591926506583

theorem tailTrace_3618988 : CollatzResearch.WordTrace tailWord_3618988 prefixEnd_3618988 1858280326853591926506583 := by
  unfold tailWord_3618988
  simp only [CollatzResearch.WordTrace]
  refine ⟨65997668106516012394064809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87996890808688016525419745 65997668106516012394064809)
  ·
    refine ⟨49498251079887009295548607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65997668106516012394064809 49498251079887009295548607)
    ·
      refine ⟨74247376619830513943322911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49498251079887009295548607 74247376619830513943322911)
      ·
        refine ⟨111371064929745770914984367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74247376619830513943322911 111371064929745770914984367)
        ·
          refine ⟨167056597394618656372476551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111371064929745770914984367 167056597394618656372476551)
          ·
            refine ⟨250584896091927984558714827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 167056597394618656372476551 250584896091927984558714827)
            ·
              refine ⟨375877344137891976838072241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 250584896091927984558714827 375877344137891976838072241)
              ·
                refine ⟨281908008103418982628554181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 375877344137891976838072241 281908008103418982628554181)
                ·
                  refine ⟨52857751519391059242853909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 281908008103418982628554181 52857751519391059242853909)
                  ·
                    refine ⟨2477707102471455902008777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 52857751519391059242853909 2477707102471455902008777)
                    ·
                      refine ⟨1858280326853591926506583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2477707102471455902008777 1858280326853591926506583)
                      ·
                        rfl

theorem cell23_3618988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 6, 2].length) (baseStart_3618988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3618988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3618988 prefixEnd_3618988 := by exact prefixLift 3618988
  have htrace : WordTrace (prefixWord ++ tailWord_3618988) baseStart_3618988 baseEnd_3618988 := by
    simpa [prefixWord, tailWord_3618988, baseEnd_3618988] using wordTrace_append hprefix tailTrace_3618988
  have hstable : (prefixWord ++ tailWord_3618988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3618988).length < 2 ^ (prefixWord ++ tailWord_3618988).sum := by decide
  have hdescent : baseEnd_3618988 < baseStart_3618988 := by decide
  rcases family_descends (prefixWord ++ tailWord_3618988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3618999 : List Nat := [1, 1, 3, 1, 4, 2, 4, 2, 1, 1, 3]
def baseStart_3618999 : Nat := 118140960795 + 3618999 * 2 ^ 59
def prefixEnd_3618999 : Nat := 4983230072969 + 3 ^ 40 * 3618999 * 2
def baseEnd_3618999 : Nat := 1858285975140791383469033

theorem tailTrace_3618999 : CollatzResearch.WordTrace tailWord_3618999 prefixEnd_3618999 1858285975140791383469033 := by
  unfold tailWord_3618999
  simp only [CollatzResearch.WordTrace]
  refine ⟨131995737415992173666780051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87997158277328115777853367 131995737415992173666780051)
  ·
    refine ⟨197993606123988260500170077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131995737415992173666780051 197993606123988260500170077)
    ·
      refine ⟨74247602296495597687563779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 197993606123988260500170077 74247602296495597687563779)
      ·
        refine ⟨111371403444743396531345669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74247602296495597687563779 111371403444743396531345669)
        ·
          refine ⟨20882138145889386849627313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 111371403444743396531345669 20882138145889386849627313)
          ·
            refine ⟨15661603609417040137220485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20882138145889386849627313 15661603609417040137220485)
            ·
              refine ⟨2936550676765695025728841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15661603609417040137220485 2936550676765695025728841)
              ·
                refine ⟨2202413007574271269296631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2936550676765695025728841 2202413007574271269296631)
                ·
                  refine ⟨3303619511361406903944947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2202413007574271269296631 3303619511361406903944947)
                  ·
                    refine ⟨4955429267042110355917421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3303619511361406903944947 4955429267042110355917421)
                    ·
                      refine ⟨1858285975140791383469033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4955429267042110355917421 1858285975140791383469033)
                      ·
                        rfl

theorem cell23_3618999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 4, 2, 1, 1, 3].length) (baseStart_3618999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3618999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3618999 prefixEnd_3618999 := by exact prefixLift 3618999
  have htrace : WordTrace (prefixWord ++ tailWord_3618999) baseStart_3618999 baseEnd_3618999 := by
    simpa [prefixWord, tailWord_3618999, baseEnd_3618999] using wordTrace_append hprefix tailTrace_3618999
  have hstable : (prefixWord ++ tailWord_3618999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3618999).length < 2 ^ (prefixWord ++ tailWord_3618999).sum := by decide
  have hdescent : baseEnd_3618999 < baseStart_3618999 := by decide
  rcases family_descends (prefixWord ++ tailWord_3618999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3619022 : List Nat := [4, 1, 1, 1, 4, 1, 1, 1, 5, 2, 2]
def baseStart_3619022 : Nat := 118140960795 + 3619022 * 2 ^ 59
def prefixEnd_3619022 : Nat := 4983230072969 + 3 ^ 40 * 3619022 * 2
def baseEnd_3619022 : Nat := 1858297785195844793481427

theorem tailTrace_3619022 : CollatzResearch.WordTrace tailWord_3619022 prefixEnd_3619022 1858297785195844793481427 := by
  unfold tailWord_3619022
  simp only [CollatzResearch.WordTrace]
  refine ⟨16499572036863606074358415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 87997717529939232396578213 16499572036863606074358415)
  ·
    refine ⟨24749358055295409111537623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16499572036863606074358415 24749358055295409111537623)
    ·
      refine ⟨37124037082943113667306435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24749358055295409111537623 37124037082943113667306435)
      ·
        refine ⟨55686055624414670500959653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37124037082943113667306435 55686055624414670500959653)
        ·
          refine ⟨10441135429577750718929935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 55686055624414670500959653 10441135429577750718929935)
          ·
            refine ⟨15661703144366626078394903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10441135429577750718929935 15661703144366626078394903)
            ·
              refine ⟨23492554716549939117592355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15661703144366626078394903 23492554716549939117592355)
              ·
                refine ⟨35238832074824908676388533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23492554716549939117592355 35238832074824908676388533)
                ·
                  refine ⟨3303640507014835188411425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 35238832074824908676388533 3303640507014835188411425)
                  ·
                    refine ⟨2477730380261126391308569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3303640507014835188411425 2477730380261126391308569)
                    ·
                      refine ⟨1858297785195844793481427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2477730380261126391308569 1858297785195844793481427)
                      ·
                        rfl

theorem cell23_3619022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 1, 1, 5, 2, 2].length) (baseStart_3619022 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3619022 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3619022 prefixEnd_3619022 := by exact prefixLift 3619022
  have htrace : WordTrace (prefixWord ++ tailWord_3619022) baseStart_3619022 baseEnd_3619022 := by
    simpa [prefixWord, tailWord_3619022, baseEnd_3619022] using wordTrace_append hprefix tailTrace_3619022
  have hstable : (prefixWord ++ tailWord_3619022).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3619022).length < 2 ^ (prefixWord ++ tailWord_3619022).sum := by decide
  have hdescent : baseEnd_3619022 < baseStart_3619022 := by decide
  rcases family_descends (prefixWord ++ tailWord_3619022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3619036 : List Nat := [2, 2, 5, 2, 1, 2, 2, 1, 1, 5]
def baseStart_3619036 : Nat := 118140960795 + 3619036 * 2 ^ 59
def prefixEnd_3619036 : Nat := 4983230072969 + 3 ^ 40 * 3619036 * 2
def baseEnd_3619036 : Nat := 619434991308335912902121

theorem tailTrace_3619036 : CollatzResearch.WordTrace tailWord_3619036 prefixEnd_3619036 619434991308335912902121 := by
  unfold tailWord_3619036
  simp only [CollatzResearch.WordTrace]
  refine ⟨65998543458429064492938481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87998057944572085990584641 65998543458429064492938481)
  ·
    refine ⟨49498907593821798369703861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65998543458429064492938481 49498907593821798369703861)
    ·
      refine ⟨4640522586920793597159737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 49498907593821798369703861 4640522586920793597159737)
      ·
        refine ⟨3480391940190595197869803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4640522586920793597159737 3480391940190595197869803)
        ·
          refine ⟨5220587910285892796804705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3480391940190595197869803 5220587910285892796804705)
          ·
            refine ⟨3915440932714419597603529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5220587910285892796804705 3915440932714419597603529)
            ·
              refine ⟨2936580699535814698202647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3915440932714419597603529 2936580699535814698202647)
              ·
                refine ⟨4404871049303722047303971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2936580699535814698202647 4404871049303722047303971)
                ·
                  refine ⟨6607306573955583070955957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4404871049303722047303971 6607306573955583070955957)
                  ·
                    refine ⟨619434991308335912902121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6607306573955583070955957 619434991308335912902121)
                    ·
                      rfl

theorem cell23_3619036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 2, 2, 1, 1, 5].length) (baseStart_3619036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3619036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3619036 prefixEnd_3619036 := by exact prefixLift 3619036
  have htrace : WordTrace (prefixWord ++ tailWord_3619036) baseStart_3619036 baseEnd_3619036 := by
    simpa [prefixWord, tailWord_3619036, baseEnd_3619036] using wordTrace_append hprefix tailTrace_3619036
  have hstable : (prefixWord ++ tailWord_3619036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3619036).length < 2 ^ (prefixWord ++ tailWord_3619036).sum := by decide
  have hdescent : baseEnd_3619036 < baseStart_3619036 := by decide
  rcases family_descends (prefixWord ++ tailWord_3619036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3619065 : List Nat := [1, 2, 1, 3, 1, 1, 2, 4, 3, 3, 2]
def baseStart_3619065 : Nat := 118140960795 + 3619065 * 2 ^ 59
def prefixEnd_3619065 : Nat := 4983230072969 + 3 ^ 40 * 3619065 * 2
def baseEnd_3619065 : Nat := 1858319864863988125243729

theorem tailTrace_3619065 : CollatzResearch.WordTrace tailWord_3619065 prefixEnd_3619065 1858319864863988125243729 := by
  unfold tailWord_3619065
  simp only [CollatzResearch.WordTrace]
  refine ⟨131998144633753066938682649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87998763089168711292455099 131998144633753066938682649)
  ·
    refine ⟨98998608475314800204011987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131998144633753066938682649 98998608475314800204011987)
    ·
      refine ⟨148497912712972200306017981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98998608475314800204011987 148497912712972200306017981)
      ·
        refine ⟨55686717267364575114756743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 148497912712972200306017981 55686717267364575114756743)
        ·
          refine ⟨83530075901046862672135115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55686717267364575114756743 83530075901046862672135115)
          ·
            refine ⟨125295113851570294008202673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83530075901046862672135115 125295113851570294008202673)
            ·
              refine ⟨93971335388677720506152005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 125295113851570294008202673 93971335388677720506152005)
              ·
                refine ⟨17619625385377072594903501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 93971335388677720506152005 17619625385377072594903501)
                ·
                  refine ⟨6607359519516402223088813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17619625385377072594903501 6607359519516402223088813)
                  ·
                    refine ⟨2477759819818650833658305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6607359519516402223088813 2477759819818650833658305)
                    ·
                      refine ⟨1858319864863988125243729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2477759819818650833658305 1858319864863988125243729)
                      ·
                        rfl

theorem cell23_3619065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 4, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 4, 3, 3, 2].length) (baseStart_3619065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3619065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3619065 prefixEnd_3619065 := by exact prefixLift 3619065
  have htrace : WordTrace (prefixWord ++ tailWord_3619065) baseStart_3619065 baseEnd_3619065 := by
    simpa [prefixWord, tailWord_3619065, baseEnd_3619065] using wordTrace_append hprefix tailTrace_3619065
  have hstable : (prefixWord ++ tailWord_3619065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3619065).length < 2 ^ (prefixWord ++ tailWord_3619065).sum := by decide
  have hdescent : baseEnd_3619065 < baseStart_3619065 := by decide
  rcases family_descends (prefixWord ++ tailWord_3619065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3619079 : List Nat := [1, 1, 4, 5, 2, 1, 2, 7]
def baseStart_3619079 : Nat := 118140960795 + 3619079 * 2 ^ 59
def prefixEnd_3619079 : Nat := 4983230072969 + 3 ^ 40 * 3619079 * 2
def baseEnd_3619079 : Nat := 68826927910857447054395

theorem tailTrace_3619079 : CollatzResearch.WordTrace tailWord_3619079 prefixEnd_3619079 68826927910857447054395 := by
  unfold tailWord_3619079
  simp only [CollatzResearch.WordTrace]
  refine ⟨131998655255702347329692291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87999103503801564886461527 131998655255702347329692291)
  ·
    refine ⟨197997982883553520994538437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131998655255702347329692291 197997982883553520994538437)
    ·
      refine ⟨37124621790666285186475957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 197997982883553520994538437 37124621790666285186475957)
      ·
        refine ⟨3480433292874964236232121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 37124621790666285186475957 3480433292874964236232121)
        ·
          refine ⟨2610324969656223177174091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3480433292874964236232121 2610324969656223177174091)
          ·
            refine ⟨3915487454484334765761137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2610324969656223177174091 3915487454484334765761137)
            ·
              refine ⟨2936615590863251074320853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3915487454484334765761137 2936615590863251074320853)
              ·
                refine ⟨68826927910857447054395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2936615590863251074320853 68826927910857447054395)
                ·
                  rfl

theorem cell23_3619079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 2, 1, 2, 7].length) (baseStart_3619079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3619079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3619079 prefixEnd_3619079 := by exact prefixLift 3619079
  have htrace : WordTrace (prefixWord ++ tailWord_3619079) baseStart_3619079 baseEnd_3619079 := by
    simpa [prefixWord, tailWord_3619079, baseEnd_3619079] using wordTrace_append hprefix tailTrace_3619079
  have hstable : (prefixWord ++ tailWord_3619079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3619079).length < 2 ^ (prefixWord ++ tailWord_3619079).sum := by decide
  have hdescent : baseEnd_3619079 < baseStart_3619079 := by decide
  rcases family_descends (prefixWord ++ tailWord_3619079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3619082 : List Nat := [3, 1, 2, 2, 1, 1, 3, 4, 1, 3, 2]
def baseStart_3619082 : Nat := 118140960795 + 3619082 * 2 ^ 59
def prefixEnd_3619082 : Nat := 4983230072969 + 3 ^ 40 * 3619082 * 2
def baseEnd_3619082 : Nat := 1858328594035114558731151

theorem tailTrace_3619082 : CollatzResearch.WordTrace tailWord_3619082 prefixEnd_3619082 1858328594035114558731151 := by
  unfold tailWord_3619082
  simp only [CollatzResearch.WordTrace]
  refine ⟨32999691168672869710512875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87999176449794319228034333 32999691168672869710512875)
  ·
    refine ⟨49499536753009304565769313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32999691168672869710512875 49499536753009304565769313)
    ·
      refine ⟨37124652564756978424326985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49499536753009304565769313 37124652564756978424326985)
      ·
        refine ⟨27843489423567733818245239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37124652564756978424326985 27843489423567733818245239)
        ·
          refine ⟨41765234135351600727367859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27843489423567733818245239 41765234135351600727367859)
          ·
            refine ⟨62647851203027401091051789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41765234135351600727367859 62647851203027401091051789)
            ·
              refine ⟨23492944201135275409144421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62647851203027401091051789 23492944201135275409144421)
              ·
                refine ⟨4404927037712864139214579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23492944201135275409144421 4404927037712864139214579)
                ·
                  refine ⟨6607390556569296208821869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4404927037712864139214579 6607390556569296208821869)
                  ·
                    refine ⟨2477771458713486078308201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6607390556569296208821869 2477771458713486078308201)
                    ·
                      refine ⟨1858328594035114558731151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2477771458713486078308201 1858328594035114558731151)
                      ·
                        rfl

theorem cell23_3619082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 3, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 3, 4, 1, 3, 2].length) (baseStart_3619082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3619082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3619082 prefixEnd_3619082 := by exact prefixLift 3619082
  have htrace : WordTrace (prefixWord ++ tailWord_3619082) baseStart_3619082 baseEnd_3619082 := by
    simpa [prefixWord, tailWord_3619082, baseEnd_3619082] using wordTrace_append hprefix tailTrace_3619082
  have hstable : (prefixWord ++ tailWord_3619082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3619082).length < 2 ^ (prefixWord ++ tailWord_3619082).sum := by decide
  have hdescent : baseEnd_3619082 < baseStart_3619082 := by decide
  rcases family_descends (prefixWord ++ tailWord_3619082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3619175 : List Nat := [1, 1, 5, 1, 3, 1, 2, 1, 1, 2, 5]
def baseStart_3619175 : Nat := 118140960795 + 3619175 * 2 ^ 59
def prefixEnd_3619175 : Nat := 4983230072969 + 3 ^ 40 * 3619175 * 2
def baseEnd_3619175 : Nat := 1858376347735982694868223

theorem tailTrace_3619175 : CollatzResearch.WordTrace tailWord_3619175 prefixEnd_3619175 1858376347735982694868223 := by
  unfold tailWord_3619175
  simp only [CollatzResearch.WordTrace]
  refine ⟨132002156663354555725186979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88001437775569703816791319 132002156663354555725186979)
  ·
    refine ⟨198003234995031833587780469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132002156663354555725186979 198003234995031833587780469)
    ·
      refine ⟨18562803280784234398854419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 198003234995031833587780469 18562803280784234398854419)
      ·
        refine ⟨27844204921176351598281629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18562803280784234398854419 27844204921176351598281629)
        ·
          refine ⟨10441576845441131849355611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27844204921176351598281629 10441576845441131849355611)
          ·
            refine ⟨15662365268161697774033417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10441576845441131849355611 15662365268161697774033417)
            ·
              refine ⟨11746773951121273330525063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15662365268161697774033417 11746773951121273330525063)
              ·
                refine ⟨17620160926681909995787595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11746773951121273330525063 17620160926681909995787595)
                ·
                  refine ⟨26430241390022864993681393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17620160926681909995787595 26430241390022864993681393)
                  ·
                    refine ⟨19822681042517148745261045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26430241390022864993681393 19822681042517148745261045)
                    ·
                      refine ⟨1858376347735982694868223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19822681042517148745261045 1858376347735982694868223)
                      ·
                        rfl

theorem cell23_3619175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 2, 1, 1, 2, 5].length) (baseStart_3619175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3619175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3619175 prefixEnd_3619175 := by exact prefixLift 3619175
  have htrace : WordTrace (prefixWord ++ tailWord_3619175) baseStart_3619175 baseEnd_3619175 := by
    simpa [prefixWord, tailWord_3619175, baseEnd_3619175] using wordTrace_append hprefix tailTrace_3619175
  have hstable : (prefixWord ++ tailWord_3619175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3619175).length < 2 ^ (prefixWord ++ tailWord_3619175).sum := by decide
  have hdescent : baseEnd_3619175 < baseStart_3619175 := by decide
  rcases family_descends (prefixWord ++ tailWord_3619175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3619195 : List Nat := [1, 1, 1, 1, 1, 7, 1, 1, 5, 4]
def baseStart_3619195 : Nat := 118140960795 + 3619195 * 2 ^ 59
def prefixEnd_3619195 : Nat := 4983230072969 + 3 ^ 40 * 3619195 * 2
def baseEnd_3619195 : Nat := 619462205783024205539377

theorem tailTrace_3619195 : CollatzResearch.WordTrace tailWord_3619195 prefixEnd_3619195 619462205783024205539377 := by
  unfold tailWord_3619195
  simp only [CollatzResearch.WordTrace]
  refine ⟨132002886123282099140915039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88001924082188066093943359 132002886123282099140915039)
  ·
    refine ⟨198004329184923148711372559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132002886123282099140915039 198004329184923148711372559)
    ·
      refine ⟨297006493777384723067058839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198004329184923148711372559 297006493777384723067058839)
      ·
        refine ⟨445509740666077084600588259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 297006493777384723067058839 445509740666077084600588259)
        ·
          refine ⟨668264610999115626900882389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 445509740666077084600588259 668264610999115626900882389)
          ·
            refine ⟨15662451820291772505489431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 668264610999115626900882389 15662451820291772505489431)
            ·
              refine ⟨23493677730437658758234147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15662451820291772505489431 23493677730437658758234147)
              ·
                refine ⟨35240516595656488137351221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23493677730437658758234147 35240516595656488137351221)
                ·
                  refine ⟨3303798430842795762876677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 35240516595656488137351221 3303798430842795762876677)
                  ·
                    refine ⟨619462205783024205539377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3303798430842795762876677 619462205783024205539377)
                    ·
                      rfl

theorem cell23_3619195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 1, 1, 5, 4].length) (baseStart_3619195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3619195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3619195 prefixEnd_3619195 := by exact prefixLift 3619195
  have htrace : WordTrace (prefixWord ++ tailWord_3619195) baseStart_3619195 baseEnd_3619195 := by
    simpa [prefixWord, tailWord_3619195, baseEnd_3619195] using wordTrace_append hprefix tailTrace_3619195
  have hstable : (prefixWord ++ tailWord_3619195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3619195).length < 2 ^ (prefixWord ++ tailWord_3619195).sum := by decide
  have hdescent : baseEnd_3619195 < baseStart_3619195 := by decide
  rcases family_descends (prefixWord ++ tailWord_3619195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3619229 : List Nat := [1, 4, 2, 1, 4, 1, 2, 1, 3, 4]
def baseStart_3619229 : Nat := 118140960795 + 3619229 * 2 ^ 59
def prefixEnd_3619229 : Nat := 4983230072969 + 3 ^ 40 * 3619229 * 2
def baseEnd_3619229 : Nat := 619468025230441827864325

theorem tailTrace_3619229 : CollatzResearch.WordTrace tailWord_3619229 prefixEnd_3619229 619468025230441827864325 := by
  unfold tailWord_3619229
  simp only [CollatzResearch.WordTrace]
  refine ⟨132004126205158922947652741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88002750803439281965101827 132004126205158922947652741)
  ·
    refine ⟨24750773663467298052684889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 132004126205158922947652741 24750773663467298052684889)
    ·
      refine ⟨18563080247600473539513667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24750773663467298052684889 18563080247600473539513667)
      ·
        refine ⟨27844620371400710309270501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18563080247600473539513667 27844620371400710309270501)
        ·
          refine ⟨5220866319637633182988219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27844620371400710309270501 5220866319637633182988219)
          ·
            refine ⟨7831299479456449774482329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5220866319637633182988219 7831299479456449774482329)
            ·
              refine ⟨5873474609592337330861747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7831299479456449774482329 5873474609592337330861747)
              ·
                refine ⟨8810211914388505996292621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5873474609592337330861747 8810211914388505996292621)
                ·
                  refine ⟨3303829467895689748609733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8810211914388505996292621 3303829467895689748609733)
                  ·
                    refine ⟨619468025230441827864325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3303829467895689748609733 619468025230441827864325)
                    ·
                      rfl

theorem cell23_3619229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 2, 1, 3, 4].length) (baseStart_3619229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3619229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3619229 prefixEnd_3619229 := by exact prefixLift 3619229
  have htrace : WordTrace (prefixWord ++ tailWord_3619229) baseStart_3619229 baseEnd_3619229 := by
    simpa [prefixWord, tailWord_3619229, baseEnd_3619229] using wordTrace_append hprefix tailTrace_3619229
  have hstable : (prefixWord ++ tailWord_3619229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3619229).length < 2 ^ (prefixWord ++ tailWord_3619229).sum := by decide
  have hdescent : baseEnd_3619229 < baseStart_3619229 := by decide
  rcases family_descends (prefixWord ++ tailWord_3619229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3619272 : List Nat := [2, 1, 3, 1, 3, 2, 2, 3, 1, 5]
def baseStart_3619272 : Nat := 118140960795 + 3619272 * 2 ^ 59
def prefixEnd_3619272 : Nat := 4983230072969 + 3 ^ 40 * 3619272 * 2
def baseEnd_3619272 : Nat := 619475385119822938451759

theorem tailTrace_3619272 : CollatzResearch.WordTrace tailWord_3619272 prefixEnd_3619272 619475385119822938451759 := by
  unfold tailWord_3619272
  simp only [CollatzResearch.WordTrace]
  refine ⟨66002847272001570645734035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88003796362668760860978713 66002847272001570645734035)
  ·
    refine ⟨99004270908002355968601053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66002847272001570645734035 99004270908002355968601053)
    ·
      refine ⟨37126601590500883488225395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 99004270908002355968601053 37126601590500883488225395)
      ·
        refine ⟨55689902385751325232338093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37126601590500883488225395 55689902385751325232338093)
        ·
          refine ⟨20883713394656746962126785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55689902385751325232338093 20883713394656746962126785)
          ·
            refine ⟨15662785045992560221595089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20883713394656746962126785 15662785045992560221595089)
            ·
              refine ⟨11747088784494420166196317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15662785045992560221595089 11747088784494420166196317)
              ·
                refine ⟨4405158294185407562323619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11747088784494420166196317 4405158294185407562323619)
                ·
                  refine ⟨6607737441278111343485429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4405158294185407562323619 6607737441278111343485429)
                  ·
                    refine ⟨619475385119822938451759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6607737441278111343485429 619475385119822938451759)
                    ·
                      rfl

theorem cell23_3619272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 2, 3, 1, 5].length) (baseStart_3619272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3619272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3619272 prefixEnd_3619272 := by exact prefixLift 3619272
  have htrace : WordTrace (prefixWord ++ tailWord_3619272) baseStart_3619272 baseEnd_3619272 := by
    simpa [prefixWord, tailWord_3619272, baseEnd_3619272] using wordTrace_append hprefix tailTrace_3619272
  have hstable : (prefixWord ++ tailWord_3619272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3619272).length < 2 ^ (prefixWord ++ tailWord_3619272).sum := by decide
  have hdescent : baseEnd_3619272 < baseStart_3619272 := by decide
  rcases family_descends (prefixWord ++ tailWord_3619272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3619275 : List Nat := [1, 1, 1, 1, 3, 3, 1, 2, 5, 1, 4]
def baseStart_3619275 : Nat := 118140960795 + 3619275 * 2 ^ 59
def prefixEnd_3619275 : Nat := 4983230072969 + 3 ^ 40 * 3619275 * 2
def baseEnd_3619275 : Nat := 1858427695801432303617763

theorem tailTrace_3619275 : CollatzResearch.WordTrace tailWord_3619275 prefixEnd_3619275 1858427695801432303617763 := by
  unfold tailWord_3619275
  simp only [CollatzResearch.WordTrace]
  refine ⟨132005803962992272803827279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88003869308661515202551519 132005803962992272803827279)
  ·
    refine ⟨198008705944488409205740919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132005803962992272803827279 198008705944488409205740919)
    ·
      refine ⟨297013058916732613808611379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198008705944488409205740919 297013058916732613808611379)
      ·
        refine ⟨445519588375098920712917069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 297013058916732613808611379 445519588375098920712917069)
        ·
          refine ⟨167069845640662095267343901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 445519588375098920712917069 167069845640662095267343901)
          ·
            refine ⟨62651192115248285725253963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 167069845640662095267343901 62651192115248285725253963)
            ·
              refine ⟨93976788172872428587880945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62651192115248285725253963 93976788172872428587880945)
              ·
                refine ⟨70482591129654321440910709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 93976788172872428587880945 70482591129654321440910709)
                ·
                  refine ⟨6607742918405092635085379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 70482591129654321440910709 6607742918405092635085379)
                  ·
                    refine ⟨9911614377607638952628069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6607742918405092635085379 9911614377607638952628069)
                    ·
                      refine ⟨1858427695801432303617763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9911614377607638952628069 1858427695801432303617763)
                      ·
                        rfl

theorem cell23_3619275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 2, 5, 1, 4].length) (baseStart_3619275 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3619275 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3619275 prefixEnd_3619275 := by exact prefixLift 3619275
  have htrace : WordTrace (prefixWord ++ tailWord_3619275) baseStart_3619275 baseEnd_3619275 := by
    simpa [prefixWord, tailWord_3619275, baseEnd_3619275] using wordTrace_append hprefix tailTrace_3619275
  have hstable : (prefixWord ++ tailWord_3619275).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3619275).length < 2 ^ (prefixWord ++ tailWord_3619275).sum := by decide
  have hdescent : baseEnd_3619275 < baseStart_3619275 := by decide
  rcases family_descends (prefixWord ++ tailWord_3619275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3619309 : List Nat := [1, 5, 1, 3, 1, 2, 1, 1, 3, 1, 4]
def baseStart_3619309 : Nat := 118140960795 + 3619309 * 2 ^ 59
def prefixEnd_3619309 : Nat := 4983230072969 + 3 ^ 40 * 3619309 * 2
def baseEnd_3619309 : Nat := 1858445154143685170592607

theorem tailTrace_3619309 : CollatzResearch.WordTrace tailWord_3619309 prefixEnd_3619309 1858445154143685170592607 := by
  unfold tailWord_3619309
  simp only [CollatzResearch.WordTrace]
  refine ⟨132007044044869096610564981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88004696029912731073709987 132007044044869096610564981)
  ·
    refine ⟨12375660379206477807240467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 132007044044869096610564981 12375660379206477807240467)
    ·
      refine ⟨18563490568809716710860701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12375660379206477807240467 18563490568809716710860701)
      ·
        refine ⟨6961308963303643766572763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18563490568809716710860701 6961308963303643766572763)
        ·
          refine ⟨10441963444955465649859145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6961308963303643766572763 10441963444955465649859145)
          ·
            refine ⟨7831472583716599237394359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10441963444955465649859145 7831472583716599237394359)
            ·
              refine ⟨11747208875574898856091539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7831472583716599237394359 11747208875574898856091539)
              ·
                refine ⟨17620813313362348284137309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11747208875574898856091539 17620813313362348284137309)
                ·
                  refine ⟨6607804992510880606551491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17620813313362348284137309 6607804992510880606551491)
                  ·
                    refine ⟨9911707488766320909827237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6607804992510880606551491 9911707488766320909827237)
                    ·
                      refine ⟨1858445154143685170592607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9911707488766320909827237 1858445154143685170592607)
                      ·
                        rfl

theorem cell23_3619309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 1, 1, 3, 1, 4].length) (baseStart_3619309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3619309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3619309 prefixEnd_3619309 := by exact prefixLift 3619309
  have htrace : WordTrace (prefixWord ++ tailWord_3619309) baseStart_3619309 baseEnd_3619309 := by
    simpa [prefixWord, tailWord_3619309, baseEnd_3619309] using wordTrace_append hprefix tailTrace_3619309
  have hstable : (prefixWord ++ tailWord_3619309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3619309).length < 2 ^ (prefixWord ++ tailWord_3619309).sum := by decide
  have hdescent : baseEnd_3619309 < baseStart_3619309 := by decide
  rcases family_descends (prefixWord ++ tailWord_3619309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3619312 : List Nat := [2, 1, 1, 1, 3, 3, 3, 1, 3, 2, 3]
def baseStart_3619312 : Nat := 118140960795 + 3619312 * 2 ^ 59
def prefixEnd_3619312 : Nat := 4983230072969 + 3 ^ 40 * 3619312 * 2
def baseEnd_3619312 : Nat := 1858446694585648658855093

theorem tailTrace_3619312 : CollatzResearch.WordTrace tailWord_3619312 prefixEnd_3619312 1858446694585648658855093 := by
  unfold tailWord_3619312
  simp only [CollatzResearch.WordTrace]
  refine ⟨66003576731929114061462095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88004768975905485415282793 66003576731929114061462095)
  ·
    refine ⟨99005365097893671092193143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66003576731929114061462095 99005365097893671092193143)
    ·
      refine ⟨148508047646840506638289715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99005365097893671092193143 148508047646840506638289715)
      ·
        refine ⟨222762071470260759957434573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148508047646840506638289715 222762071470260759957434573)
        ·
          refine ⟨83535776801347784984037965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 222762071470260759957434573 83535776801347784984037965)
          ·
            refine ⟨31325916300505419369014237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 83535776801347784984037965 31325916300505419369014237)
            ·
              refine ⟨11747218612689532263380339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31325916300505419369014237 11747218612689532263380339)
              ·
                refine ⟨17620827919034298395070509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11747218612689532263380339 17620827919034298395070509)
                ·
                  refine ⟨6607810469637861898151441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17620827919034298395070509 6607810469637861898151441)
                  ·
                    refine ⟨4955857852228396423613581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6607810469637861898151441 4955857852228396423613581)
                    ·
                      refine ⟨1858446694585648658855093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4955857852228396423613581 1858446694585648658855093)
                      ·
                        rfl

theorem cell23_3619312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 3, 1, 3, 2, 3].length) (baseStart_3619312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3619312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3619312 prefixEnd_3619312 := by exact prefixLift 3619312
  have htrace : WordTrace (prefixWord ++ tailWord_3619312) baseStart_3619312 baseEnd_3619312 := by
    simpa [prefixWord, tailWord_3619312, baseEnd_3619312] using wordTrace_append hprefix tailTrace_3619312
  have hstable : (prefixWord ++ tailWord_3619312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3619312).length < 2 ^ (prefixWord ++ tailWord_3619312).sum := by decide
  have hdescent : baseEnd_3619312 < baseStart_3619312 := by decide
  rcases family_descends (prefixWord ++ tailWord_3619312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3619329 : List Nat := [1, 2, 4, 1, 3, 3, 1, 1, 1, 1, 5]
def baseStart_3619329 : Nat := 118140960795 + 3619329 * 2 ^ 59
def prefixEnd_3619329 : Nat := 4983230072969 + 3 ^ 40 * 3619329 * 2
def baseEnd_3619329 : Nat := 1858455423756775092342515

theorem tailTrace_3619329 : CollatzResearch.WordTrace tailWord_3619329 prefixEnd_3619329 1858455423756775092342515 := by
  unfold tailWord_3619329
  simp only [CollatzResearch.WordTrace]
  refine ⟨132007773504796640026293041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88005182336531093350862027 132007773504796640026293041)
  ·
    refine ⟨99005830128597480019719781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132007773504796640026293041 99005830128597480019719781)
    ·
      refine ⟨18563593149112027503697459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 99005830128597480019719781 18563593149112027503697459)
      ·
        refine ⟨27845389723668041255546189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18563593149112027503697459 27845389723668041255546189)
        ·
          refine ⟨10442021146375515470829821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27845389723668041255546189 10442021146375515470829821)
          ·
            refine ⟨3915757929890818301561183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10442021146375515470829821 3915757929890818301561183)
            ·
              refine ⟨5873636894836227452341775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3915757929890818301561183 5873636894836227452341775)
              ·
                refine ⟨8810455342254341178512663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5873636894836227452341775 8810455342254341178512663)
                ·
                  refine ⟨13215683013381511767768995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8810455342254341178512663 13215683013381511767768995)
                  ·
                    refine ⟨19823524520072267651653493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13215683013381511767768995 19823524520072267651653493)
                    ·
                      refine ⟨1858455423756775092342515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19823524520072267651653493 1858455423756775092342515)
                      ·
                        rfl

theorem cell23_3619329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 3, 1, 1, 1, 1, 5].length) (baseStart_3619329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3619329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3619329 prefixEnd_3619329 := by exact prefixLift 3619329
  have htrace : WordTrace (prefixWord ++ tailWord_3619329) baseStart_3619329 baseEnd_3619329 := by
    simpa [prefixWord, tailWord_3619329, baseEnd_3619329] using wordTrace_append hprefix tailTrace_3619329
  have hstable : (prefixWord ++ tailWord_3619329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3619329).length < 2 ^ (prefixWord ++ tailWord_3619329).sum := by decide
  have hdescent : baseEnd_3619329 < baseStart_3619329 := by decide
  rcases family_descends (prefixWord ++ tailWord_3619329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3619386 : List Nat := [3, 1, 1, 1, 3, 4, 1, 3, 1, 3, 2]
def baseStart_3619386 : Nat := 118140960795 + 3619386 * 2 ^ 59
def prefixEnd_3619386 : Nat := 4983230072969 + 3 ^ 40 * 3619386 * 2
def baseEnd_3619386 : Nat := 1858484692154081369329753

theorem tailTrace_3619386 : CollatzResearch.WordTrace tailWord_3619386 prefixEnd_3619386 1858484692154081369329753 := by
  unfold tailWord_3619386
  simp only [CollatzResearch.WordTrace]
  refine ⟨33002463116397534690279503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88006568310393425840745341 33002463116397534690279503)
  ·
    refine ⟨49503694674596302035419255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33002463116397534690279503 49503694674596302035419255)
    ·
      refine ⟨74255542011894453053128883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49503694674596302035419255 74255542011894453053128883)
      ·
        refine ⟨111383313017841679579693325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74255542011894453053128883 111383313017841679579693325)
        ·
          refine ⟨41768742381690629842384997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 111383313017841679579693325 41768742381690629842384997)
          ·
            refine ⟨7831639196566993095447187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41768742381690629842384997 7831639196566993095447187)
            ·
              refine ⟨11747458794850489643170781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7831639196566993095447187 11747458794850489643170781)
              ·
                refine ⟨4405297048068933616189043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11747458794850489643170781 4405297048068933616189043)
                ·
                  refine ⟨6607945572103400424283565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4405297048068933616189043 6607945572103400424283565)
                  ·
                    refine ⟨2477979589538775159106337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6607945572103400424283565 2477979589538775159106337)
                    ·
                      refine ⟨1858484692154081369329753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2477979589538775159106337 1858484692154081369329753)
                      ·
                        rfl

theorem cell23_3619386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 1, 3, 1, 3, 2].length) (baseStart_3619386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3619386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3619386 prefixEnd_3619386 := by exact prefixLift 3619386
  have htrace : WordTrace (prefixWord ++ tailWord_3619386) baseStart_3619386 baseEnd_3619386 := by
    simpa [prefixWord, tailWord_3619386, baseEnd_3619386] using wordTrace_append hprefix tailTrace_3619386
  have hstable : (prefixWord ++ tailWord_3619386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3619386).length < 2 ^ (prefixWord ++ tailWord_3619386).sum := by decide
  have hdescent : baseEnd_3619386 < baseStart_3619386 := by decide
  rcases family_descends (prefixWord ++ tailWord_3619386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3619393 : List Nat := [1, 2, 5, 1, 1, 4, 1, 2, 2, 1, 3]
def baseStart_3619393 : Nat := 118140960795 + 3619393 * 2 ^ 59
def prefixEnd_3619393 : Nat := 4983230072969 + 3 ^ 40 * 3619393 * 2
def baseEnd_3619393 : Nat := 1858488286518662841942221

theorem tailTrace_3619393 : CollatzResearch.WordTrace tailWord_3619393 prefixEnd_3619393 1858488286518662841942221 := by
  unfold tailWord_3619393
  simp only [CollatzResearch.WordTrace]
  refine ⟨132010107776564778956622833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88006738517709852637748555 132010107776564778956622833)
  ·
    refine ⟨99007580832423584217467125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132010107776564778956622833 99007580832423584217467125)
    ·
      refine ⟨9281960703039711020387543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 99007580832423584217467125 9281960703039711020387543)
      ·
        refine ⟨13922941054559566530581315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9281960703039711020387543 13922941054559566530581315)
        ·
          refine ⟨20884411581839349795871973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13922941054559566530581315 20884411581839349795871973)
          ·
            refine ⟨3915827171594878086725995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20884411581839349795871973 3915827171594878086725995)
            ·
              refine ⟨5873740757392317130088993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3915827171594878086725995 5873740757392317130088993)
              ·
                refine ⟨4405305568044237847566745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5873740757392317130088993 4405305568044237847566745)
                ·
                  refine ⟨3303979176033178385675059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4405305568044237847566745 3303979176033178385675059)
                  ·
                    refine ⟨4955968764049767578512589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3303979176033178385675059 4955968764049767578512589)
                    ·
                      refine ⟨1858488286518662841942221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4955968764049767578512589 1858488286518662841942221)
                      ·
                        rfl

theorem cell23_3619393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 4, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 4, 1, 2, 2, 1, 3].length) (baseStart_3619393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3619393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3619393 prefixEnd_3619393 := by exact prefixLift 3619393
  have htrace : WordTrace (prefixWord ++ tailWord_3619393) baseStart_3619393 baseEnd_3619393 := by
    simpa [prefixWord, tailWord_3619393, baseEnd_3619393] using wordTrace_append hprefix tailTrace_3619393
  have hstable : (prefixWord ++ tailWord_3619393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3619393).length < 2 ^ (prefixWord ++ tailWord_3619393).sum := by decide
  have hdescent : baseEnd_3619393 < baseStart_3619393 := by decide
  rcases family_descends (prefixWord ++ tailWord_3619393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3619416 : List Nat := [2, 1, 2, 2, 1, 2, 2, 5, 2, 2, 2]
def baseStart_3619416 : Nat := 118140960795 + 3619416 * 2 ^ 59
def prefixEnd_3619416 : Nat := 4983230072969 + 3 ^ 40 * 3619416 * 2
def baseEnd_3619416 : Nat := 1858500096573716251954615

theorem tailTrace_3619416 : CollatzResearch.WordTrace tailWord_3619416 prefixEnd_3619416 1858500096573716251954615 := by
  unfold tailWord_3619416
  simp only [CollatzResearch.WordTrace]
  refine ⟨66005473327740726942355051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88007297770320969256473401 66005473327740726942355051)
  ·
    refine ⟨99008209991611090413532577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66005473327740726942355051 99008209991611090413532577)
    ·
      refine ⟨74256157493708317810149433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99008209991611090413532577 74256157493708317810149433)
      ·
        refine ⟨55692118120281238357612075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74256157493708317810149433 55692118120281238357612075)
        ·
          refine ⟨83538177180421857536418113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55692118120281238357612075 83538177180421857536418113)
          ·
            refine ⟨62653632885316393152313585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83538177180421857536418113 62653632885316393152313585)
            ·
              refine ⟨46990224663987294864235189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62653632885316393152313585 46990224663987294864235189)
              ·
                refine ⟨4405333562248808893522049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 46990224663987294864235189 4405333562248808893522049)
                ·
                  refine ⟨3304000171686606670141537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4405333562248808893522049 3304000171686606670141537)
                  ·
                    refine ⟨2478000128764955002606153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3304000171686606670141537 2478000128764955002606153)
                    ·
                      refine ⟨1858500096573716251954615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2478000128764955002606153 1858500096573716251954615)
                      ·
                        rfl

theorem cell23_3619416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 5, 2, 2, 2].length) (baseStart_3619416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3619416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3619416 prefixEnd_3619416 := by exact prefixLift 3619416
  have htrace : WordTrace (prefixWord ++ tailWord_3619416) baseStart_3619416 baseEnd_3619416 := by
    simpa [prefixWord, tailWord_3619416, baseEnd_3619416] using wordTrace_append hprefix tailTrace_3619416
  have hstable : (prefixWord ++ tailWord_3619416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3619416).length < 2 ^ (prefixWord ++ tailWord_3619416).sum := by decide
  have hdescent : baseEnd_3619416 < baseStart_3619416 := by decide
  rcases family_descends (prefixWord ++ tailWord_3619416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3619439 : List Nat := [1, 1, 2, 1, 3, 2, 5, 3, 5]
def baseStart_3619439 : Nat := 118140960795 + 3619439 * 2 ^ 59
def prefixEnd_3619439 : Nat := 4983230072969 + 3 ^ 40 * 3619439 * 2
def baseEnd_3619439 : Nat := 206501322958752184663001

theorem tailTrace_3619439 : CollatzResearch.WordTrace tailWord_3619439 prefixEnd_3619439 206501322958752184663001 := by
  unfold tailWord_3619439
  simp only [CollatzResearch.WordTrace]
  refine ⟨132011785534398128812797371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88007857022932085875198247 132011785534398128812797371)
  ·
    refine ⟨198017678301597193219196057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132011785534398128812797371 198017678301597193219196057)
    ·
      refine ⟨148513258726197894914397043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 198017678301597193219196057 148513258726197894914397043)
      ·
        refine ⟨222769888089296842371595565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148513258726197894914397043 222769888089296842371595565)
        ·
          refine ⟨83538708033486315889348337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 222769888089296842371595565 83538708033486315889348337)
          ·
            refine ⟨62654031025114736917011253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83538708033486315889348337 62654031025114736917011253)
            ·
              refine ⟨5873815408604506585969805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 62654031025114736917011253 5873815408604506585969805)
              ·
                refine ⟨2202680778226689969738677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5873815408604506585969805 2202680778226689969738677)
                ·
                  refine ⟨206501322958752184663001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2202680778226689969738677 206501322958752184663001)
                  ·
                    rfl

theorem cell23_3619439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 5, 3, 5].length) (baseStart_3619439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3619439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3619439 prefixEnd_3619439 := by exact prefixLift 3619439
  have htrace : WordTrace (prefixWord ++ tailWord_3619439) baseStart_3619439 baseEnd_3619439 := by
    simpa [prefixWord, tailWord_3619439, baseEnd_3619439] using wordTrace_append hprefix tailTrace_3619439
  have hstable : (prefixWord ++ tailWord_3619439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3619439).length < 2 ^ (prefixWord ++ tailWord_3619439).sum := by decide
  have hdescent : baseEnd_3619439 < baseStart_3619439 := by decide
  rcases family_descends (prefixWord ++ tailWord_3619439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3619452 : List Nat := [2, 2, 2, 1, 1, 2, 3, 1, 4, 5]
def baseStart_3619452 : Nat := 118140960795 + 3619452 * 2 ^ 59
def prefixEnd_3619452 : Nat := 4983230072969 + 3 ^ 40 * 3619452 * 2
def baseEnd_3619452 : Nat := 619506193959092703701483

theorem tailTrace_3619452 : CollatzResearch.WordTrace tailWord_3619452 prefixEnd_3619452 619506193959092703701483 := by
  unfold tailWord_3619452
  simp only [CollatzResearch.WordTrace]
  refine ⟨66006129841675516016510305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88008173122234021355347073 66006129841675516016510305)
  ·
    refine ⟨49504597381256637012382729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66006129841675516016510305 49504597381256637012382729)
    ·
      refine ⟨37128448035942477759287047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49504597381256637012382729 37128448035942477759287047)
      ·
        refine ⟨55692672053913716638930571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37128448035942477759287047 55692672053913716638930571)
        ·
          refine ⟨83539008080870574958395857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55692672053913716638930571 83539008080870574958395857)
          ·
            refine ⟨62654256060652931218796893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83539008080870574958395857 62654256060652931218796893)
            ·
              refine ⟨23495346022744849207048835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62654256060652931218796893 23495346022744849207048835)
              ·
                refine ⟨35243019034117273810573253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23495346022744849207048835 35243019034117273810573253)
                ·
                  refine ⟨6608066068896988839482485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35243019034117273810573253 6608066068896988839482485)
                  ·
                    refine ⟨619506193959092703701483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6608066068896988839482485 619506193959092703701483)
                    ·
                      rfl

theorem cell23_3619452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 3, 1, 4, 5].length) (baseStart_3619452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3619452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3619452 prefixEnd_3619452 := by exact prefixLift 3619452
  have htrace : WordTrace (prefixWord ++ tailWord_3619452) baseStart_3619452 baseEnd_3619452 := by
    simpa [prefixWord, tailWord_3619452, baseEnd_3619452] using wordTrace_append hprefix tailTrace_3619452
  have hstable : (prefixWord ++ tailWord_3619452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3619452).length < 2 ^ (prefixWord ++ tailWord_3619452).sum := by decide
  have hdescent : baseEnd_3619452 < baseStart_3619452 := by decide
  rcases family_descends (prefixWord ++ tailWord_3619452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3619456 : List Nat := [2, 1, 1, 2, 1, 6, 3, 2, 5]
def baseStart_3619456 : Nat := 118140960795 + 3619456 * 2 ^ 59
def prefixEnd_3619456 : Nat := 4983230072969 + 3 ^ 40 * 3619456 * 2
def baseEnd_3619456 : Nat := 206502292866655121717159

theorem tailTrace_3619456 : CollatzResearch.WordTrace tailWord_3619456 prefixEnd_3619456 206502292866655121717159 := by
  unfold tailWord_3619456
  simp only [CollatzResearch.WordTrace]
  refine ⟨66006202787668270358083111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88008270383557693810777481 66006202787668270358083111)
  ·
    refine ⟨99009304181502405537124667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66006202787668270358083111 99009304181502405537124667)
    ·
      refine ⟨148513956272253608305687001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99009304181502405537124667 148513956272253608305687001)
      ·
        refine ⟨111385467204190206229265251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 148513956272253608305687001 111385467204190206229265251)
        ·
          refine ⟨167078200806285309343897877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111385467204190206229265251 167078200806285309343897877)
          ·
            refine ⟨7831790662794623875495213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 167078200806285309343897877 7831790662794623875495213)
            ·
              refine ⟨2936921498547983953310705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7831790662794623875495213 2936921498547983953310705)
              ·
                refine ⟨2202691123910987964983029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2936921498547983953310705 2202691123910987964983029)
                ·
                  refine ⟨206502292866655121717159, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2202691123910987964983029 206502292866655121717159)
                  ·
                    rfl

theorem cell23_3619456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 3, 2, 5].length) (baseStart_3619456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3619456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3619456 prefixEnd_3619456 := by exact prefixLift 3619456
  have htrace : WordTrace (prefixWord ++ tailWord_3619456) baseStart_3619456 baseEnd_3619456 := by
    simpa [prefixWord, tailWord_3619456, baseEnd_3619456] using wordTrace_append hprefix tailTrace_3619456
  have hstable : (prefixWord ++ tailWord_3619456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3619456).length < 2 ^ (prefixWord ++ tailWord_3619456).sum := by decide
  have hdescent : baseEnd_3619456 < baseStart_3619456 := by decide
  rcases family_descends (prefixWord ++ tailWord_3619456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3619486 : List Nat := [4, 3, 1, 1, 1, 1, 4, 1, 2, 5]
def baseStart_3619486 : Nat := 118140960795 + 3619486 * 2 ^ 59
def prefixEnd_3619486 : Nat := 4983230072969 + 3 ^ 40 * 3619486 * 2
def baseEnd_3619486 : Nat := 619512013406510326026431

theorem tailTrace_3619486 : CollatzResearch.WordTrace tailWord_3619486 prefixEnd_3619486 619512013406510326026431 := by
  unfold tailWord_3619486
  simp only [CollatzResearch.WordTrace]
  refine ⟨16501687470653481979969789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 88008999843485237226505541 16501687470653481979969789)
  ·
    refine ⟨6188132801495055742488671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16501687470653481979969789 6188132801495055742488671)
    ·
      refine ⟨9282199202242583613733007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6188132801495055742488671 9282199202242583613733007)
      ·
        refine ⟨13923298803363875420599511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9282199202242583613733007 13923298803363875420599511)
        ·
          refine ⟨20884948205045813130899267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13923298803363875420599511 20884948205045813130899267)
          ·
            refine ⟨31327422307568719696348901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20884948205045813130899267 31327422307568719696348901)
            ·
              refine ⟨5873891682669134943065419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31327422307568719696348901 5873891682669134943065419)
              ·
                refine ⟨8810837524003702414598129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5873891682669134943065419 8810837524003702414598129)
                ·
                  refine ⟨6608128143002776810948597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8810837524003702414598129 6608128143002776810948597)
                  ·
                    refine ⟨619512013406510326026431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6608128143002776810948597 619512013406510326026431)
                    ·
                      rfl

theorem cell23_3619486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 4, 1, 2, 5].length) (baseStart_3619486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3619486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3619486 prefixEnd_3619486 := by exact prefixLift 3619486
  have htrace : WordTrace (prefixWord ++ tailWord_3619486) baseStart_3619486 baseEnd_3619486 := by
    simpa [prefixWord, tailWord_3619486, baseEnd_3619486] using wordTrace_append hprefix tailTrace_3619486
  have hstable : (prefixWord ++ tailWord_3619486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3619486).length < 2 ^ (prefixWord ++ tailWord_3619486).sum := by decide
  have hdescent : baseEnd_3619486 < baseStart_3619486 := by decide
  rcases family_descends (prefixWord ++ tailWord_3619486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3619540 : List Nat := [2, 4, 1, 3, 3, 1, 1, 1, 2, 1, 4]
def baseStart_3619540 : Nat := 118140960795 + 3619540 * 2 ^ 59
def prefixEnd_3619540 : Nat := 4983230072969 + 3 ^ 40 * 3619540 * 2
def baseEnd_3619540 : Nat := 1858563768174873766804045

theorem tailTrace_3619540 : CollatzResearch.WordTrace tailWord_3619540 prefixEnd_3619540 1858563768174873766804045 := by
  unfold tailWord_3619540
  simp only [CollatzResearch.WordTrace]
  refine ⟨66007734653516111531112037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88010312871354815374816049 66007734653516111531112037)
  ·
    refine ⟨12376450247534270912083507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 66007734653516111531112037 12376450247534270912083507)
    ·
      refine ⟨18564675371301406368125261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12376450247534270912083507 18564675371301406368125261)
      ·
        refine ⟨6961753264238027388046973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18564675371301406368125261 6961753264238027388046973)
        ·
          refine ⟨2610657474089260270517615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6961753264238027388046973 2610657474089260270517615)
          ·
            refine ⟨3915986211133890405776423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2610657474089260270517615 3915986211133890405776423)
            ·
              refine ⟨5873979316700835608664635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3915986211133890405776423 5873979316700835608664635)
              ·
                refine ⟨8810968975051253412996953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5873979316700835608664635 8810968975051253412996953)
                ·
                  refine ⟨6608226731288440059747715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8810968975051253412996953 6608226731288440059747715)
                  ·
                    refine ⟨9912340096932660089621573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6608226731288440059747715 9912340096932660089621573)
                    ·
                      refine ⟨1858563768174873766804045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9912340096932660089621573 1858563768174873766804045)
                      ·
                        rfl

theorem cell23_3619540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 3, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 3, 1, 1, 1, 2, 1, 4].length) (baseStart_3619540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3619540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3619540 prefixEnd_3619540 := by exact prefixLift 3619540
  have htrace : WordTrace (prefixWord ++ tailWord_3619540) baseStart_3619540 baseEnd_3619540 := by
    simpa [prefixWord, tailWord_3619540, baseEnd_3619540] using wordTrace_append hprefix tailTrace_3619540
  have hstable : (prefixWord ++ tailWord_3619540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3619540).length < 2 ^ (prefixWord ++ tailWord_3619540).sum := by decide
  have hdescent : baseEnd_3619540 < baseStart_3619540 := by decide
  rcases family_descends (prefixWord ++ tailWord_3619540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3619552 : List Nat := [2, 1, 1, 3, 1, 2, 1, 1, 2, 4, 5]
def baseStart_3619552 : Nat := 118140960795 + 3619552 * 2 ^ 59
def prefixEnd_3619552 : Nat := 4983230072969 + 3 ^ 40 * 3619552 * 2
def baseEnd_3619552 : Nat := 1858569929942727719853989

theorem tailTrace_3619552 : CollatzResearch.WordTrace tailWord_3619552 prefixEnd_3619552 1858569929942727719853989 := by
  unfold tailWord_3619552
  simp only [CollatzResearch.WordTrace]
  refine ⟨66007953491494374555830455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88010604655325832741107273 66007953491494374555830455)
  ·
    refine ⟨99011930237241561833745683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66007953491494374555830455 99011930237241561833745683)
    ·
      refine ⟨148517895355862342750618525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99011930237241561833745683 148517895355862342750618525)
      ·
        refine ⟨55694210758448378531481947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 148517895355862342750618525 55694210758448378531481947)
        ·
          refine ⟨83541316137672567797222921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55694210758448378531481947 83541316137672567797222921)
          ·
            refine ⟨62655987103254425847917191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83541316137672567797222921 62655987103254425847917191)
            ·
              refine ⟨93983980654881638771875787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62655987103254425847917191 93983980654881638771875787)
              ·
                refine ⟨140975970982322458157813681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 93983980654881638771875787 140975970982322458157813681)
                ·
                  refine ⟨105731978236741843618360261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 140975970982322458157813681 105731978236741843618360261)
                  ·
                    refine ⟨19824745919389095678442549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 105731978236741843618360261 19824745919389095678442549)
                    ·
                      refine ⟨1858569929942727719853989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19824745919389095678442549 1858569929942727719853989)
                      ·
                        rfl

theorem cell23_3619552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 1, 2, 4, 5].length) (baseStart_3619552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3619552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3619552 prefixEnd_3619552 := by exact prefixLift 3619552
  have htrace : WordTrace (prefixWord ++ tailWord_3619552) baseStart_3619552 baseEnd_3619552 := by
    simpa [prefixWord, tailWord_3619552, baseEnd_3619552] using wordTrace_append hprefix tailTrace_3619552
  have hstable : (prefixWord ++ tailWord_3619552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3619552).length < 2 ^ (prefixWord ++ tailWord_3619552).sum := by decide
  have hdescent : baseEnd_3619552 < baseStart_3619552 := by decide
  rcases family_descends (prefixWord ++ tailWord_3619552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3619607 : List Nat := [1, 1, 3, 4, 3, 2, 1, 3, 1, 1, 3]
def baseStart_3619607 : Nat := 118140960795 + 3619607 * 2 ^ 59
def prefixEnd_3619607 : Nat := 4983230072969 + 3 ^ 40 * 3619607 * 2
def baseEnd_3619607 : Nat := 1858598171378725004666237

theorem tailTrace_3619607 : CollatzResearch.WordTrace tailWord_3619607 prefixEnd_3619607 1858598171378725004666237 := by
  unfold tailWord_3619607
  simp only [CollatzResearch.WordTrace]
  refine ⟨132017912997789493504913075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88011941998526329003275383 132017912997789493504913075)
  ·
    refine ⟨198026869496684240257369613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132017912997789493504913075 198026869496684240257369613)
    ·
      refine ⟨74260076061256590096513605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 198026869496684240257369613 74260076061256590096513605)
      ·
        refine ⟨13923764261485610643096301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 74260076061256590096513605 13923764261485610643096301)
        ·
          refine ⟨5221411598057103991161113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13923764261485610643096301 5221411598057103991161113)
          ·
            refine ⟨3916058698542827993370835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5221411598057103991161113 3916058698542827993370835)
            ·
              refine ⟨5874088047814241990056253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3916058698542827993370835 5874088047814241990056253)
              ·
                refine ⟨2202783017930340746271095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5874088047814241990056253 2202783017930340746271095)
                ·
                  refine ⟨3304174526895511119406643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2202783017930340746271095 3304174526895511119406643)
                  ·
                    refine ⟨4956261790343266679109965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3304174526895511119406643 4956261790343266679109965)
                    ·
                      refine ⟨1858598171378725004666237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4956261790343266679109965 1858598171378725004666237)
                      ·
                        rfl

theorem cell23_3619607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 2, 1, 3, 1, 1, 3].length) (baseStart_3619607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3619607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3619607 prefixEnd_3619607 := by exact prefixLift 3619607
  have htrace : WordTrace (prefixWord ++ tailWord_3619607) baseStart_3619607 baseEnd_3619607 := by
    simpa [prefixWord, tailWord_3619607, baseEnd_3619607] using wordTrace_append hprefix tailTrace_3619607
  have hstable : (prefixWord ++ tailWord_3619607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3619607).length < 2 ^ (prefixWord ++ tailWord_3619607).sum := by decide
  have hdescent : baseEnd_3619607 < baseStart_3619607 := by decide
  rcases family_descends (prefixWord ++ tailWord_3619607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3619616 : List Nat := [2, 1, 1, 5, 1, 3, 2, 1, 1, 1, 5]
def baseStart_3619616 : Nat := 118140960795 + 3619616 * 2 ^ 59
def prefixEnd_3619616 : Nat := 4983230072969 + 3 ^ 40 * 3619616 * 2
def baseEnd_3619616 : Nat := 1858602792704615469453695

theorem tailTrace_3619616 : CollatzResearch.WordTrace tailWord_3619616 prefixEnd_3619616 1858602792704615469453695 := by
  unfold tailWord_3619616
  simp only [CollatzResearch.WordTrace]
  refine ⟨66009120627378444020995351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88012160836504592027993801 66009120627378444020995351)
  ·
    refine ⟨99013680941067666031493027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66009120627378444020995351 99013680941067666031493027)
    ·
      refine ⟨148520521411601499047239541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99013680941067666031493027 148520521411601499047239541)
      ·
        refine ⟨13923798882337640535678707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 148520521411601499047239541 13923798882337640535678707)
        ·
          refine ⟨20885698323506460803518061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13923798882337640535678707 20885698323506460803518061)
          ·
            refine ⟨7832136871314922801319273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20885698323506460803518061 7832136871314922801319273)
            ·
              refine ⟨5874102653486192100989455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7832136871314922801319273 5874102653486192100989455)
              ·
                refine ⟨8811153980229288151484183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5874102653486192100989455 8811153980229288151484183)
                ·
                  refine ⟨13216730970343932227226275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8811153980229288151484183 13216730970343932227226275)
                  ·
                    refine ⟨19825096455515898340839413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13216730970343932227226275 19825096455515898340839413)
                    ·
                      refine ⟨1858602792704615469453695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19825096455515898340839413 1858602792704615469453695)
                      ·
                        rfl

theorem cell23_3619616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 2, 1, 1, 1, 5].length) (baseStart_3619616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3619616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3619616 prefixEnd_3619616 := by exact prefixLift 3619616
  have htrace : WordTrace (prefixWord ++ tailWord_3619616) baseStart_3619616 baseEnd_3619616 := by
    simpa [prefixWord, tailWord_3619616, baseEnd_3619616] using wordTrace_append hprefix tailTrace_3619616
  have hstable : (prefixWord ++ tailWord_3619616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3619616).length < 2 ^ (prefixWord ++ tailWord_3619616).sum := by decide
  have hdescent : baseEnd_3619616 < baseStart_3619616 := by decide
  rcases family_descends (prefixWord ++ tailWord_3619616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3619679 : List Nat := [1, 1, 2, 3, 1, 3, 2, 2, 2, 6]
def baseStart_3619679 : Nat := 118140960795 + 3619679 * 2 ^ 59
def prefixEnd_3619679 : Nat := 4983230072969 + 3 ^ 40 * 3619679 * 2
def baseEnd_3619679 : Nat := 619545047328616240988635

theorem tailTrace_3619679 : CollatzResearch.WordTrace tailWord_3619679 prefixEnd_3619679 619545047328616240988635 := by
  unfold tailWord_3619679
  simp only [CollatzResearch.WordTrace]
  refine ⟨132020539053528649801534091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88013692702352433201022727 132020539053528649801534091)
  ·
    refine ⟨198030808580292974702301137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132020539053528649801534091 198030808580292974702301137)
    ·
      refine ⟨148523106435219731026725853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 198030808580292974702301137 148523106435219731026725853)
      ·
        refine ⟨55696164913207399135022195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 148523106435219731026725853 55696164913207399135022195)
        ·
          refine ⟨83544247369811098702533293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55696164913207399135022195 83544247369811098702533293)
          ·
            refine ⟨31329092763679162013449985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 83544247369811098702533293 31329092763679162013449985)
            ·
              refine ⟨23496819572759371510087489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31329092763679162013449985 23496819572759371510087489)
              ·
                refine ⟨17622614679569528632565617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23496819572759371510087489 17622614679569528632565617)
                ·
                  refine ⟨13216961009677146474424213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17622614679569528632565617 13216961009677146474424213)
                  ·
                    refine ⟨619545047328616240988635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13216961009677146474424213 619545047328616240988635)
                    ·
                      rfl

theorem cell23_3619679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 2, 2, 2, 6].length) (baseStart_3619679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3619679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3619679 prefixEnd_3619679 := by exact prefixLift 3619679
  have htrace : WordTrace (prefixWord ++ tailWord_3619679) baseStart_3619679 baseEnd_3619679 := by
    simpa [prefixWord, tailWord_3619679, baseEnd_3619679] using wordTrace_append hprefix tailTrace_3619679
  have hstable : (prefixWord ++ tailWord_3619679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3619679).length < 2 ^ (prefixWord ++ tailWord_3619679).sum := by decide
  have hdescent : baseEnd_3619679 < baseStart_3619679 := by decide
  rcases family_descends (prefixWord ++ tailWord_3619679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3619699 : List Nat := [1, 1, 1, 2, 2, 1, 5, 1, 1, 4, 4]
def baseStart_3619699 : Nat := 118140960795 + 3619699 * 2 ^ 59
def prefixEnd_3619699 : Nat := 4983230072969 + 3 ^ 40 * 3619699 * 2
def baseEnd_3619699 : Nat := 1858645411598938644715813

theorem tailTrace_3619699 : CollatzResearch.WordTrace tailWord_3619699 prefixEnd_3619699 1858645411598938644715813 := by
  unfold tailWord_3619699
  simp only [CollatzResearch.WordTrace]
  refine ⟨132021268513456193217262151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88014179008970795478174767 132021268513456193217262151)
  ·
    refine ⟨198031902770184289825893227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132021268513456193217262151 198031902770184289825893227)
    ·
      refine ⟨297047854155276434738839841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198031902770184289825893227 297047854155276434738839841)
      ·
        refine ⟨222785890616457326054129881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 297047854155276434738839841 222785890616457326054129881)
        ·
          refine ⟨167089417962342994540597411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 222785890616457326054129881 167089417962342994540597411)
          ·
            refine ⟨250634126943514491810896117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 167089417962342994540597411 250634126943514491810896117)
            ·
              refine ⟨23496949400954483607271511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 250634126943514491810896117 23496949400954483607271511)
              ·
                refine ⟨35245424101431725410907267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23496949400954483607271511 35245424101431725410907267)
                ·
                  refine ⟨52868136152147588116360901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35245424101431725410907267 52868136152147588116360901)
                  ·
                    refine ⟨9912775528527672771817669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 52868136152147588116360901 9912775528527672771817669)
                    ·
                      refine ⟨1858645411598938644715813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9912775528527672771817669 1858645411598938644715813)
                      ·
                        rfl

theorem cell23_3619699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 5, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 5, 1, 1, 4, 4].length) (baseStart_3619699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3619699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3619699 prefixEnd_3619699 := by exact prefixLift 3619699
  have htrace : WordTrace (prefixWord ++ tailWord_3619699) baseStart_3619699 baseEnd_3619699 := by
    simpa [prefixWord, tailWord_3619699, baseEnd_3619699] using wordTrace_append hprefix tailTrace_3619699
  have hstable : (prefixWord ++ tailWord_3619699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3619699).length < 2 ^ (prefixWord ++ tailWord_3619699).sum := by decide
  have hdescent : baseEnd_3619699 < baseStart_3619699 := by decide
  rcases family_descends (prefixWord ++ tailWord_3619699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3619709 : List Nat := [1, 4, 1, 1, 2, 1, 3, 1, 9]
def baseStart_3619709 : Nat := 118140960795 + 3619709 * 2 ^ 59
def prefixEnd_3619709 : Nat := 4983230072969 + 3 ^ 40 * 3619709 * 2
def baseEnd_3619709 : Nat := 206516727378387067287863

theorem tailTrace_3619709 : CollatzResearch.WordTrace tailWord_3619709 prefixEnd_3619709 206516727378387067287863 := by
  unfold tailWord_3619709
  simp only [CollatzResearch.WordTrace]
  refine ⟨132021633243419964925126181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88014422162279976616750787 132021633243419964925126181)
  ·
    refine ⟨24754056233141243423461159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 132021633243419964925126181 24754056233141243423461159)
    ·
      refine ⟨37131084349711865135191739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24754056233141243423461159 37131084349711865135191739)
      ·
        refine ⟨55696626524567797702787609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37131084349711865135191739 55696626524567797702787609)
        ·
          refine ⟨41772469893425848277090707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55696626524567797702787609 41772469893425848277090707)
          ·
            refine ⟨62658704840138772415636061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41772469893425848277090707 62658704840138772415636061)
            ·
              refine ⟨23497014315052039655863523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62658704840138772415636061 23497014315052039655863523)
              ·
                refine ⟨35245521472578059483795285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23497014315052039655863523 35245521472578059483795285)
                ·
                  refine ⟨206516727378387067287863, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 35245521472578059483795285 206516727378387067287863)
                  ·
                    rfl

theorem cell23_3619709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 3, 1, 9].length) (baseStart_3619709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3619709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3619709 prefixEnd_3619709 := by exact prefixLift 3619709
  have htrace : WordTrace (prefixWord ++ tailWord_3619709) baseStart_3619709 baseEnd_3619709 := by
    simpa [prefixWord, tailWord_3619709, baseEnd_3619709] using wordTrace_append hprefix tailTrace_3619709
  have hstable : (prefixWord ++ tailWord_3619709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3619709).length < 2 ^ (prefixWord ++ tailWord_3619709).sum := by decide
  have hdescent : baseEnd_3619709 < baseStart_3619709 := by decide
  rcases family_descends (prefixWord ++ tailWord_3619709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3619743 : List Nat := [1, 1, 2, 5, 2, 1, 2, 4, 5]
def baseStart_3619743 : Nat := 118140960795 + 3619743 * 2 ^ 59
def prefixEnd_3619743 : Nat := 4983230072969 + 3 ^ 40 * 3619743 * 2
def baseEnd_3619743 : Nat := 206518667194192941396179

theorem tailTrace_3619743 : CollatzResearch.WordTrace tailWord_3619743 prefixEnd_3619743 206518667194192941396179 := by
  unfold tailWord_3619743
  simp only [CollatzResearch.WordTrace]
  refine ⟨132022873325296788731863883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88015248883531192487909255 132022873325296788731863883)
  ·
    refine ⟨198034309987945183097795825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132022873325296788731863883 198034309987945183097795825)
    ·
      refine ⟨148525732490958887323346869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 198034309987945183097795825 148525732490958887323346869)
      ·
        refine ⟨13924287421027395686563769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 148525732490958887323346869 13924287421027395686563769)
        ·
          refine ⟨10443215565770546764922827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13924287421027395686563769 10443215565770546764922827)
          ·
            refine ⟨15664823348655820147384241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10443215565770546764922827 15664823348655820147384241)
            ·
              refine ⟨11748617511491865110538181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15664823348655820147384241 11748617511491865110538181)
              ·
                refine ⟨2202865783404724708225909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11748617511491865110538181 2202865783404724708225909)
                ·
                  refine ⟨206518667194192941396179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2202865783404724708225909 206518667194192941396179)
                  ·
                    rfl

theorem cell23_3619743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 2, 4, 5].length) (baseStart_3619743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3619743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3619743 prefixEnd_3619743 := by exact prefixLift 3619743
  have htrace : WordTrace (prefixWord ++ tailWord_3619743) baseStart_3619743 baseEnd_3619743 := by
    simpa [prefixWord, tailWord_3619743, baseEnd_3619743] using wordTrace_append hprefix tailTrace_3619743
  have hstable : (prefixWord ++ tailWord_3619743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3619743).length < 2 ^ (prefixWord ++ tailWord_3619743).sum := by decide
  have hdescent : baseEnd_3619743 < baseStart_3619743 := by decide
  rcases family_descends (prefixWord ++ tailWord_3619743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3619776 : List Nat := [2, 1, 1, 2, 3, 3, 2, 1, 1, 3, 4]
def baseStart_3619776 : Nat := 118140960795 + 3619776 * 2 ^ 59
def prefixEnd_3619776 : Nat := 4983230072969 + 3 ^ 40 * 3619776 * 2
def baseEnd_3619776 : Nat := 1858684949609334843452959

theorem tailTrace_3619776 : CollatzResearch.WordTrace tailWord_3619776 prefixEnd_3619776 1858684949609334843452959 := by
  unfold tailWord_3619776
  simp only [CollatzResearch.WordTrace]
  refine ⟨66012038467088617683907591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88016051289451490245210121 66012038467088617683907591)
  ·
    refine ⟨99018057700632926525861387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66012038467088617683907591 99018057700632926525861387)
    ·
      refine ⟨148527086550949389788792081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99018057700632926525861387 148527086550949389788792081)
      ·
        refine ⟨111395314913212042341594061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 148527086550949389788792081 111395314913212042341594061)
        ·
          refine ⟨41773243092454515878097773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 111395314913212042341594061 41773243092454515878097773)
          ·
            refine ⟨15664966159670443454286665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41773243092454515878097773 15664966159670443454286665)
            ·
              refine ⟨11748724619752832590714999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15664966159670443454286665 11748724619752832590714999)
              ·
                refine ⟨17623086929629248886072499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11748724619752832590714999 17623086929629248886072499)
                ·
                  refine ⟨26434630394443873329108749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17623086929629248886072499 26434630394443873329108749)
                  ·
                    refine ⟨9912986397916452498415781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26434630394443873329108749 9912986397916452498415781)
                    ·
                      refine ⟨1858684949609334843452959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9912986397916452498415781 1858684949609334843452959)
                      ·
                        rfl

theorem cell23_3619776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 2, 1, 1, 3, 4].length) (baseStart_3619776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3619776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3619776 prefixEnd_3619776 := by exact prefixLift 3619776
  have htrace : WordTrace (prefixWord ++ tailWord_3619776) baseStart_3619776 baseEnd_3619776 := by
    simpa [prefixWord, tailWord_3619776, baseEnd_3619776] using wordTrace_append hprefix tailTrace_3619776
  have hstable : (prefixWord ++ tailWord_3619776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3619776).length < 2 ^ (prefixWord ++ tailWord_3619776).sum := by decide
  have hdescent : baseEnd_3619776 < baseStart_3619776 := by decide
  rcases family_descends (prefixWord ++ tailWord_3619776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3619830 : List Nat := [5, 1, 1, 1, 3, 1, 1, 3, 2, 2, 3]
def baseStart_3619830 : Nat := 118140960795 + 3619830 * 2 ^ 59
def prefixEnd_3619830 : Nat := 4983230072969 + 3 ^ 40 * 3619830 * 2
def baseEnd_3619830 : Nat := 1858712677564677632177711

theorem tailTrace_3619830 : CollatzResearch.WordTrace tailWord_3619830 prefixEnd_3619830 1858712677564677632177711 := by
  unfold tailWord_3619830
  simp only [CollatzResearch.WordTrace]
  refine ⟨8251627904748850161892559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 88017364317321068393520629 8251627904748850161892559)
  ·
    refine ⟨12377441857123275242838839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8251627904748850161892559 12377441857123275242838839)
    ·
      refine ⟨18566162785684912864258259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12377441857123275242838839 18566162785684912864258259)
      ·
        refine ⟨27849244178527369296387389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18566162785684912864258259 27849244178527369296387389)
        ·
          refine ⟨10443466566947763486145271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27849244178527369296387389 10443466566947763486145271)
          ·
            refine ⟨15665199850421645229217907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10443466566947763486145271 15665199850421645229217907)
            ·
              refine ⟨23497799775632467843826861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15665199850421645229217907 23497799775632467843826861)
              ·
                refine ⟨8811674915862175441435073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23497799775632467843826861 8811674915862175441435073)
                ·
                  refine ⟨6608756186896631581076305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8811674915862175441435073 6608756186896631581076305)
                  ·
                    refine ⟨4956567140172473685807229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6608756186896631581076305 4956567140172473685807229)
                    ·
                      refine ⟨1858712677564677632177711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4956567140172473685807229 1858712677564677632177711)
                      ·
                        rfl

theorem cell23_3619830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 1, 3, 2, 2, 3].length) (baseStart_3619830 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3619830 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3619830 prefixEnd_3619830 := by exact prefixLift 3619830
  have htrace : WordTrace (prefixWord ++ tailWord_3619830) baseStart_3619830 baseEnd_3619830 := by
    simpa [prefixWord, tailWord_3619830, baseEnd_3619830] using wordTrace_append hprefix tailTrace_3619830
  have hstable : (prefixWord ++ tailWord_3619830).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3619830).length < 2 ^ (prefixWord ++ tailWord_3619830).sum := by decide
  have hdescent : baseEnd_3619830 < baseStart_3619830 := by decide
  rcases family_descends (prefixWord ++ tailWord_3619830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3619854 : List Nat := [4, 1, 1, 2, 2, 4, 2, 2, 1, 4]
def baseStart_3619854 : Nat := 118140960795 + 3619854 * 2 ^ 59
def prefixEnd_3619854 : Nat := 4983230072969 + 3 ^ 40 * 3619854 * 2
def baseEnd_3619854 : Nat := 619575000366795179425867

theorem tailTrace_3619854 : CollatzResearch.WordTrace tailWord_3619854 prefixEnd_3619854 619575000366795179425867 := by
  unfold tailWord_3619854
  simp only [CollatzResearch.WordTrace]
  refine ⟨16503365228486831836144327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 88017947885263103126103077 16503365228486831836144327)
  ·
    refine ⟨24755047842730247754216491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16503365228486831836144327 24755047842730247754216491)
    ·
      refine ⟨37132571764095371631324737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24755047842730247754216491 37132571764095371631324737)
      ·
        refine ⟨27849428823071528723493553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37132571764095371631324737 27849428823071528723493553)
        ·
          refine ⟨20887071617303646542620165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27849428823071528723493553 20887071617303646542620165)
          ·
            refine ⟨3916325928244433726741281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20887071617303646542620165 3916325928244433726741281)
            ·
              refine ⟨2937244446183325295055961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3916325928244433726741281 2937244446183325295055961)
              ·
                refine ⟨2202933334637493971291971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2937244446183325295055961 2202933334637493971291971)
                ·
                  refine ⟨3304400001956240956937957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2202933334637493971291971 3304400001956240956937957)
                  ·
                    refine ⟨619575000366795179425867, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3304400001956240956937957 619575000366795179425867)
                    ·
                      rfl

theorem cell23_3619854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 4, 2, 2, 1, 4].length) (baseStart_3619854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3619854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3619854 prefixEnd_3619854 := by exact prefixLift 3619854
  have htrace : WordTrace (prefixWord ++ tailWord_3619854) baseStart_3619854 baseEnd_3619854 := by
    simpa [prefixWord, tailWord_3619854, baseEnd_3619854] using wordTrace_append hprefix tailTrace_3619854
  have hstable : (prefixWord ++ tailWord_3619854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3619854).length < 2 ^ (prefixWord ++ tailWord_3619854).sum := by decide
  have hdescent : baseEnd_3619854 < baseStart_3619854 := by decide
  rcases family_descends (prefixWord ++ tailWord_3619854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3619863 : List Nat := [1, 1, 3, 5, 1, 1, 1, 2, 3, 5]
def baseStart_3619863 : Nat := 118140960795 + 3619863 * 2 ^ 59
def prefixEnd_3619863 : Nat := 4983230072969 + 3 ^ 40 * 3619863 * 2
def baseEnd_3619863 : Nat := 619576540808758667688353

theorem tailTrace_3619863 : CollatzResearch.WordTrace tailWord_3619863 prefixEnd_3619863 619576540808758667688353 := by
  unfold tailWord_3619863
  simp only [CollatzResearch.WordTrace]
  refine ⟨132027250084862049226232243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88018166723241366150821495 132027250084862049226232243)
  ·
    refine ⟨198040875127293073839348365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132027250084862049226232243 198040875127293073839348365)
    ·
      refine ⟨74265328172734902689755637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 198040875127293073839348365 74265328172734902689755637)
      ·
        refine ⟨6962374516193897127164591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 74265328172734902689755637 6962374516193897127164591)
        ·
          refine ⟨10443561774290845690746887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6962374516193897127164591 10443561774290845690746887)
          ·
            refine ⟨15665342661436268536120331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10443561774290845690746887 15665342661436268536120331)
            ·
              refine ⟨23498013992154402804180497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15665342661436268536120331 23498013992154402804180497)
              ·
                refine ⟨17623510494115802103135373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23498013992154402804180497 17623510494115802103135373)
                ·
                  refine ⟨6608816435293425788675765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17623510494115802103135373 6608816435293425788675765)
                  ·
                    refine ⟨619576540808758667688353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6608816435293425788675765 619576540808758667688353)
                    ·
                      rfl

theorem cell23_3619863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 1, 2, 3, 5].length) (baseStart_3619863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3619863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3619863 prefixEnd_3619863 := by exact prefixLift 3619863
  have htrace : WordTrace (prefixWord ++ tailWord_3619863) baseStart_3619863 baseEnd_3619863 := by
    simpa [prefixWord, tailWord_3619863, baseEnd_3619863] using wordTrace_append hprefix tailTrace_3619863
  have hstable : (prefixWord ++ tailWord_3619863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3619863).length < 2 ^ (prefixWord ++ tailWord_3619863).sum := by decide
  have hdescent : baseEnd_3619863 < baseStart_3619863 := by decide
  rcases family_descends (prefixWord ++ tailWord_3619863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3619883 : List Nat := [1, 1, 1, 1, 2, 1, 6, 4, 1, 1, 4]
def baseStart_3619883 : Nat := 118140960795 + 3619883 * 2 ^ 59
def prefixEnd_3619883 : Nat := 4983230072969 + 3 ^ 40 * 3619883 * 2
def baseEnd_3619883 : Nat := 1858739892039365924814967

theorem tailTrace_3619883 : CollatzResearch.WordTrace tailWord_3619883 prefixEnd_3619883 1858739892039365924814967 := by
  unfold tailWord_3619883
  simp only [CollatzResearch.WordTrace]
  refine ⟨132027979544789592641960303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88018653029859728427973535 132027979544789592641960303)
  ·
    refine ⟨198041969317184388962940455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132027979544789592641960303 198041969317184388962940455)
    ·
      refine ⟨297062953975776583444410683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198041969317184388962940455 297062953975776583444410683)
      ·
        refine ⟨445594430963664875166616025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 297062953975776583444410683 445594430963664875166616025)
        ·
          refine ⟨334195823222748656374962019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 445594430963664875166616025 334195823222748656374962019)
          ·
            refine ⟨501293734834122984562443029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 334195823222748656374962019 501293734834122984562443029)
            ·
              refine ⟨23498143820349514901364517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 501293734834122984562443029 23498143820349514901364517)
              ·
                refine ⟨4405901966315534044005847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23498143820349514901364517 4405901966315534044005847)
                ·
                  refine ⟨6608852949473301066008771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4405901966315534044005847 6608852949473301066008771)
                  ·
                    refine ⟨9913279424209951599013157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6608852949473301066008771 9913279424209951599013157)
                    ·
                      refine ⟨1858739892039365924814967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9913279424209951599013157 1858739892039365924814967)
                      ·
                        rfl

theorem cell23_3619883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 6, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 6, 4, 1, 1, 4].length) (baseStart_3619883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3619883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3619883 prefixEnd_3619883 := by exact prefixLift 3619883
  have htrace : WordTrace (prefixWord ++ tailWord_3619883) baseStart_3619883 baseEnd_3619883 := by
    simpa [prefixWord, tailWord_3619883, baseEnd_3619883] using wordTrace_append hprefix tailTrace_3619883
  have hstable : (prefixWord ++ tailWord_3619883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3619883).length < 2 ^ (prefixWord ++ tailWord_3619883).sum := by decide
  have hdescent : baseEnd_3619883 < baseStart_3619883 := by decide
  rcases family_descends (prefixWord ++ tailWord_3619883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3619893 : List Nat := [1, 3, 3, 1, 1, 1, 1, 4, 4, 4]
def baseStart_3619893 : Nat := 118140960795 + 3619893 * 2 ^ 59
def prefixEnd_3619893 : Nat := 4983230072969 + 3 ^ 40 * 3619893 * 2
def baseEnd_3619893 : Nat := 619581675615303628563307

theorem tailTrace_3619893 : CollatzResearch.WordTrace tailWord_3619893 prefixEnd_3619893 619581675615303628563307 := by
  unfold tailWord_3619893
  simp only [CollatzResearch.WordTrace]
  refine ⟨132028344274753364349824333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88018896183168909566549555 132028344274753364349824333)
  ·
    refine ⟨49510629103032511631184125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 132028344274753364349824333 49510629103032511631184125)
    ·
      refine ⟨18566485913637191861694047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49510629103032511631184125 18566485913637191861694047)
      ·
        refine ⟨27849728870455787792541071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18566485913637191861694047 27849728870455787792541071)
        ·
          refine ⟨41774593305683681688811607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27849728870455787792541071 41774593305683681688811607)
          ·
            refine ⟨62661889958525522533217411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41774593305683681688811607 62661889958525522533217411)
            ·
              refine ⟨93992834937788283799826117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62661889958525522533217411 93992834937788283799826117)
              ·
                refine ⟨17623656550835303212467397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 93992834937788283799826117 17623656550835303212467397)
                ·
                  refine ⟨3304435603281619352337637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17623656550835303212467397 3304435603281619352337637)
                  ·
                    refine ⟨619581675615303628563307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3304435603281619352337637 619581675615303628563307)
                    ·
                      rfl

theorem cell23_3619893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 4, 4, 4].length) (baseStart_3619893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3619893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3619893 prefixEnd_3619893 := by exact prefixLift 3619893
  have htrace : WordTrace (prefixWord ++ tailWord_3619893) baseStart_3619893 baseEnd_3619893 := by
    simpa [prefixWord, tailWord_3619893, baseEnd_3619893] using wordTrace_append hprefix tailTrace_3619893
  have hstable : (prefixWord ++ tailWord_3619893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3619893).length < 2 ^ (prefixWord ++ tailWord_3619893).sum := by decide
  have hdescent : baseEnd_3619893 < baseStart_3619893 := by decide
  rcases family_descends (prefixWord ++ tailWord_3619893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3619894 : List Nat := [5, 1, 2, 1, 1, 2, 1, 5, 1, 1, 3]
def baseStart_3619894 : Nat := 118140960795 + 3619894 * 2 ^ 59
def prefixEnd_3619894 : Nat := 4983230072969 + 3 ^ 40 * 3619894 * 2
def baseEnd_3619894 : Nat := 1858745540326565381777417

theorem tailTrace_3619894 : CollatzResearch.WordTrace tailWord_3619894 prefixEnd_3619894 1858745540326565381777417 := by
  unfold tailWord_3619894
  simp only [CollatzResearch.WordTrace]
  refine ⟨8251773796734358845038171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 88018920498499827680407157 8251773796734358845038171)
  ·
    refine ⟨12377660695101538267557257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8251773796734358845038171 12377660695101538267557257)
    ·
      refine ⟨9283245521326153700667943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12377660695101538267557257 9283245521326153700667943)
      ·
        refine ⟨13924868281989230551001915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9283245521326153700667943 13924868281989230551001915)
        ·
          refine ⟨20887302422983845826502873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13924868281989230551001915 20887302422983845826502873)
          ·
            refine ⟨15665476817237884369877155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20887302422983845826502873 15665476817237884369877155)
            ·
              refine ⟨23498215225856826554815733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15665476817237884369877155 23498215225856826554815733)
              ·
                refine ⟨2202957677424077489513975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 23498215225856826554815733 2202957677424077489513975)
                ·
                  refine ⟨3304436516136116234270963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2202957677424077489513975 3304436516136116234270963)
                  ·
                    refine ⟨4956654774204174351406445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3304436516136116234270963 4956654774204174351406445)
                    ·
                      refine ⟨1858745540326565381777417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4956654774204174351406445 1858745540326565381777417)
                      ·
                        rfl

theorem cell23_3619894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 1, 5, 1, 1, 3].length) (baseStart_3619894 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3619894 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3619894 prefixEnd_3619894 := by exact prefixLift 3619894
  have htrace : WordTrace (prefixWord ++ tailWord_3619894) baseStart_3619894 baseEnd_3619894 := by
    simpa [prefixWord, tailWord_3619894, baseEnd_3619894] using wordTrace_append hprefix tailTrace_3619894
  have hstable : (prefixWord ++ tailWord_3619894).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3619894).length < 2 ^ (prefixWord ++ tailWord_3619894).sum := by decide
  have hdescent : baseEnd_3619894 < baseStart_3619894 := by decide
  rcases family_descends (prefixWord ++ tailWord_3619894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3619897 : List Nat := [1, 2, 1, 5, 2, 3, 2, 1, 1, 5]
def baseStart_3619897 : Nat := 118140960795 + 3619897 * 2 ^ 59
def prefixEnd_3619897 : Nat := 4983230072969 + 3 ^ 40 * 3619897 * 2
def baseEnd_3619897 : Nat := 619582360256176290013301

theorem tailTrace_3619897 : CollatzResearch.WordTrace tailWord_3619897 prefixEnd_3619897 619582360256176290013301 := by
  unfold tailWord_3619897
  simp only [CollatzResearch.WordTrace]
  refine ⟨132028490166738873032969945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88018993444492582021979963 132028490166738873032969945)
  ·
    refine ⟨99021367625054154774727459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132028490166738873032969945 99021367625054154774727459)
    ·
      refine ⟨148532051437581232162091189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99021367625054154774727459 148532051437581232162091189)
      ·
        refine ⟨13924879822273240515196049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 148532051437581232162091189 13924879822273240515196049)
        ·
          refine ⟨10443659866704930386397037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13924879822273240515196049 10443659866704930386397037)
          ·
            refine ⟨3916372450014348894898889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10443659866704930386397037 3916372450014348894898889)
            ·
              refine ⟨2937279337510761671174167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3916372450014348894898889 2937279337510761671174167)
              ·
                refine ⟨4405919006266142506761251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2937279337510761671174167 4405919006266142506761251)
                ·
                  refine ⟨6608878509399213760141877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4405919006266142506761251 6608878509399213760141877)
                  ·
                    refine ⟨619582360256176290013301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6608878509399213760141877 619582360256176290013301)
                    ·
                      rfl

theorem cell23_3619897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 3, 2, 1, 1, 5].length) (baseStart_3619897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3619897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3619897 prefixEnd_3619897 := by exact prefixLift 3619897
  have htrace : WordTrace (prefixWord ++ tailWord_3619897) baseStart_3619897 baseEnd_3619897 := by
    simpa [prefixWord, tailWord_3619897, baseEnd_3619897] using wordTrace_append hprefix tailTrace_3619897
  have hstable : (prefixWord ++ tailWord_3619897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3619897).length < 2 ^ (prefixWord ++ tailWord_3619897).sum := by decide
  have hdescent : baseEnd_3619897 < baseStart_3619897 := by decide
  rcases family_descends (prefixWord ++ tailWord_3619897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3619900 : List Nat := [2, 2, 2, 2, 2, 3, 1, 3, 1, 1, 4]
def baseStart_3619900 : Nat := 118140960795 + 3619900 * 2 ^ 59
def prefixEnd_3619900 : Nat := 4983230072969 + 3 ^ 40 * 3619900 * 2
def baseEnd_3619900 : Nat := 1858748621210492358302389

theorem tailTrace_3619900 : CollatzResearch.WordTrace tailWord_3619900 prefixEnd_3619900 1858748621210492358302389 := by
  unfold tailWord_3619900
  simp only [CollatzResearch.WordTrace]
  refine ⟨66014299792864002272664577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88019066390485336363552769 66014299792864002272664577)
  ·
    refine ⟨49510724844648001704498433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66014299792864002272664577 49510724844648001704498433)
    ·
      refine ⟨37133043633486001278373825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49510724844648001704498433 37133043633486001278373825)
      ·
        refine ⟨27849782725114500958780369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37133043633486001278373825 27849782725114500958780369)
        ·
          refine ⟨20887337043835875719085277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27849782725114500958780369 20887337043835875719085277)
          ·
            refine ⟨7832751391438453394656979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20887337043835875719085277 7832751391438453394656979)
            ·
              refine ⟨11749127087157680091985469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7832751391438453394656979 11749127087157680091985469)
              ·
                refine ⟨4405922657684130034494551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11749127087157680091985469 4405922657684130034494551)
                ·
                  refine ⟨6608883986526195051741827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4405922657684130034494551 6608883986526195051741827)
                  ·
                    refine ⟨9913325979789292577612741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6608883986526195051741827 9913325979789292577612741)
                    ·
                      refine ⟨1858748621210492358302389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9913325979789292577612741 1858748621210492358302389)
                      ·
                        rfl

theorem cell23_3619900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 1, 3, 1, 1, 4].length) (baseStart_3619900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3619900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3619900 prefixEnd_3619900 := by exact prefixLift 3619900
  have htrace : WordTrace (prefixWord ++ tailWord_3619900) baseStart_3619900 baseEnd_3619900 := by
    simpa [prefixWord, tailWord_3619900, baseEnd_3619900] using wordTrace_append hprefix tailTrace_3619900
  have hstable : (prefixWord ++ tailWord_3619900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3619900).length < 2 ^ (prefixWord ++ tailWord_3619900).sum := by decide
  have hdescent : baseEnd_3619900 < baseStart_3619900 := by decide
  rcases family_descends (prefixWord ++ tailWord_3619900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3619916 : List Nat := [2, 2, 1, 3, 1, 1, 1, 1, 2, 2, 7]
def baseStart_3619916 : Nat := 118140960795 + 3619916 * 2 ^ 59
def prefixEnd_3619916 : Nat := 4983230072969 + 3 ^ 40 * 3619916 * 2
def baseEnd_3619916 : Nat := 1858756836900964295702315

theorem tailTrace_3619916 : CollatzResearch.WordTrace tailWord_3619916 prefixEnd_3619916 1858756836900964295702315 := by
  unfold tailWord_3619916
  simp only [CollatzResearch.WordTrace]
  refine ⟨66014591576835019638955801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88019455435780026185274401 66014591576835019638955801)
  ·
    refine ⟨49510943682626264729216851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66014591576835019638955801 49510943682626264729216851)
    ·
      refine ⟨74266415523939397093825277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49510943682626264729216851 74266415523939397093825277)
      ·
        refine ⟨27849905821477273910184479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74266415523939397093825277 27849905821477273910184479)
        ·
          refine ⟨41774858732215910865276719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27849905821477273910184479 41774858732215910865276719)
          ·
            refine ⟨62662288098323866297915079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41774858732215910865276719 62662288098323866297915079)
            ·
              refine ⟨93993432147485799446872619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62662288098323866297915079 93993432147485799446872619)
              ·
                refine ⟨140990148221228699170308929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 93993432147485799446872619 140990148221228699170308929)
                ·
                  refine ⟨105742611165921524377731697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 140990148221228699170308929 105742611165921524377731697)
                  ·
                    refine ⟨79306958374441143283298773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 105742611165921524377731697 79306958374441143283298773)
                    ·
                      refine ⟨1858756836900964295702315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 79306958374441143283298773 1858756836900964295702315)
                      ·
                        rfl

theorem cell23_3619916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 1, 2, 2, 7].length) (baseStart_3619916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3619916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3619916 prefixEnd_3619916 := by exact prefixLift 3619916
  have htrace : WordTrace (prefixWord ++ tailWord_3619916) baseStart_3619916 baseEnd_3619916 := by
    simpa [prefixWord, tailWord_3619916, baseEnd_3619916] using wordTrace_append hprefix tailTrace_3619916
  have hstable : (prefixWord ++ tailWord_3619916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3619916).length < 2 ^ (prefixWord ++ tailWord_3619916).sum := by decide
  have hdescent : baseEnd_3619916 < baseStart_3619916 := by decide
  rcases family_descends (prefixWord ++ tailWord_3619916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3619934 : List Nat := [4, 4, 1, 1, 1, 1, 1, 4, 1, 1, 4]
def baseStart_3619934 : Nat := 118140960795 + 3619934 * 2 ^ 59
def prefixEnd_3619934 : Nat := 4983230072969 + 3 ^ 40 * 3619934 * 2
def baseEnd_3619934 : Nat := 1858766079552745225277233

theorem tailTrace_3619934 : CollatzResearch.WordTrace tailWord_3619934 prefixEnd_3619934 1858766079552745225277233 := by
  unfold tailWord_3619934
  simp only [CollatzResearch.WordTrace]
  refine ⟨16503729958450603544008357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 88019893111736552234711237 16503729958450603544008357)
  ·
    refine ⟨3094449367209488164501567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16503729958450603544008357 3094449367209488164501567)
    ·
      refine ⟨4641674050814232246752351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3094449367209488164501567 4641674050814232246752351)
      ·
        refine ⟨6962511076221348370128527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4641674050814232246752351 6962511076221348370128527)
        ·
          refine ⟨10443766614332022555192791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6962511076221348370128527 10443766614332022555192791)
          ·
            refine ⟨15665649921498033832789187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10443766614332022555192791 15665649921498033832789187)
            ·
              refine ⟨23498474882247050749183781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15665649921498033832789187 23498474882247050749183781)
              ·
                refine ⟨4405964040421322015471959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23498474882247050749183781 4405964040421322015471959)
                ·
                  refine ⟨6608946060631983023207939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4405964040421322015471959 6608946060631983023207939)
                  ·
                    refine ⟨9913419090947974534811909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6608946060631983023207939 9913419090947974534811909)
                    ·
                      refine ⟨1858766079552745225277233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9913419090947974534811909 1858766079552745225277233)
                      ·
                        rfl

theorem cell23_3619934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 1, 4, 1, 1, 4].length) (baseStart_3619934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3619934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3619934 prefixEnd_3619934 := by exact prefixLift 3619934
  have htrace : WordTrace (prefixWord ++ tailWord_3619934) baseStart_3619934 baseEnd_3619934 := by
    simpa [prefixWord, tailWord_3619934, baseEnd_3619934] using wordTrace_append hprefix tailTrace_3619934
  have hstable : (prefixWord ++ tailWord_3619934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3619934).length < 2 ^ (prefixWord ++ tailWord_3619934).sum := by decide
  have hdescent : baseEnd_3619934 < baseStart_3619934 := by decide
  rcases family_descends (prefixWord ++ tailWord_3619934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3619957 : List Nat := [1, 3, 4, 3, 2, 1, 9]
def baseStart_3619957 : Nat := 118140960795 + 3619957 * 2 ^ 59
def prefixEnd_3619957 : Nat := 4983230072969 + 3 ^ 40 * 3619957 * 2
def baseEnd_3619957 : Nat := 22947875180343193028267

theorem tailTrace_3619957 : CollatzResearch.WordTrace tailWord_3619957 prefixEnd_3619957 22947875180343193028267 := by
  unfold tailWord_3619957
  simp only [CollatzResearch.WordTrace]
  refine ⟨132030678546521503280154125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88020452364347668853436083 132030678546521503280154125)
  ·
    refine ⟨49511504454945563730057797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 132030678546521503280154125 49511504454945563730057797)
    ·
      refine ⟨9283407085302293199385837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 49511504454945563730057797 9283407085302293199385837)
      ·
        refine ⟨3481277656988359949769689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9283407085302293199385837 3481277656988359949769689)
        ·
          refine ⟨2610958242741269962327267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3481277656988359949769689 2610958242741269962327267)
          ·
            refine ⟨3916437364111904943490901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2610958242741269962327267 3916437364111904943490901)
            ·
              refine ⟨22947875180343193028267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3916437364111904943490901 22947875180343193028267)
              ·
                rfl

theorem cell23_3619957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 2, 1, 9].length) (baseStart_3619957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3619957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3619957 prefixEnd_3619957 := by exact prefixLift 3619957
  have htrace : WordTrace (prefixWord ++ tailWord_3619957) baseStart_3619957 baseEnd_3619957 := by
    simpa [prefixWord, tailWord_3619957, baseEnd_3619957] using wordTrace_append hprefix tailTrace_3619957
  have hstable : (prefixWord ++ tailWord_3619957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3619957).length < 2 ^ (prefixWord ++ tailWord_3619957).sum := by decide
  have hdescent : baseEnd_3619957 < baseStart_3619957 := by decide
  rcases family_descends (prefixWord ++ tailWord_3619957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3619994 : List Nat := [3, 1, 1, 5, 1, 1, 3, 2, 1, 3, 2]
def baseStart_3619994 : Nat := 118140960795 + 3619994 * 2 ^ 59
def prefixEnd_3619994 : Nat := 4983230072969 + 3 ^ 40 * 3619994 * 2
def baseEnd_3619994 : Nat := 1858796888392014990526957

theorem tailTrace_3619994 : CollatzResearch.WordTrace tailWord_3619994 prefixEnd_3619994 1858796888392014990526957 := by
  unfold tailWord_3619994
  simp only [CollatzResearch.WordTrace]
  refine ⟨33008007011846864649812759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88021352031591639066167357 33008007011846864649812759)
  ·
    refine ⟨49512010517770296974719139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33008007011846864649812759 49512010517770296974719139)
    ·
      refine ⟨74268015776655445462078709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49512010517770296974719139 74268015776655445462078709)
      ·
        refine ⟨6962626479061448012069879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 74268015776655445462078709 6962626479061448012069879)
        ·
          refine ⟨10443939718592172018104819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6962626479061448012069879 10443939718592172018104819)
          ·
            refine ⟨15665909577888258027157229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10443939718592172018104819 15665909577888258027157229)
            ·
              refine ⟨5874716091708096760183961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15665909577888258027157229 5874716091708096760183961)
              ·
                refine ⟨4406037068781072570137971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5874716091708096760183961 4406037068781072570137971)
                ·
                  refine ⟨6609055603171608855206957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4406037068781072570137971 6609055603171608855206957)
                  ·
                    refine ⟨2478395851189353320702609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6609055603171608855206957 2478395851189353320702609)
                    ·
                      refine ⟨1858796888392014990526957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2478395851189353320702609 1858796888392014990526957)
                      ·
                        rfl

theorem cell23_3619994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 3, 2, 1, 3, 2].length) (baseStart_3619994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3619994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3619994 prefixEnd_3619994 := by exact prefixLift 3619994
  have htrace : WordTrace (prefixWord ++ tailWord_3619994) baseStart_3619994 baseEnd_3619994 := by
    simpa [prefixWord, tailWord_3619994, baseEnd_3619994] using wordTrace_append hprefix tailTrace_3619994
  have hstable : (prefixWord ++ tailWord_3619994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3619994).length < 2 ^ (prefixWord ++ tailWord_3619994).sum := by decide
  have hdescent : baseEnd_3619994 < baseStart_3619994 := by decide
  rcases family_descends (prefixWord ++ tailWord_3619994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3620007 : List Nat := [1, 1, 6, 2, 1, 1, 1, 1, 3, 4, 2]
def baseStart_3620007 : Nat := 118140960795 + 3620007 * 2 ^ 59
def prefixEnd_3620007 : Nat := 4983230072969 + 3 ^ 40 * 3620007 * 2
def baseEnd_3620007 : Nat := 1858803563640523439664397

theorem tailTrace_3620007 : CollatzResearch.WordTrace tailWord_3620007 prefixEnd_3620007 1858803563640523439664397 := by
  unfold tailWord_3620007
  simp only [CollatzResearch.WordTrace]
  refine ⟨132032502196340361819474275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88021668130893574546316183 132032502196340361819474275)
  ·
    refine ⟨198048753294510542729211413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132032502196340361819474275 198048753294510542729211413)
    ·
      refine ⟨9283535310680181690431785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 198048753294510542729211413 9283535310680181690431785)
      ·
        refine ⟨6962651483010136267823839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9283535310680181690431785 6962651483010136267823839)
        ·
          refine ⟨10443977224515204401735759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6962651483010136267823839 10443977224515204401735759)
          ·
            refine ⟨15665965836772806602603639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10443977224515204401735759 15665965836772806602603639)
            ·
              refine ⟨23498948755159209903905459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15665965836772806602603639 23498948755159209903905459)
              ·
                refine ⟨35248423132738814855858189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23498948755159209903905459 35248423132738814855858189)
                ·
                  refine ⟨13218158674777055570946821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35248423132738814855858189 13218158674777055570946821)
                  ·
                    refine ⟨2478404751520697919552529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13218158674777055570946821 2478404751520697919552529)
                    ·
                      refine ⟨1858803563640523439664397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2478404751520697919552529 1858803563640523439664397)
                      ·
                        rfl

theorem cell23_3620007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 1, 1, 3, 4, 2].length) (baseStart_3620007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3620007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3620007 prefixEnd_3620007 := by exact prefixLift 3620007
  have htrace : WordTrace (prefixWord ++ tailWord_3620007) baseStart_3620007 baseEnd_3620007 := by
    simpa [prefixWord, tailWord_3620007, baseEnd_3620007] using wordTrace_append hprefix tailTrace_3620007
  have hstable : (prefixWord ++ tailWord_3620007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3620007).length < 2 ^ (prefixWord ++ tailWord_3620007).sum := by decide
  have hdescent : baseEnd_3620007 < baseStart_3620007 := by decide
  rcases family_descends (prefixWord ++ tailWord_3620007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3620034 : List Nat := [3, 5, 1, 1, 2, 1, 1, 1, 2, 6]
def baseStart_3620034 : Nat := 118140960795 + 3620034 * 2 ^ 59
def prefixEnd_3620034 : Nat := 4983230072969 + 3 ^ 40 * 3620034 * 2
def baseEnd_3620034 : Nat := 619605809206064944675591

theorem tailTrace_3620034 : CollatzResearch.WordTrace tailWord_3620034 prefixEnd_3620034 619605809206064944675591 := by
  unfold tailWord_3620034
  simp only [CollatzResearch.WordTrace]
  refine ⟨33008371741810636357676789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88022324644828363620471437 33008371741810636357676789)
  ·
    refine ⟨3094534850794747158532199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 33008371741810636357676789 3094534850794747158532199)
    ·
      refine ⟨4641802276192120737798299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3094534850794747158532199 4641802276192120737798299)
      ·
        refine ⟨6962703414288181106697449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4641802276192120737798299 6962703414288181106697449)
        ·
          refine ⟨5222027560716135830023087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6962703414288181106697449 5222027560716135830023087)
          ·
            refine ⟨7833041341074203745034631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5222027560716135830023087 7833041341074203745034631)
            ·
              refine ⟨11749562011611305617551947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7833041341074203745034631 11749562011611305617551947)
              ·
                refine ⟨17624343017416958426327921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11749562011611305617551947 17624343017416958426327921)
                ·
                  refine ⟨13218257263062718819745941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17624343017416958426327921 13218257263062718819745941)
                  ·
                    refine ⟨619605809206064944675591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13218257263062718819745941 619605809206064944675591)
                    ·
                      rfl

theorem cell23_3620034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 1, 1, 2, 6].length) (baseStart_3620034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3620034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3620034 prefixEnd_3620034 := by exact prefixLift 3620034
  have htrace : WordTrace (prefixWord ++ tailWord_3620034) baseStart_3620034 baseEnd_3620034 := by
    simpa [prefixWord, tailWord_3620034, baseEnd_3620034] using wordTrace_append hprefix tailTrace_3620034
  have hstable : (prefixWord ++ tailWord_3620034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3620034).length < 2 ^ (prefixWord ++ tailWord_3620034).sum := by decide
  have hdescent : baseEnd_3620034 < baseStart_3620034 := by decide
  rcases family_descends (prefixWord ++ tailWord_3620034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3620097 : List Nat := [1, 2, 4, 1, 1, 3, 2, 1, 2, 4, 2]
def baseStart_3620097 : Nat := 118140960795 + 3620097 * 2 ^ 59
def prefixEnd_3620097 : Nat := 4983230072969 + 3 ^ 40 * 3620097 * 2
def baseEnd_3620097 : Nat := 1858849776899428087538983

theorem tailTrace_3620097 : CollatzResearch.WordTrace tailWord_3620097 prefixEnd_3620097 1858849776899428087538983 := by
  unfold tailWord_3620097
  simp only [CollatzResearch.WordTrace]
  refine ⟨132035784766014307190250545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88023856510676204793500363 132035784766014307190250545)
  ·
    refine ⟨99026838574510730392687909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132035784766014307190250545 99026838574510730392687909)
    ·
      refine ⟨18567532232720761948628983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 99026838574510730392687909 18567532232720761948628983)
      ·
        refine ⟨27851298349081142922943475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18567532232720761948628983 27851298349081142922943475)
        ·
          refine ⟨41776947523621714384415213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27851298349081142922943475 41776947523621714384415213)
          ·
            refine ⟨15666355321358142894155705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41776947523621714384415213 15666355321358142894155705)
            ·
              refine ⟨11749766491018607170616779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15666355321358142894155705 11749766491018607170616779)
              ·
                refine ⟨17624649736527910755925169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11749766491018607170616779 17624649736527910755925169)
                ·
                  refine ⟨13218487302395933066943877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17624649736527910755925169 13218487302395933066943877)
                  ·
                    refine ⟨2478466369199237450051977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13218487302395933066943877 2478466369199237450051977)
                    ·
                      refine ⟨1858849776899428087538983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2478466369199237450051977 1858849776899428087538983)
                      ·
                        rfl

theorem cell23_3620097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 2, 1, 2, 4, 2].length) (baseStart_3620097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3620097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3620097 prefixEnd_3620097 := by exact prefixLift 3620097
  have htrace : WordTrace (prefixWord ++ tailWord_3620097) baseStart_3620097 baseEnd_3620097 := by
    simpa [prefixWord, tailWord_3620097, baseEnd_3620097] using wordTrace_append hprefix tailTrace_3620097
  have hstable : (prefixWord ++ tailWord_3620097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3620097).length < 2 ^ (prefixWord ++ tailWord_3620097).sum := by decide
  have hdescent : baseEnd_3620097 < baseStart_3620097 := by decide
  rcases family_descends (prefixWord ++ tailWord_3620097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3620124 : List Nat := [2, 2, 3, 1, 1, 1, 5, 3, 1, 4]
def baseStart_3620124 : Nat := 118140960795 + 3620124 * 2 ^ 59
def prefixEnd_3620124 : Nat := 4983230072969 + 3 ^ 40 * 3620124 * 2
def baseEnd_3620124 : Nat := 619621213625699827300453

theorem tailTrace_3620124 : CollatzResearch.WordTrace tailWord_3620124 prefixEnd_3620124 619621213625699827300453 := by
  unfold tailWord_3620124
  simp only [CollatzResearch.WordTrace]
  refine ⟨66018384768458245400741713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88024513024610993867655617 66018384768458245400741713)
  ·
    refine ⟨49513788576343684050556285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66018384768458245400741713 49513788576343684050556285)
    ·
      refine ⟨18567670716128881518958607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49513788576343684050556285 18567670716128881518958607)
      ·
        refine ⟨27851506074193322278437911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18567670716128881518958607 27851506074193322278437911)
        ·
          refine ⟨41777259111289983417656867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27851506074193322278437911 41777259111289983417656867)
          ·
            refine ⟨62665888666934975126485301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41777259111289983417656867 62665888666934975126485301)
            ·
              refine ⟨5874927062525153918107997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 62665888666934975126485301 5874927062525153918107997)
              ·
                refine ⟨2203097648446932719290499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5874927062525153918107997 2203097648446932719290499)
                ·
                  refine ⟨3304646472670399078935749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2203097648446932719290499 3304646472670399078935749)
                  ·
                    refine ⟨619621213625699827300453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3304646472670399078935749 619621213625699827300453)
                    ·
                      rfl

theorem cell23_3620124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 5, 3, 1, 4].length) (baseStart_3620124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3620124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3620124 prefixEnd_3620124 := by exact prefixLift 3620124
  have htrace : WordTrace (prefixWord ++ tailWord_3620124) baseStart_3620124 baseEnd_3620124 := by
    simpa [prefixWord, tailWord_3620124, baseEnd_3620124] using wordTrace_append hprefix tailTrace_3620124
  have hstable : (prefixWord ++ tailWord_3620124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3620124).length < 2 ^ (prefixWord ++ tailWord_3620124).sum := by decide
  have hdescent : baseEnd_3620124 < baseStart_3620124 := by decide
  rcases family_descends (prefixWord ++ tailWord_3620124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3620141 : List Nat := [1, 5, 3, 1, 1, 3, 1, 1, 3, 4]
def baseStart_3620141 : Nat := 118140960795 + 3620141 * 2 ^ 59
def prefixEnd_3620141 : Nat := 4983230072969 + 3 ^ 40 * 3620141 * 2
def baseEnd_3620141 : Nat := 619624123349408638462927

theorem tailTrace_3620141 : CollatzResearch.WordTrace tailWord_3620141 prefixEnd_3620141 619624123349408638462927 := by
  unfold tailWord_3620141
  simp only [CollatzResearch.WordTrace]
  refine ⟨132037389577854902704852277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88024926385236601803234851 132037389577854902704852277)
  ·
    refine ⟨12378505272923897128579901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 132037389577854902704852277 12378505272923897128579901)
    ·
      refine ⟨4641939477346461423217463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12378505272923897128579901 4641939477346461423217463)
      ·
        refine ⟨6962909216019692134826195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4641939477346461423217463 6962909216019692134826195)
        ·
          refine ⟨10444363824029538202239293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6962909216019692134826195 10444363824029538202239293)
          ·
            refine ⟨3916636434011076825839735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10444363824029538202239293 3916636434011076825839735)
            ·
              refine ⟨5874954651016615238759603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3916636434011076825839735 5874954651016615238759603)
              ·
                refine ⟨8812431976524922858139405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5874954651016615238759603 8812431976524922858139405)
                ·
                  refine ⟨3304661991196846071802277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8812431976524922858139405 3304661991196846071802277)
                  ·
                    refine ⟨619624123349408638462927, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3304661991196846071802277 619624123349408638462927)
                    ·
                      rfl

theorem cell23_3620141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 3, 1, 1, 3, 4].length) (baseStart_3620141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3620141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3620141 prefixEnd_3620141 := by exact prefixLift 3620141
  have htrace : WordTrace (prefixWord ++ tailWord_3620141) baseStart_3620141 baseEnd_3620141 := by
    simpa [prefixWord, tailWord_3620141, baseEnd_3620141] using wordTrace_append hprefix tailTrace_3620141
  have hstable : (prefixWord ++ tailWord_3620141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3620141).length < 2 ^ (prefixWord ++ tailWord_3620141).sum := by decide
  have hdescent : baseEnd_3620141 < baseStart_3620141 := by decide
  rcases family_descends (prefixWord ++ tailWord_3620141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3620143 : List Nat := [1, 1, 2, 1, 2, 1, 3, 2, 2, 1, 7]
def baseStart_3620143 : Nat := 118140960795 + 3620143 * 2 ^ 59
def prefixEnd_3620143 : Nat := 4983230072969 + 3 ^ 40 * 3620143 * 2
def baseEnd_3620143 : Nat := 1858873397009534907563771

theorem tailTrace_3620143 : CollatzResearch.WordTrace tailWord_3620143 prefixEnd_3620143 1858873397009534907563771 := by
  unfold tailWord_3620143
  simp only [CollatzResearch.WordTrace]
  refine ⟨132037462523847657046425083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88024975015898438030950055 132037462523847657046425083)
  ·
    refine ⟨198056193785771485569637625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132037462523847657046425083 198056193785771485569637625)
    ·
      refine ⟨148542145339328614177228219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 198056193785771485569637625 148542145339328614177228219)
      ·
        refine ⟨222813218008992921265842329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148542145339328614177228219 222813218008992921265842329)
        ·
          refine ⟨167109913506744690949381747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 222813218008992921265842329 167109913506744690949381747)
          ·
            refine ⟨250664870260117036424072621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 167109913506744690949381747 250664870260117036424072621)
            ·
              refine ⟨93999326347543888659027233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 250664870260117036424072621 93999326347543888659027233)
              ·
                refine ⟨70499494760657916494270425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 93999326347543888659027233 70499494760657916494270425)
                ·
                  refine ⟨52874621070493437370702819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 70499494760657916494270425 52874621070493437370702819)
                  ·
                    refine ⟨79311931605740156056054229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 52874621070493437370702819 79311931605740156056054229)
                    ·
                      refine ⟨1858873397009534907563771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 79311931605740156056054229 1858873397009534907563771)
                      ·
                        rfl

theorem cell23_3620143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 2, 2, 1, 7].length) (baseStart_3620143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3620143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3620143 prefixEnd_3620143 := by exact prefixLift 3620143
  have htrace : WordTrace (prefixWord ++ tailWord_3620143) baseStart_3620143 baseEnd_3620143 := by
    simpa [prefixWord, tailWord_3620143, baseEnd_3620143] using wordTrace_append hprefix tailTrace_3620143
  have hstable : (prefixWord ++ tailWord_3620143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3620143).length < 2 ^ (prefixWord ++ tailWord_3620143).sum := by decide
  have hdescent : baseEnd_3620143 < baseStart_3620143 := by decide
  rcases family_descends (prefixWord ++ tailWord_3620143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3620167 : List Nat := [1, 1, 4, 1, 2, 3, 3, 2, 1, 5]
def baseStart_3620167 : Nat := 118140960795 + 3620167 * 2 ^ 59
def prefixEnd_3620167 : Nat := 4983230072969 + 3 ^ 40 * 3620167 * 2
def baseEnd_3620167 : Nat := 619628573515080937887887

theorem tailTrace_3620167 : CollatzResearch.WordTrace tailWord_3620167 prefixEnd_3620167 619628573515080937887887 := by
  unfold tailWord_3620167
  simp only [CollatzResearch.WordTrace]
  refine ⟨132038337875760709145298755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88025558583840472763532503 132038337875760709145298755)
  ·
    refine ⟨198057506813641063717948133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132038337875760709145298755 198057506813641063717948133)
    ·
      refine ⟨37135782527557699447115275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 198057506813641063717948133 37135782527557699447115275)
      ·
        refine ⟨55703673791336549170672913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37135782527557699447115275 55703673791336549170672913)
        ·
          refine ⟨41777755343502411878004685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55703673791336549170672913 41777755343502411878004685)
          ·
            refine ⟨15666658253813404454251757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41777755343502411878004685 15666658253813404454251757)
            ·
              refine ⟨5874996845180026670344409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15666658253813404454251757 5874996845180026670344409)
              ·
                refine ⟨4406247633885020002758307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5874996845180026670344409 4406247633885020002758307)
                ·
                  refine ⟨6609371450827530004137461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4406247633885020002758307 6609371450827530004137461)
                  ·
                    refine ⟨619628573515080937887887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6609371450827530004137461 619628573515080937887887)
                    ·
                      rfl

theorem cell23_3620167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 3, 2, 1, 5].length) (baseStart_3620167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3620167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3620167 prefixEnd_3620167 := by exact prefixLift 3620167
  have htrace : WordTrace (prefixWord ++ tailWord_3620167) baseStart_3620167 baseEnd_3620167 := by
    simpa [prefixWord, tailWord_3620167, baseEnd_3620167] using wordTrace_append hprefix tailTrace_3620167
  have hstable : (prefixWord ++ tailWord_3620167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3620167).length < 2 ^ (prefixWord ++ tailWord_3620167).sum := by decide
  have hdescent : baseEnd_3620167 < baseStart_3620167 := by decide
  rcases family_descends (prefixWord ++ tailWord_3620167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3620174 : List Nat := [4, 1, 1, 1, 1, 1, 6, 1, 2, 3, 2]
def baseStart_3620174 : Nat := 118140960795 + 3620174 * 2 ^ 59
def prefixEnd_3620174 : Nat := 4983230072969 + 3 ^ 40 * 3620174 * 2
def baseEnd_3620174 : Nat := 1858889314909824286276129

theorem tailTrace_3620174 : CollatzResearch.WordTrace tailWord_3620174 prefixEnd_3620174 1858889314909824286276129 := by
  unfold tailWord_3620174
  simp only [CollatzResearch.WordTrace]
  refine ⟨16504824148341918667600447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 88025728791156899560535717 16504824148341918667600447)
  ·
    refine ⟨24757236222512878001400671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16504824148341918667600447 24757236222512878001400671)
    ·
      refine ⟨37135854333769317002101007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24757236222512878001400671 37135854333769317002101007)
      ·
        refine ⟨55703781500653975503151511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37135854333769317002101007 55703781500653975503151511)
        ·
          refine ⟨83555672250980963254727267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55703781500653975503151511 83555672250980963254727267)
          ·
            refine ⟨125333508376471444882090901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83555672250980963254727267 125333508376471444882090901)
            ·
              refine ⟨5875008205147098978848011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 125333508376471444882090901 5875008205147098978848011)
              ·
                refine ⟨8812512307720648468272017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5875008205147098978848011 8812512307720648468272017)
                ·
                  refine ⟨6609384230790486351204013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8812512307720648468272017 6609384230790486351204013)
                  ·
                    refine ⟨2478519086546432381701505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6609384230790486351204013 2478519086546432381701505)
                    ·
                      refine ⟨1858889314909824286276129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2478519086546432381701505 1858889314909824286276129)
                      ·
                        rfl

theorem cell23_3620174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 6, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 6, 1, 2, 3, 2].length) (baseStart_3620174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3620174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3620174 prefixEnd_3620174 := by exact prefixLift 3620174
  have htrace : WordTrace (prefixWord ++ tailWord_3620174) baseStart_3620174 baseEnd_3620174 := by
    simpa [prefixWord, tailWord_3620174, baseEnd_3620174] using wordTrace_append hprefix tailTrace_3620174
  have hstable : (prefixWord ++ tailWord_3620174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3620174).length < 2 ^ (prefixWord ++ tailWord_3620174).sum := by decide
  have hdescent : baseEnd_3620174 < baseStart_3620174 := by decide
  rcases family_descends (prefixWord ++ tailWord_3620174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3620227 : List Nat := [1, 1, 1, 3, 5, 2, 3, 7]
def baseStart_3620227 : Nat := 118140960795 + 3620227 * 2 ^ 59
def prefixEnd_3620227 : Nat := 4983230072969 + 3 ^ 40 * 3620227 * 2
def baseEnd_3620227 : Nat := 68848760347574539959755

theorem tailTrace_3620227 : CollatzResearch.WordTrace tailWord_3620227 prefixEnd_3620227 68848760347574539959755 := by
  unfold tailWord_3620227
  simp only [CollatzResearch.WordTrace]
  refine ⟨132040526255543339392482935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88027017503695559594988623 132040526255543339392482935)
  ·
    refine ⟨198060789383315009088724403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132040526255543339392482935 198060789383315009088724403)
    ·
      refine ⟨297091184074972513633086605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198060789383315009088724403 297091184074972513633086605)
      ·
        refine ⟨111409194028114692612407477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 297091184074972513633086605 111409194028114692612407477)
        ·
          refine ⟨10444611940135752432413201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 111409194028114692612407477 10444611940135752432413201)
          ·
            refine ⟨7833458955101814324309901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10444611940135752432413201 7833458955101814324309901)
            ·
              refine ⟨2937547108163180371616213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7833458955101814324309901 2937547108163180371616213)
              ·
                refine ⟨68848760347574539959755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2937547108163180371616213 68848760347574539959755)
                ·
                  rfl

theorem cell23_3620227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 3, 7].length) (baseStart_3620227 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3620227 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3620227 prefixEnd_3620227 := by exact prefixLift 3620227
  have htrace : WordTrace (prefixWord ++ tailWord_3620227) baseStart_3620227 baseEnd_3620227 := by
    simpa [prefixWord, tailWord_3620227, baseEnd_3620227] using wordTrace_append hprefix tailTrace_3620227
  have hstable : (prefixWord ++ tailWord_3620227).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3620227).length < 2 ^ (prefixWord ++ tailWord_3620227).sum := by decide
  have hdescent : baseEnd_3620227 < baseStart_3620227 := by decide
  rcases family_descends (prefixWord ++ tailWord_3620227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3620238 : List Nat := [4, 1, 1, 4, 2, 2, 2, 1, 1, 1, 4]
def baseStart_3620238 : Nat := 118140960795 + 3620238 * 2 ^ 59
def prefixEnd_3620238 : Nat := 4983230072969 + 3 ^ 40 * 3620238 * 2
def baseEnd_3620238 : Nat := 1858922177671712035875835

theorem tailTrace_3620238 : CollatzResearch.WordTrace tailWord_3620238 prefixEnd_3620238 1858922177671712035875835 := by
  unfold tailWord_3620238
  simp only [CollatzResearch.WordTrace]
  refine ⟨16505115932312936033891671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 88027284972335658847422245 16505115932312936033891671)
  ·
    refine ⟨24757673898469404050837507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16505115932312936033891671 24757673898469404050837507)
    ·
      refine ⟨37136510847704106076256261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24757673898469404050837507 37136510847704106076256261)
      ·
        refine ⟨6963095783944519889298049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37136510847704106076256261 6963095783944519889298049)
        ·
          refine ⟨5222321837958389916973537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6963095783944519889298049 5222321837958389916973537)
          ·
            refine ⟨3916741378468792437730153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5222321837958389916973537 3916741378468792437730153)
            ·
              refine ⟨2937556033851594328297615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3916741378468792437730153 2937556033851594328297615)
              ·
                refine ⟨4406334050777391492446423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2937556033851594328297615 4406334050777391492446423)
                ·
                  refine ⟨6609501076166087238669635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4406334050777391492446423 6609501076166087238669635)
                  ·
                    refine ⟨9914251614249130858004453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6609501076166087238669635 9914251614249130858004453)
                    ·
                      refine ⟨1858922177671712035875835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9914251614249130858004453 1858922177671712035875835)
                      ·
                        rfl

theorem cell23_3620238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 2, 2, 1, 1, 1, 4].length) (baseStart_3620238 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3620238 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3620238 prefixEnd_3620238 := by exact prefixLift 3620238
  have htrace : WordTrace (prefixWord ++ tailWord_3620238) baseStart_3620238 baseEnd_3620238 := by
    simpa [prefixWord, tailWord_3620238, baseEnd_3620238] using wordTrace_append hprefix tailTrace_3620238
  have hstable : (prefixWord ++ tailWord_3620238).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3620238).length < 2 ^ (prefixWord ++ tailWord_3620238).sum := by decide
  have hdescent : baseEnd_3620238 < baseStart_3620238 := by decide
  rcases family_descends (prefixWord ++ tailWord_3620238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3620248 : List Nat := [2, 1, 2, 5, 3, 1, 1, 2, 2, 4]
def baseStart_3620248 : Nat := 118140960795 + 3620248 * 2 ^ 59
def prefixEnd_3620248 : Nat := 4983230072969 + 3 ^ 40 * 3620248 * 2
def baseEnd_3620248 : Nat := 619642437492752332250263

theorem tailTrace_3620248 : CollatzResearch.WordTrace tailWord_3620248 prefixEnd_3620248 619642437492752332250263 := by
  unfold tailWord_3620248
  simp only [CollatzResearch.WordTrace]
  refine ⟨66020646094233629989498699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88027528125644839985998265 66020646094233629989498699)
  ·
    refine ⟨99030969141350444984248049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66020646094233629989498699 99030969141350444984248049)
    ·
      refine ⟨74273226856012833738186037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99030969141350444984248049 74273226856012833738186037)
      ·
        refine ⟨6963115017751203162954941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 74273226856012833738186037 6963115017751203162954941)
        ·
          refine ⟨2611168131656701186108103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6963115017751203162954941 2611168131656701186108103)
          ·
            refine ⟨3916752197485051779162155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2611168131656701186108103 3916752197485051779162155)
            ·
              refine ⟨5875128296227577668743233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3916752197485051779162155 5875128296227577668743233)
              ·
                refine ⟨4406346222170683251557425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5875128296227577668743233 4406346222170683251557425)
                ·
                  refine ⟨3304759666628012438668069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4406346222170683251557425 3304759666628012438668069)
                  ·
                    refine ⟨619642437492752332250263, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3304759666628012438668069 619642437492752332250263)
                    ·
                      rfl

theorem cell23_3620248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 3, 1, 1, 2, 2, 4].length) (baseStart_3620248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3620248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3620248 prefixEnd_3620248 := by exact prefixLift 3620248
  have htrace : WordTrace (prefixWord ++ tailWord_3620248) baseStart_3620248 baseEnd_3620248 := by
    simpa [prefixWord, tailWord_3620248, baseEnd_3620248] using wordTrace_append hprefix tailTrace_3620248
  have hstable : (prefixWord ++ tailWord_3620248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3620248).length < 2 ^ (prefixWord ++ tailWord_3620248).sum := by decide
  have hdescent : baseEnd_3620248 < baseStart_3620248 := by decide
  rcases family_descends (prefixWord ++ tailWord_3620248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3620320 : List Nat := [2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 8]
def baseStart_3620320 : Nat := 118140960795 + 3620320 * 2 ^ 59
def prefixEnd_3620320 : Nat := 4983230072969 + 3 ^ 40 * 3620320 * 2
def baseEnd_3620320 : Nat := 1858964283085380715050457

theorem tailTrace_3620320 : CollatzResearch.WordTrace tailWord_3620320 prefixEnd_3620320 1858964283085380715050457 := by
  unfold tailWord_3620320
  simp only [CollatzResearch.WordTrace]
  refine ⟨66021959122103208137809207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88029278829470944183745609 66021959122103208137809207)
  ·
    refine ⟨99032938683154812206713811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66021959122103208137809207 99032938683154812206713811)
    ·
      refine ⟨148549408024732218310070717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99032938683154812206713811 148549408024732218310070717)
      ·
        refine ⟨55706028009274581866276519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 148549408024732218310070717 55706028009274581866276519)
        ·
          refine ⟨83559042013911872799414779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55706028009274581866276519 83559042013911872799414779)
          ·
            refine ⟨125338563020867809199122169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83559042013911872799414779 125338563020867809199122169)
            ·
              refine ⟨94003922265650856899341627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 125338563020867809199122169 94003922265650856899341627)
              ·
                refine ⟨141005883398476285349012441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 94003922265650856899341627 141005883398476285349012441)
                ·
                  refine ⟨105754412548857214011759331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 141005883398476285349012441 105754412548857214011759331)
                  ·
                    refine ⟨158631618823285821017638997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 105754412548857214011759331 158631618823285821017638997)
                    ·
                      refine ⟨1858964283085380715050457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 158631618823285821017638997 1858964283085380715050457)
                      ·
                        rfl

theorem cell23_3620320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 8].length) (baseStart_3620320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3620320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3620320 prefixEnd_3620320 := by exact prefixLift 3620320
  have htrace : WordTrace (prefixWord ++ tailWord_3620320) baseStart_3620320 baseEnd_3620320 := by
    simpa [prefixWord, tailWord_3620320, baseEnd_3620320] using wordTrace_append hprefix tailTrace_3620320
  have hstable : (prefixWord ++ tailWord_3620320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3620320).length < 2 ^ (prefixWord ++ tailWord_3620320).sum := by decide
  have hdescent : baseEnd_3620320 < baseStart_3620320 := by decide
  rcases family_descends (prefixWord ++ tailWord_3620320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3620451 : List Nat := [1, 1, 1, 5, 1, 3, 2, 2, 3, 1, 3]
def baseStart_3620451 : Nat := 118140960795 + 3620451 * 2 ^ 59
def prefixEnd_3620451 : Nat := 4983230072969 + 3 ^ 40 * 3620451 * 2
def baseEnd_3620451 : Nat := 1859031549051119702512355

theorem tailTrace_3620451 : CollatzResearch.WordTrace tailWord_3620451 prefixEnd_3620451 1859031549051119702512355 := by
  unfold tailWord_3620451
  simp only [CollatzResearch.WordTrace]
  refine ⟨132048696206731825648637207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88032464137821217099091471 132048696206731825648637207)
  ·
    refine ⟨198073044310097738472955811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132048696206731825648637207 198073044310097738472955811)
    ·
      refine ⟨297109566465146607709433717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198073044310097738472955811 297109566465146607709433717)
      ·
        refine ⟨27854021856107494472759411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 297109566465146607709433717 27854021856107494472759411)
        ·
          refine ⟨41781032784161241709139117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27854021856107494472759411 41781032784161241709139117)
          ·
            refine ⟨15667887294060465640927169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41781032784161241709139117 15667887294060465640927169)
            ·
              refine ⟨11750915470545349230695377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15667887294060465640927169 11750915470545349230695377)
              ·
                refine ⟨8813186602909011923021533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11750915470545349230695377 8813186602909011923021533)
                ·
                  refine ⟨3304944976090879471133075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8813186602909011923021533 3304944976090879471133075)
                  ·
                    refine ⟨4957417464136319206699613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3304944976090879471133075 4957417464136319206699613)
                    ·
                      refine ⟨1859031549051119702512355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4957417464136319206699613 1859031549051119702512355)
                      ·
                        rfl

theorem cell23_3620451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 2, 2, 3, 1, 3].length) (baseStart_3620451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3620451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3620451 prefixEnd_3620451 := by exact prefixLift 3620451
  have htrace : WordTrace (prefixWord ++ tailWord_3620451) baseStart_3620451 baseEnd_3620451 := by
    simpa [prefixWord, tailWord_3620451, baseEnd_3620451] using wordTrace_append hprefix tailTrace_3620451
  have hstable : (prefixWord ++ tailWord_3620451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3620451).length < 2 ^ (prefixWord ++ tailWord_3620451).sum := by decide
  have hdescent : baseEnd_3620451 < baseStart_3620451 := by decide
  rcases family_descends (prefixWord ++ tailWord_3620451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3620462 : List Nat := [4, 1, 2, 2, 4, 1, 1, 3, 1, 4]
def baseStart_3620462 : Nat := 118140960795 + 3620462 * 2 ^ 59
def prefixEnd_3620462 : Nat := 4983230072969 + 3 ^ 40 * 3620462 * 2
def baseEnd_3620462 : Nat := 619679065779439719824935

theorem tailTrace_3620462 : CollatzResearch.WordTrace tailWord_3620462 prefixEnd_3620462 619679065779439719824935 := by
  unfold tailWord_3620462
  simp only [CollatzResearch.WordTrace]
  refine ⟨16506137176211496815910955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 88032731606461316351525093 16506137176211496815910955)
  ·
    refine ⟨24759205764317245223866433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16506137176211496815910955 24759205764317245223866433)
    ·
      refine ⟨18569404323237933917899825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24759205764317245223866433 18569404323237933917899825)
      ·
        refine ⟨13927053242428450438424869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18569404323237933917899825 13927053242428450438424869)
        ·
          refine ⟨2611322482955334457204663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13927053242428450438424869 2611322482955334457204663)
          ·
            refine ⟨3916983724433001685806995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2611322482955334457204663 3916983724433001685806995)
            ·
              refine ⟨5875475586649502528710493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3916983724433001685806995 5875475586649502528710493)
              ·
                refine ⟨2203303344993563448266435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5875475586649502528710493 2203303344993563448266435)
                ·
                  refine ⟨3304955017490345172399653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2203303344993563448266435 3304955017490345172399653)
                  ·
                    refine ⟨619679065779439719824935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3304955017490345172399653 619679065779439719824935)
                    ·
                      rfl

theorem cell23_3620462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 4, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 4, 1, 1, 3, 1, 4].length) (baseStart_3620462 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3620462 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3620462 prefixEnd_3620462 := by exact prefixLift 3620462
  have htrace : WordTrace (prefixWord ++ tailWord_3620462) baseStart_3620462 baseEnd_3620462 := by
    simpa [prefixWord, tailWord_3620462, baseEnd_3620462] using wordTrace_append hprefix tailTrace_3620462
  have hstable : (prefixWord ++ tailWord_3620462).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3620462).length < 2 ^ (prefixWord ++ tailWord_3620462).sum := by decide
  have hdescent : baseEnd_3620462 < baseStart_3620462 := by decide
  rcases family_descends (prefixWord ++ tailWord_3620462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3620485 : List Nat := [1, 3, 1, 1, 4, 1, 5, 2, 1, 1, 3]
def baseStart_3620485 : Nat := 118140960795 + 3620485 * 2 ^ 59
def prefixEnd_3620485 : Nat := 4983230072969 + 3 ^ 40 * 3620485 * 2
def baseEnd_3620485 : Nat := 1859049007393372569487199

theorem tailTrace_3620485 : CollatzResearch.WordTrace tailWord_3620485 prefixEnd_3620485 1859049007393372569487199 := by
  unfold tailWord_3620485
  simp only [CollatzResearch.WordTrace]
  refine ⟨132049936288608649455374909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88033290859072432970249939 132049936288608649455374909)
  ·
    refine ⟨49518726108228243545765591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 132049936288608649455374909 49518726108228243545765591)
    ·
      refine ⟨74278089162342365318648387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49518726108228243545765591 74278089162342365318648387)
      ·
        refine ⟨111417133743513547977972581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74278089162342365318648387 111417133743513547977972581)
        ·
          refine ⟨20890712576908790245869859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 111417133743513547977972581 20890712576908790245869859)
          ·
            refine ⟨31336068865363185368804789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20890712576908790245869859 31336068865363185368804789)
            ·
              refine ⟨2937756456127798628325449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 31336068865363185368804789 2937756456127798628325449)
              ·
                refine ⟨2203317342095848971244087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2937756456127798628325449 2203317342095848971244087)
                ·
                  refine ⟨3304976013143773456866131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2203317342095848971244087 3304976013143773456866131)
                  ·
                    refine ⟨4957464019715660185299197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3304976013143773456866131 4957464019715660185299197)
                    ·
                      refine ⟨1859049007393372569487199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4957464019715660185299197 1859049007393372569487199)
                      ·
                        rfl

theorem cell23_3620485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 5, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 5, 2, 1, 1, 3].length) (baseStart_3620485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3620485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3620485 prefixEnd_3620485 := by exact prefixLift 3620485
  have htrace : WordTrace (prefixWord ++ tailWord_3620485) baseStart_3620485 baseEnd_3620485 := by
    simpa [prefixWord, tailWord_3620485, baseEnd_3620485] using wordTrace_append hprefix tailTrace_3620485
  have hstable : (prefixWord ++ tailWord_3620485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3620485).length < 2 ^ (prefixWord ++ tailWord_3620485).sum := by decide
  have hdescent : baseEnd_3620485 < baseStart_3620485 := by decide
  rcases family_descends (prefixWord ++ tailWord_3620485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3620504 : List Nat := [2, 1, 2, 4, 1, 2, 2, 1, 1, 1, 6]
def baseStart_3620504 : Nat := 118140960795 + 3620504 * 2 ^ 59
def prefixEnd_3620504 : Nat := 4983230072969 + 3 ^ 40 * 3620504 * 2
def baseEnd_3620504 : Nat := 1859058763525807995149611

theorem tailTrace_3620504 : CollatzResearch.WordTrace tailWord_3620504 prefixEnd_3620504 1859058763525807995149611 := by
  unfold tailWord_3620504
  simp only [CollatzResearch.WordTrace]
  refine ⟨66025314637769907850158283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88033752850359877133544377 66025314637769907850158283)
  ·
    refine ⟨99037971956654861775237425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66025314637769907850158283 99037971956654861775237425)
    ·
      refine ⟨74278478967491146331428069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99037971956654861775237425 74278478967491146331428069)
      ·
        refine ⟨13927214806404589937142763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 74278478967491146331428069 13927214806404589937142763)
        ·
          refine ⟨20890822209606884905714145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13927214806404589937142763 20890822209606884905714145)
          ·
            refine ⟨15668116657205163679285609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20890822209606884905714145 15668116657205163679285609)
            ·
              refine ⟨11751087492903872759464207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15668116657205163679285609 11751087492903872759464207)
              ·
                refine ⟨17626631239355809139196311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11751087492903872759464207 17626631239355809139196311)
                ·
                  refine ⟨26439946859033713708794467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17626631239355809139196311 26439946859033713708794467)
                  ·
                    refine ⟨39659920288550570563191701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26439946859033713708794467 39659920288550570563191701)
                    ·
                      refine ⟨1859058763525807995149611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 39659920288550570563191701 1859058763525807995149611)
                      ·
                        rfl

theorem cell23_3620504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 2, 1, 1, 1, 6].length) (baseStart_3620504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3620504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3620504 prefixEnd_3620504 := by exact prefixLift 3620504
  have htrace : WordTrace (prefixWord ++ tailWord_3620504) baseStart_3620504 baseEnd_3620504 := by
    simpa [prefixWord, tailWord_3620504, baseEnd_3620504] using wordTrace_append hprefix tailTrace_3620504
  have hstable : (prefixWord ++ tailWord_3620504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3620504).length < 2 ^ (prefixWord ++ tailWord_3620504).sum := by decide
  have hdescent : baseEnd_3620504 < baseStart_3620504 := by decide
  rcases family_descends (prefixWord ++ tailWord_3620504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3620542 : List Nat := [4, 2, 1, 1, 2, 3, 1, 4, 1, 2, 2]
def baseStart_3620542 : Nat := 118140960795 + 3620542 * 2 ^ 59
def prefixEnd_3620542 : Nat := 4983230072969 + 3 ^ 40 * 3620542 * 2
def baseEnd_3620542 : Nat := 1859078275790678846474437

theorem tailTrace_3620542 : CollatzResearch.WordTrace tailWord_3620542 prefixEnd_3620542 1859078275790678846474437 := by
  unfold tailWord_3620542
  simp only [CollatzResearch.WordTrace]
  refine ⟨16506501906175268523774985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 88034676832934765460133253 16506501906175268523774985)
  ·
    refine ⟨12379876429631451392831239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16506501906175268523774985 12379876429631451392831239)
    ·
      refine ⟨18569814644447177089246859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12379876429631451392831239 18569814644447177089246859)
      ·
        refine ⟨27854721966670765633870289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18569814644447177089246859 27854721966670765633870289)
        ·
          refine ⟨20891041475003074225402717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27854721966670765633870289 20891041475003074225402717)
          ·
            refine ⟨7834140553126152834526019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20891041475003074225402717 7834140553126152834526019)
            ·
              refine ⟨11751210829689229251789029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7834140553126152834526019 11751210829689229251789029)
              ·
                refine ⟨2203352030566730484710443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11751210829689229251789029 2203352030566730484710443)
                ·
                  refine ⟨3305028045850095727065665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2203352030566730484710443 3305028045850095727065665)
                  ·
                    refine ⟨2478771034387571795299249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3305028045850095727065665 2478771034387571795299249)
                    ·
                      refine ⟨1859078275790678846474437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2478771034387571795299249 1859078275790678846474437)
                      ·
                        rfl

theorem cell23_3620542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 1, 4, 1, 2, 2].length) (baseStart_3620542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3620542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3620542 prefixEnd_3620542 := by exact prefixLift 3620542
  have htrace : WordTrace (prefixWord ++ tailWord_3620542) baseStart_3620542 baseEnd_3620542 := by
    simpa [prefixWord, tailWord_3620542, baseEnd_3620542] using wordTrace_append hprefix tailTrace_3620542
  have hstable : (prefixWord ++ tailWord_3620542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3620542).length < 2 ^ (prefixWord ++ tailWord_3620542).sum := by decide
  have hdescent : baseEnd_3620542 < baseStart_3620542 := by decide
  rcases family_descends (prefixWord ++ tailWord_3620542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3620551 : List Nat := [1, 1, 4, 1, 1, 1, 3, 1, 5, 3, 2]
def baseStart_3620551 : Nat := 118140960795 + 3620551 * 2 ^ 59
def prefixEnd_3620551 : Nat := 4983230072969 + 3 ^ 40 * 3620551 * 2
def baseEnd_3620551 : Nat := 1859082897116569311261895

theorem tailTrace_3620551 : CollatzResearch.WordTrace tailWord_3620551 prefixEnd_3620551 1859082897116569311261895 := by
  unfold tailWord_3620551
  simp only [CollatzResearch.WordTrace]
  refine ⟨132052343506369542727277507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88034895670913028484851671 132052343506369542727277507)
  ·
    refine ⟨198078515259554314090916261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132052343506369542727277507 198078515259554314090916261)
    ·
      refine ⟨37139721611166433892046799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 198078515259554314090916261 37139721611166433892046799)
      ·
        refine ⟨55709582416749650838070199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37139721611166433892046799 55709582416749650838070199)
        ·
          refine ⟨83564373625124476257105299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55709582416749650838070199 83564373625124476257105299)
          ·
            refine ⟨125346560437686714385657949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83564373625124476257105299 125346560437686714385657949)
            ·
              refine ⟨47004960164132517894621731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 125346560437686714385657949 47004960164132517894621731)
              ·
                refine ⟨70507440246198776841932597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47004960164132517894621731 70507440246198776841932597)
                ·
                  refine ⟨6610072523081135328931181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 70507440246198776841932597 6610072523081135328931181)
                  ·
                    refine ⟨2478777196155425748349193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6610072523081135328931181 2478777196155425748349193)
                    ·
                      refine ⟨1859082897116569311261895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2478777196155425748349193 1859082897116569311261895)
                      ·
                        rfl

theorem cell23_3620551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 1, 5, 3, 2].length) (baseStart_3620551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3620551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3620551 prefixEnd_3620551 := by exact prefixLift 3620551
  have htrace : WordTrace (prefixWord ++ tailWord_3620551) baseStart_3620551 baseEnd_3620551 := by
    simpa [prefixWord, tailWord_3620551, baseEnd_3620551] using wordTrace_append hprefix tailTrace_3620551
  have hstable : (prefixWord ++ tailWord_3620551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3620551).length < 2 ^ (prefixWord ++ tailWord_3620551).sum := by decide
  have hdescent : baseEnd_3620551 < baseStart_3620551 := by decide
  rcases family_descends (prefixWord ++ tailWord_3620551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3620558 : List Nat := [4, 1, 1, 1, 3, 1, 1, 5, 2, 1, 3]
def baseStart_3620558 : Nat := 118140960795 + 3620558 * 2 ^ 59
def prefixEnd_3620558 : Nat := 4983230072969 + 3 ^ 40 * 3620558 * 2
def baseEnd_3620558 : Nat := 1859086491481150783874363

theorem tailTrace_3620558 : CollatzResearch.WordTrace tailWord_3620558 prefixEnd_3620558 1859086491481150783874363 := by
  unfold tailWord_3620558
  simp only [CollatzResearch.WordTrace]
  refine ⟨16506574852168022865347791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 88035065878229455281854885 16506574852168022865347791)
  ·
    refine ⟨24759862278252034298021687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16506574852168022865347791 24759862278252034298021687)
    ·
      refine ⟨37139793417378051447032531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24759862278252034298021687 37139793417378051447032531)
      ·
        refine ⟨55709690126067077170548797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37139793417378051447032531 55709690126067077170548797)
        ·
          refine ⟨20891133797275153938955799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55709690126067077170548797 20891133797275153938955799)
          ·
            refine ⟨31336700695912730908433699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20891133797275153938955799 31336700695912730908433699)
            ·
              refine ⟨47005051043869096362650549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31336700695912730908433699 47005051043869096362650549)
              ·
                refine ⟨4406723535362727783998489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 47005051043869096362650549 4406723535362727783998489)
                ·
                  refine ⟨3305042651522045837998867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4406723535362727783998489 3305042651522045837998867)
                  ·
                    refine ⟨4957563977283068756998301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3305042651522045837998867 4957563977283068756998301)
                    ·
                      refine ⟨1859086491481150783874363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4957563977283068756998301 1859086491481150783874363)
                      ·
                        rfl

theorem cell23_3620558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 5, 2, 1, 3].length) (baseStart_3620558 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3620558 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3620558 prefixEnd_3620558 := by exact prefixLift 3620558
  have htrace : WordTrace (prefixWord ++ tailWord_3620558) baseStart_3620558 baseEnd_3620558 := by
    simpa [prefixWord, tailWord_3620558, baseEnd_3620558] using wordTrace_append hprefix tailTrace_3620558
  have hstable : (prefixWord ++ tailWord_3620558).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3620558).length < 2 ^ (prefixWord ++ tailWord_3620558).sum := by decide
  have hdescent : baseEnd_3620558 < baseStart_3620558 := by decide
  rcases family_descends (prefixWord ++ tailWord_3620558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3620568 : List Nat := [2, 1, 2, 2, 3, 1, 2, 4, 1, 3, 2]
def baseStart_3620568 : Nat := 118140960795 + 3620568 * 2 ^ 59
def prefixEnd_3620568 : Nat := 4983230072969 + 3 ^ 40 * 3620568 * 2
def baseEnd_3620568 : Nat := 1859091626287695744749317

theorem tailTrace_3620568 : CollatzResearch.WordTrace tailWord_3620568 prefixEnd_3620568 1859091626287695744749317 := by
  unfold tailWord_3620568
  simp only [CollatzResearch.WordTrace]
  refine ⟨66026481773653977315323179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88035309031538636420430905 66026481773653977315323179)
  ·
    refine ⟨99039722660480965972984769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66026481773653977315323179 99039722660480965972984769)
    ·
      refine ⟨74279791995360724479738577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99039722660480965972984769 74279791995360724479738577)
      ·
        refine ⟨55709843996520543359803933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74279791995360724479738577 55709843996520543359803933)
        ·
          refine ⟨20891191498695203759926475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55709843996520543359803933 20891191498695203759926475)
          ·
            refine ⟨31336787248042805639889713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20891191498695203759926475 31336787248042805639889713)
            ·
              refine ⟨23502590436032104229917285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31336787248042805639889713 23502590436032104229917285)
              ·
                refine ⟨4406735706756019543109491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23502590436032104229917285 4406735706756019543109491)
                ·
                  refine ⟨6610103560134029314664237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4406735706756019543109491 6610103560134029314664237)
                  ·
                    refine ⟨2478788835050260992999089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6610103560134029314664237 2478788835050260992999089)
                    ·
                      refine ⟨1859091626287695744749317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2478788835050260992999089 1859091626287695744749317)
                      ·
                        rfl

theorem cell23_3620568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 2, 4, 1, 3, 2].length) (baseStart_3620568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3620568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3620568 prefixEnd_3620568 := by exact prefixLift 3620568
  have htrace : WordTrace (prefixWord ++ tailWord_3620568) baseStart_3620568 baseEnd_3620568 := by
    simpa [prefixWord, tailWord_3620568, baseEnd_3620568] using wordTrace_append hprefix tailTrace_3620568
  have hstable : (prefixWord ++ tailWord_3620568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3620568).length < 2 ^ (prefixWord ++ tailWord_3620568).sum := by decide
  have hdescent : baseEnd_3620568 < baseStart_3620568 := by decide
  rcases family_descends (prefixWord ++ tailWord_3620568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3620681 : List Nat := [1, 2, 1, 1, 2, 4, 2, 1, 5, 4]
def baseStart_3620681 : Nat := 118140960795 + 3620681 * 2 ^ 59
def prefixEnd_3620681 : Nat := 4983230072969 + 3 ^ 40 * 3620681 * 2
def baseEnd_3620681 : Nat := 619716549867217934212099

theorem tailTrace_3620681 : CollatzResearch.WordTrace tailWord_3620681 prefixEnd_3620681 619716549867217934212099 := by
  unfold tailWord_3620681
  simp only [CollatzResearch.WordTrace]
  refine ⟨132057084995898574929509897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88038056663932383286339931 132057084995898574929509897)
  ·
    refine ⟨99042813746923931197132423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132057084995898574929509897 99042813746923931197132423)
    ·
      refine ⟨148564220620385896795698635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99042813746923931197132423 148564220620385896795698635)
      ·
        refine ⟨222846330930578845193547953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148564220620385896795698635 222846330930578845193547953)
        ·
          refine ⟨167134748197934133895160965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 222846330930578845193547953 167134748197934133895160965)
          ·
            refine ⟨31337765287112650105342681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 167134748197934133895160965 31337765287112650105342681)
            ·
              refine ⟨23503323965334487579007011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31337765287112650105342681 23503323965334487579007011)
              ·
                refine ⟨35254985948001731368510517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23503323965334487579007011 35254985948001731368510517)
                ·
                  refine ⟨3305154932625162315797861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 35254985948001731368510517 3305154932625162315797861)
                  ·
                    refine ⟨619716549867217934212099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3305154932625162315797861 619716549867217934212099)
                    ·
                      rfl

theorem cell23_3620681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 2, 1, 5, 4].length) (baseStart_3620681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3620681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3620681 prefixEnd_3620681 := by exact prefixLift 3620681
  have htrace : WordTrace (prefixWord ++ tailWord_3620681) baseStart_3620681 baseEnd_3620681 := by
    simpa [prefixWord, tailWord_3620681, baseEnd_3620681] using wordTrace_append hprefix tailTrace_3620681
  have hstable : (prefixWord ++ tailWord_3620681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3620681).length < 2 ^ (prefixWord ++ tailWord_3620681).sum := by decide
  have hdescent : baseEnd_3620681 < baseStart_3620681 := by decide
  rcases family_descends (prefixWord ++ tailWord_3620681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3620685 : List Nat := [1, 6, 1, 2, 1, 2, 2, 1, 2, 5]
def baseStart_3620685 : Nat := 118140960795 + 3620685 * 2 ^ 59
def prefixEnd_3620685 : Nat := 4983230072969 + 3 ^ 40 * 3620685 * 2
def baseEnd_3620685 : Nat := 619717234508090595662093

theorem tailTrace_3620685 : CollatzResearch.WordTrace tailWord_3620685 prefixEnd_3620685 619717234508090595662093 := by
  unfold tailWord_3620685
  simp only [CollatzResearch.WordTrace]
  refine ⟨132057230887884083612655509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88038153925256055741770339 132057230887884083612655509)
  ·
    refine ⟨6190182697869566419343227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 132057230887884083612655509 6190182697869566419343227)
    ·
      refine ⟨9285274046804349629014841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6190182697869566419343227 9285274046804349629014841)
      ·
        refine ⟨6963955535103262221761131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9285274046804349629014841 6963955535103262221761131)
        ·
          refine ⟨10445933302654893332641697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6963955535103262221761131 10445933302654893332641697)
          ·
            refine ⟨7834449976991169999481273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10445933302654893332641697 7834449976991169999481273)
            ·
              refine ⟨5875837482743377499610955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7834449976991169999481273 5875837482743377499610955)
              ·
                refine ⟨8813756224115066249416433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5875837482743377499610955 8813756224115066249416433)
                ·
                  refine ⟨6610317168086299687062325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8813756224115066249416433 6610317168086299687062325)
                  ·
                    refine ⟨619717234508090595662093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6610317168086299687062325 619717234508090595662093)
                    ·
                      rfl

theorem cell23_3620685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 2, 1, 2, 5].length) (baseStart_3620685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3620685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3620685 prefixEnd_3620685 := by exact prefixLift 3620685
  have htrace : WordTrace (prefixWord ++ tailWord_3620685) baseStart_3620685 baseEnd_3620685 := by
    simpa [prefixWord, tailWord_3620685, baseEnd_3620685] using wordTrace_append hprefix tailTrace_3620685
  have hstable : (prefixWord ++ tailWord_3620685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3620685).length < 2 ^ (prefixWord ++ tailWord_3620685).sum := by decide
  have hdescent : baseEnd_3620685 < baseStart_3620685 := by decide
  rcases family_descends (prefixWord ++ tailWord_3620685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3620741 : List Nat := [1, 3, 1, 1, 3, 2, 1, 3, 3, 5]
def baseStart_3620741 : Nat := 118140960795 + 3620741 * 2 ^ 59
def prefixEnd_3620741 : Nat := 4983230072969 + 3 ^ 40 * 3620741 * 2
def baseEnd_3620741 : Nat := 619726819480307855962007

theorem tailTrace_3620741 : CollatzResearch.WordTrace tailWord_3620741 prefixEnd_3620741 619726819480307855962007 := by
  unfold tailWord_3620741
  simp only [CollatzResearch.WordTrace]
  refine ⟨132059273375681205176694077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88039515583787470117796051 132059273375681205176694077)
  ·
    refine ⟨49522227515880451941260279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 132059273375681205176694077 49522227515880451941260279)
    ·
      refine ⟨74283341273820677911890419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49522227515880451941260279 74283341273820677911890419)
      ·
        refine ⟨111425011910731016867835629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74283341273820677911890419 111425011910731016867835629)
        ·
          refine ⟨41784379466524131325438361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 111425011910731016867835629 41784379466524131325438361)
          ·
            refine ⟨31338284599893098494078771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41784379466524131325438361 31338284599893098494078771)
            ·
              refine ⟨47007426899839647741118157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31338284599893098494078771 47007426899839647741118157)
              ·
                refine ⟨17627785087439867902919309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47007426899839647741118157 17627785087439867902919309)
                ·
                  refine ⟨6610419407789950463594741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17627785087439867902919309 6610419407789950463594741)
                  ·
                    refine ⟨619726819480307855962007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6610419407789950463594741 619726819480307855962007)
                    ·
                      rfl

theorem cell23_3620741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 3, 3, 5].length) (baseStart_3620741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3620741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3620741 prefixEnd_3620741 := by exact prefixLift 3620741
  have htrace : WordTrace (prefixWord ++ tailWord_3620741) baseStart_3620741 baseEnd_3620741 := by
    simpa [prefixWord, tailWord_3620741, baseEnd_3620741] using wordTrace_append hprefix tailTrace_3620741
  have hstable : (prefixWord ++ tailWord_3620741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3620741).length < 2 ^ (prefixWord ++ tailWord_3620741).sum := by decide
  have hdescent : baseEnd_3620741 < baseStart_3620741 := by decide
  rcases family_descends (prefixWord ++ tailWord_3620741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3620772 : List Nat := [2, 3, 1, 2, 1, 3, 2, 4, 1, 1, 3]
def baseStart_3620772 : Nat := 118140960795 + 3620772 * 2 ^ 59
def prefixEnd_3620772 : Nat := 4983230072969 + 3 ^ 40 * 3620772 * 2
def baseEnd_3620772 : Nat := 1859196376341212946598379

theorem tailTrace_3620772 : CollatzResearch.WordTrace tailWord_3620772 prefixEnd_3620772 1859196376341212946598379 := by
  unfold tailWord_3620772
  simp only [CollatzResearch.WordTrace]
  refine ⟨66030202019284448735536285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88040269359045931647381713 66030202019284448735536285)
  ·
    refine ⟨24761325757231668275826107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66030202019284448735536285 24761325757231668275826107)
    ·
      refine ⟨37141988635847502413739161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24761325757231668275826107 37141988635847502413739161)
      ·
        refine ⟨27856491476885626810304371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37141988635847502413739161 27856491476885626810304371)
        ·
          refine ⟨41784737215328440215456557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27856491476885626810304371 41784737215328440215456557)
          ·
            refine ⟨15669276455748165080796209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41784737215328440215456557 15669276455748165080796209)
            ·
              refine ⟨11751957341811123810597157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15669276455748165080796209 11751957341811123810597157)
              ·
                refine ⟨2203492001589585714486967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11751957341811123810597157 2203492001589585714486967)
                ·
                  refine ⟨3305238002384378571730451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2203492001589585714486967 3305238002384378571730451)
                  ·
                    refine ⟨4957857003576567857595677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3305238002384378571730451 4957857003576567857595677)
                    ·
                      refine ⟨1859196376341212946598379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4957857003576567857595677 1859196376341212946598379)
                      ·
                        rfl

theorem cell23_3620772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 2, 4, 1, 1, 3].length) (baseStart_3620772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3620772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3620772 prefixEnd_3620772 := by exact prefixLift 3620772
  have htrace : WordTrace (prefixWord ++ tailWord_3620772) baseStart_3620772 baseEnd_3620772 := by
    simpa [prefixWord, tailWord_3620772, baseEnd_3620772] using wordTrace_append hprefix tailTrace_3620772
  have hstable : (prefixWord ++ tailWord_3620772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3620772).length < 2 ^ (prefixWord ++ tailWord_3620772).sum := by decide
  have hdescent : baseEnd_3620772 < baseStart_3620772 := by decide
  rcases family_descends (prefixWord ++ tailWord_3620772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3620839 : List Nat := [1, 1, 5, 2, 3, 2, 2, 1, 2, 4]
def baseStart_3620839 : Nat := 118140960795 + 3620839 * 2 ^ 59
def prefixEnd_3620839 : Nat := 4983230072969 + 3 ^ 40 * 3620839 * 2
def baseEnd_3620839 : Nat := 619743593181688061486857

theorem tailTrace_3620839 : CollatzResearch.WordTrace tailWord_3620839 prefixEnd_3620839 619743593181688061486857 := by
  unfold tailWord_3620839
  simp only [CollatzResearch.WordTrace]
  refine ⟨132062847729326167913761571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88041898486217445275841047 132062847729326167913761571)
  ·
    refine ⟨198094271593989251870642357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132062847729326167913761571 198094271593989251870642357)
    ·
      refine ⟨18571337961936492362872721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 198094271593989251870642357 18571337961936492362872721)
      ·
        refine ⟨13928503471452369272154541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18571337961936492362872721 13928503471452369272154541)
        ·
          refine ⟨5223188801794638477057953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13928503471452369272154541 5223188801794638477057953)
          ·
            refine ⟨3917391601345978857793465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5223188801794638477057953 3917391601345978857793465)
            ·
              refine ⟨2938043701009484143345099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3917391601345978857793465 2938043701009484143345099)
              ·
                refine ⟨4407065551514226215017649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2938043701009484143345099 4407065551514226215017649)
                ·
                  refine ⟨3305299163635669661263237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4407065551514226215017649 3305299163635669661263237)
                  ·
                    refine ⟨619743593181688061486857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3305299163635669661263237 619743593181688061486857)
                    ·
                      rfl

theorem cell23_3620839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 2, 2, 1, 2, 4].length) (baseStart_3620839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3620839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3620839 prefixEnd_3620839 := by exact prefixLift 3620839
  have htrace : WordTrace (prefixWord ++ tailWord_3620839) baseStart_3620839 baseEnd_3620839 := by
    simpa [prefixWord, tailWord_3620839, baseEnd_3620839] using wordTrace_append hprefix tailTrace_3620839
  have hstable : (prefixWord ++ tailWord_3620839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3620839).length < 2 ^ (prefixWord ++ tailWord_3620839).sum := by decide
  have hdescent : baseEnd_3620839 < baseStart_3620839 := by decide
  rcases family_descends (prefixWord ++ tailWord_3620839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3620849 : List Nat := [1, 2, 2, 2, 6, 1, 1, 2, 1, 2, 3]
def baseStart_3620849 : Nat := 118140960795 + 3620849 * 2 ^ 59
def prefixEnd_3620849 : Nat := 4983230072969 + 3 ^ 40 * 3620849 * 2
def baseEnd_3620849 : Nat := 1859235914351609145335525

theorem tailTrace_3620849 : CollatzResearch.WordTrace tailWord_3620849 prefixEnd_3620849 1859235914351609145335525 := by
  unfold tailWord_3620849
  simp only [CollatzResearch.WordTrace]
  refine ⟨132063212459289939621625601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88042141639526626414417067 132063212459289939621625601)
  ·
    refine ⟨99047409344467454716219201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132063212459289939621625601 99047409344467454716219201)
    ·
      refine ⟨74285557008350591037164401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99047409344467454716219201 74285557008350591037164401)
      ·
        refine ⟨55714167756262943277873301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74285557008350591037164401 55714167756262943277873301)
        ·
          refine ⟨2611601613574825466150311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 55714167756262943277873301 2611601613574825466150311)
          ·
            refine ⟨3917402420362238199225467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2611601613574825466150311 3917402420362238199225467)
            ·
              refine ⟨5876103630543357298838201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3917402420362238199225467 5876103630543357298838201)
              ·
                refine ⟨4407077722907517974128651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5876103630543357298838201 4407077722907517974128651)
                ·
                  refine ⟨6610616584361276961192977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4407077722907517974128651 6610616584361276961192977)
                  ·
                    refine ⟨4957962438270957720894733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6610616584361276961192977 4957962438270957720894733)
                    ·
                      refine ⟨1859235914351609145335525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4957962438270957720894733 1859235914351609145335525)
                      ·
                        rfl

theorem cell23_3620849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 6, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 6, 1, 1, 2, 1, 2, 3].length) (baseStart_3620849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3620849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3620849 prefixEnd_3620849 := by exact prefixLift 3620849
  have htrace : WordTrace (prefixWord ++ tailWord_3620849) baseStart_3620849 baseEnd_3620849 := by
    simpa [prefixWord, tailWord_3620849, baseEnd_3620849] using wordTrace_append hprefix tailTrace_3620849
  have hstable : (prefixWord ++ tailWord_3620849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3620849).length < 2 ^ (prefixWord ++ tailWord_3620849).sum := by decide
  have hdescent : baseEnd_3620849 < baseStart_3620849 := by decide
  rcases family_descends (prefixWord ++ tailWord_3620849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3620862 : List Nat := [4, 2, 2, 2, 1, 2, 1, 2, 1, 3, 3]
def baseStart_3620862 : Nat := 118140960795 + 3620862 * 2 ^ 59
def prefixEnd_3620862 : Nat := 4983230072969 + 3 ^ 40 * 3620862 * 2
def baseEnd_3620862 : Nat := 1859242589600117594472965

theorem tailTrace_3620862 : CollatzResearch.WordTrace tailWord_3620862 prefixEnd_3620862 1859242589600117594472965 := by
  unfold tailWord_3620862
  simp only [CollatzResearch.WordTrace]
  refine ⟨16507960826030355355231105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 88042457738828561894565893 16507960826030355355231105)
  ·
    refine ⟨12380970619522766516423329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16507960826030355355231105 12380970619522766516423329)
    ·
      refine ⟨9285727964642074887317497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12380970619522766516423329 9285727964642074887317497)
      ·
        refine ⟨6964295973481556165488123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9285727964642074887317497 6964295973481556165488123)
        ·
          refine ⟨10446443960222334248232185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6964295973481556165488123 10446443960222334248232185)
          ·
            refine ⟨7834832970166750686174139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10446443960222334248232185 7834832970166750686174139)
            ·
              refine ⟨11752249455250126029261209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7834832970166750686174139 11752249455250126029261209)
              ·
                refine ⟨8814187091437594521945907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11752249455250126029261209 8814187091437594521945907)
                ·
                  refine ⟨13221280637156391782918861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8814187091437594521945907 13221280637156391782918861)
                  ·
                    refine ⟨4957980238933646918594573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13221280637156391782918861 4957980238933646918594573)
                    ·
                      refine ⟨1859242589600117594472965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4957980238933646918594573 1859242589600117594472965)
                      ·
                        rfl

theorem cell23_3620862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 1, 2, 1, 3, 3].length) (baseStart_3620862 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3620862 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3620862 prefixEnd_3620862 := by exact prefixLift 3620862
  have htrace : WordTrace (prefixWord ++ tailWord_3620862) baseStart_3620862 baseEnd_3620862 := by
    simpa [prefixWord, tailWord_3620862, baseEnd_3620862] using wordTrace_append hprefix tailTrace_3620862
  have hstable : (prefixWord ++ tailWord_3620862).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3620862).length < 2 ^ (prefixWord ++ tailWord_3620862).sum := by decide
  have hdescent : baseEnd_3620862 < baseStart_3620862 := by decide
  rcases family_descends (prefixWord ++ tailWord_3620862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3620878 : List Nat := [4, 1, 1, 2, 2, 1, 2, 2, 2, 6]
def baseStart_3620878 : Nat := 118140960795 + 3620878 * 2 ^ 59
def prefixEnd_3620878 : Nat := 4983230072969 + 3 ^ 40 * 3620878 * 2
def baseEnd_3620878 : Nat := 619750268430196510624297

theorem tailTrace_3620878 : CollatzResearch.WordTrace tailWord_3620878 prefixEnd_3620878 619750268430196510624297 := by
  unfold tailWord_3620878
  simp only [CollatzResearch.WordTrace]
  refine ⟨16508033772023109696803911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 88042846784123251716287525 16508033772023109696803911)
  ·
    refine ⟨24762050658034664545205867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16508033772023109696803911 24762050658034664545205867)
    ·
      refine ⟨37143075987051996817808801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24762050658034664545205867 37143075987051996817808801)
      ·
        refine ⟨27857306990288997613356601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37143075987051996817808801 27857306990288997613356601)
        ·
          refine ⟨20892980242716748210017451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27857306990288997613356601 20892980242716748210017451)
          ·
            refine ⟨31339470364075122315026177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20892980242716748210017451 31339470364075122315026177)
            ·
              refine ⟨23504602773056341736269633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31339470364075122315026177 23504602773056341736269633)
              ·
                refine ⟨17628452079792256302202225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23504602773056341736269633 17628452079792256302202225)
                ·
                  refine ⟨13221339059844192226651669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17628452079792256302202225 13221339059844192226651669)
                  ·
                    refine ⟨619750268430196510624297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13221339059844192226651669 619750268430196510624297)
                    ·
                      rfl

theorem cell23_3620878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 2, 2, 2, 6].length) (baseStart_3620878 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3620878 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3620878 prefixEnd_3620878 := by exact prefixLift 3620878
  have htrace : WordTrace (prefixWord ++ tailWord_3620878) baseStart_3620878 baseEnd_3620878 := by
    simpa [prefixWord, tailWord_3620878, baseEnd_3620878] using wordTrace_append hprefix tailTrace_3620878
  have hstable : (prefixWord ++ tailWord_3620878).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3620878).length < 2 ^ (prefixWord ++ tailWord_3620878).sum := by decide
  have hdescent : baseEnd_3620878 < baseStart_3620878 := by decide
  rcases family_descends (prefixWord ++ tailWord_3620878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3620881 : List Nat := [1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 6]
def baseStart_3620881 : Nat := 118140960795 + 3620881 * 2 ^ 59
def prefixEnd_3620881 : Nat := 4983230072969 + 3 ^ 40 * 3620881 * 2
def baseEnd_3620881 : Nat := 1859252345732553020135377

theorem tailTrace_3620881 : CollatzResearch.WordTrace tailWord_3620881 prefixEnd_3620881 1859252345732553020135377 := by
  unfold tailWord_3620881
  simp only [CollatzResearch.WordTrace]
  refine ⟨132064379595174009086790497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88042919730116006057860331 132064379595174009086790497)
  ·
    refine ⟨99048284696380506815092873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132064379595174009086790497 99048284696380506815092873)
    ·
      refine ⟨74286213522285380111319655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99048284696380506815092873 74286213522285380111319655)
      ·
        refine ⟨111429320283428070166979483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74286213522285380111319655 111429320283428070166979483)
        ·
          refine ⟨167143980425142105250469225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111429320283428070166979483 167143980425142105250469225)
          ·
            refine ⟨125357985318856578937851919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 167143980425142105250469225 125357985318856578937851919)
            ·
              refine ⟨188036977978284868406777879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 125357985318856578937851919 188036977978284868406777879)
              ·
                refine ⟨282055466967427302610166819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 188036977978284868406777879 282055466967427302610166819)
                ·
                  refine ⟨423083200451140953915250229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 282055466967427302610166819 423083200451140953915250229)
                  ·
                    refine ⟨39664050042294464429554709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 423083200451140953915250229 39664050042294464429554709)
                    ·
                      refine ⟨1859252345732553020135377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 39664050042294464429554709 1859252345732553020135377)
                      ·
                        rfl

theorem cell23_3620881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 6].length) (baseStart_3620881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3620881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3620881 prefixEnd_3620881 := by exact prefixLift 3620881
  have htrace : WordTrace (prefixWord ++ tailWord_3620881) baseStart_3620881 baseEnd_3620881 := by
    simpa [prefixWord, tailWord_3620881, baseEnd_3620881] using wordTrace_append hprefix tailTrace_3620881
  have hstable : (prefixWord ++ tailWord_3620881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3620881).length < 2 ^ (prefixWord ++ tailWord_3620881).sum := by decide
  have hdescent : baseEnd_3620881 < baseStart_3620881 := by decide
  rcases family_descends (prefixWord ++ tailWord_3620881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3620888 : List Nat := [2, 1, 2, 3, 2, 1, 1, 1, 1, 6, 3]
def baseStart_3620888 : Nat := 118140960795 + 3620888 * 2 ^ 59
def prefixEnd_3620888 : Nat := 4983230072969 + 3 ^ 40 * 3620888 * 2
def baseEnd_3620888 : Nat := 1859255940097134492747845

theorem tailTrace_3620888 : CollatzResearch.WordTrace tailWord_3620888 prefixEnd_3620888 1859255940097134492747845 := by
  unfold tailWord_3620888
  simp only [CollatzResearch.WordTrace]
  refine ⟨66032317453074324641147659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88043089937432432854863545 66032317453074324641147659)
  ·
    refine ⟨99048476179611486961721489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66032317453074324641147659 99048476179611486961721489)
    ·
      refine ⟨74286357134708615221291117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99048476179611486961721489 74286357134708615221291117)
      ·
        refine ⟨27857383925515730707984169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74286357134708615221291117 27857383925515730707984169)
        ·
          refine ⟨20893037944136798030988127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27857383925515730707984169 20893037944136798030988127)
          ·
            refine ⟨31339556916205197046482191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20893037944136798030988127 31339556916205197046482191)
            ·
              refine ⟨47009335374307795569723287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31339556916205197046482191 47009335374307795569723287)
              ·
                refine ⟨70514003061461693354584931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47009335374307795569723287 70514003061461693354584931)
                ·
                  refine ⟨105771004592192540031877397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 70514003061461693354584931 105771004592192540031877397)
                  ·
                    refine ⟨4958015840259025313994253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 105771004592192540031877397 4958015840259025313994253)
                    ·
                      refine ⟨1859255940097134492747845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4958015840259025313994253 1859255940097134492747845)
                      ·
                        rfl

theorem cell23_3620888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 1, 1, 6, 3].length) (baseStart_3620888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3620888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3620888 prefixEnd_3620888 := by exact prefixLift 3620888
  have htrace : WordTrace (prefixWord ++ tailWord_3620888) baseStart_3620888 baseEnd_3620888 := by
    simpa [prefixWord, tailWord_3620888, baseEnd_3620888] using wordTrace_append hprefix tailTrace_3620888
  have hstable : (prefixWord ++ tailWord_3620888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3620888).length < 2 ^ (prefixWord ++ tailWord_3620888).sum := by decide
  have hdescent : baseEnd_3620888 < baseStart_3620888 := by decide
  rcases family_descends (prefixWord ++ tailWord_3620888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3620938 : List Nat := [3, 1, 2, 1, 1, 2, 1, 3, 4, 5]
def baseStart_3620938 : Nat := 118140960795 + 3620938 * 2 ^ 59
def prefixEnd_3620938 : Nat := 4983230072969 + 3 ^ 40 * 3620938 * 2
def baseEnd_3620938 : Nat := 619760538043286432374205

theorem tailTrace_3620938 : CollatzResearch.WordTrace tailWord_3620938 prefixEnd_3620938 619760538043286432374205 := by
  unfold tailWord_3620938
  simp only [CollatzResearch.WordTrace]
  refine ⟨33016614638991876955403867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88044305703978338547743645 33016614638991876955403867)
  ·
    refine ⟨49524921958487815433105801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33016614638991876955403867 49524921958487815433105801)
    ·
      refine ⟨37143691468865861574829351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49524921958487815433105801 37143691468865861574829351)
      ·
        refine ⟨55715537203298792362244027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37143691468865861574829351 55715537203298792362244027)
        ·
          refine ⟨83573305804948188543366041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55715537203298792362244027 83573305804948188543366041)
          ·
            refine ⟨62679979353711141407524531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83573305804948188543366041 62679979353711141407524531)
            ·
              refine ⟨94019969030566712111286797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62679979353711141407524531 94019969030566712111286797)
              ·
                refine ⟨35257488386462517041732549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 94019969030566712111286797 35257488386462517041732549)
                ·
                  refine ⟨6610779072461721945324853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35257488386462517041732549 6610779072461721945324853)
                  ·
                    refine ⟨619760538043286432374205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6610779072461721945324853 619760538043286432374205)
                    ·
                      rfl

theorem cell23_3620938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 3, 4, 5].length) (baseStart_3620938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3620938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3620938 prefixEnd_3620938 := by exact prefixLift 3620938
  have htrace : WordTrace (prefixWord ++ tailWord_3620938) baseStart_3620938 baseEnd_3620938 := by
    simpa [prefixWord, tailWord_3620938, baseEnd_3620938] using wordTrace_append hprefix tailTrace_3620938
  have hstable : (prefixWord ++ tailWord_3620938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3620938).length < 2 ^ (prefixWord ++ tailWord_3620938).sum := by decide
  have hdescent : baseEnd_3620938 < baseStart_3620938 := by decide
  rcases family_descends (prefixWord ++ tailWord_3620938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3620948 : List Nat := [2, 4, 1, 1, 1, 1, 1, 3, 1, 1, 7]
def baseStart_3620948 : Nat := 118140960795 + 3620948 * 2 ^ 59
def prefixEnd_3620948 : Nat := 4983230072969 + 3 ^ 40 * 3620948 * 2
def baseEnd_3620948 : Nat := 1859286748936404257997569

theorem tailTrace_3620948 : CollatzResearch.WordTrace tailWord_3620948 prefixEnd_3620948 1859286748936404257997569 := by
  unfold tailWord_3620948
  simp only [CollatzResearch.WordTrace]
  refine ⟨66033411642965639764739749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88044548857287519686319665 66033411642965639764739749)
  ·
    refine ⟨12381264683056057455888703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 66033411642965639764739749 12381264683056057455888703)
    ·
      refine ⟨18571897024584086183833055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12381264683056057455888703 18571897024584086183833055)
      ·
        refine ⟨27857845536876129275749583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18571897024584086183833055 27857845536876129275749583)
        ·
          refine ⟨41786768305314193913624375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27857845536876129275749583 41786768305314193913624375)
          ·
            refine ⟨62680152457971290870436563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41786768305314193913624375 62680152457971290870436563)
            ·
              refine ⟨94020228686956936305654845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62680152457971290870436563 94020228686956936305654845)
              ·
                refine ⟨35257585757608851114620567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 94020228686956936305654845 35257585757608851114620567)
                ·
                  refine ⟨52886378636413276671930851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35257585757608851114620567 52886378636413276671930851)
                  ·
                    refine ⟨79329567954619915007896277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 52886378636413276671930851 79329567954619915007896277)
                    ·
                      refine ⟨1859286748936404257997569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 79329567954619915007896277 1859286748936404257997569)
                      ·
                        rfl

theorem cell23_3620948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 3, 1, 1, 7].length) (baseStart_3620948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3620948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3620948 prefixEnd_3620948 := by exact prefixLift 3620948
  have htrace : WordTrace (prefixWord ++ tailWord_3620948) baseStart_3620948 baseEnd_3620948 := by
    simpa [prefixWord, tailWord_3620948, baseEnd_3620948] using wordTrace_append hprefix tailTrace_3620948
  have hstable : (prefixWord ++ tailWord_3620948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3620948).length < 2 ^ (prefixWord ++ tailWord_3620948).sum := by decide
  have hdescent : baseEnd_3620948 < baseStart_3620948 := by decide
  rcases family_descends (prefixWord ++ tailWord_3620948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3620995 : List Nat := [1, 1, 1, 3, 3, 3, 1, 1, 4, 2, 3]
def baseStart_3620995 : Nat := 118140960795 + 3620995 * 2 ^ 59
def prefixEnd_3620995 : Nat := 4983230072969 + 3 ^ 40 * 3620995 * 2
def baseEnd_3620995 : Nat := 1859310882527165574109853

theorem tailTrace_3620995 : CollatzResearch.WordTrace tailWord_3620995 prefixEnd_3620995 1859310882527165574109853 := by
  unfold tailWord_3620995
  simp only [CollatzResearch.WordTrace]
  refine ⟨132068537516761006556440439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88045691677840671037626959 132068537516761006556440439)
  ·
    refine ⟨198102806275141509834660659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132068537516761006556440439 198102806275141509834660659)
    ·
      refine ⟨297154209412712264751990989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198102806275141509834660659 297154209412712264751990989)
      ·
        refine ⟨111432828529767099281996621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 297154209412712264751990989 111432828529767099281996621)
        ·
          refine ⟨41787310698662662230748733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 111432828529767099281996621 41787310698662662230748733)
          ·
            refine ⟨15670241511998498336530775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41787310698662662230748733 15670241511998498336530775)
            ·
              refine ⟨23505362267997747504796163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15670241511998498336530775 23505362267997747504796163)
              ·
                refine ⟨35258043401996621257194245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23505362267997747504796163 35258043401996621257194245)
                ·
                  refine ⟨6610883137874366485723921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35258043401996621257194245 6610883137874366485723921)
                  ·
                    refine ⟨4958162353405774864292941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6610883137874366485723921 4958162353405774864292941)
                    ·
                      refine ⟨1859310882527165574109853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4958162353405774864292941 1859310882527165574109853)
                      ·
                        rfl

theorem cell23_3620995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 1, 1, 4, 2, 3].length) (baseStart_3620995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3620995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3620995 prefixEnd_3620995 := by exact prefixLift 3620995
  have htrace : WordTrace (prefixWord ++ tailWord_3620995) baseStart_3620995 baseEnd_3620995 := by
    simpa [prefixWord, tailWord_3620995, baseEnd_3620995] using wordTrace_append hprefix tailTrace_3620995
  have hstable : (prefixWord ++ tailWord_3620995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3620995).length < 2 ^ (prefixWord ++ tailWord_3620995).sum := by decide
  have hdescent : baseEnd_3620995 < baseStart_3620995 := by decide
  rcases family_descends (prefixWord ++ tailWord_3620995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3621002 : List Nat := [3, 1, 2, 3, 1, 2, 3, 1, 3, 4]
def baseStart_3621002 : Nat := 118140960795 + 3621002 * 2 ^ 59
def prefixEnd_3621002 : Nat := 4983230072969 + 3 ^ 40 * 3621002 * 2
def baseEnd_3621002 : Nat := 619771492297249015574107

theorem tailTrace_3621002 : CollatzResearch.WordTrace tailWord_3621002 prefixEnd_3621002 619771492297249015574107 := by
  unfold tailWord_3621002
  simp only [CollatzResearch.WordTrace]
  refine ⟨33017198206933911687986315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88045861885157097834630173 33017198206933911687986315)
  ·
    refine ⟨49525797310400867531979473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33017198206933911687986315 49525797310400867531979473)
    ·
      refine ⟨37144347982800650648984605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49525797310400867531979473 37144347982800650648984605)
      ·
        refine ⟨13929130493550243993369227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37144347982800650648984605 13929130493550243993369227)
        ·
          refine ⟨20893695740325365990053841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13929130493550243993369227 20893695740325365990053841)
          ·
            refine ⟨15670271805244024492540381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20893695740325365990053841 15670271805244024492540381)
            ·
              refine ⟨5876351926966509184702643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15670271805244024492540381 5876351926966509184702643)
              ·
                refine ⟨8814527890449763777053965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5876351926966509184702643 8814527890449763777053965)
                ·
                  refine ⟨3305447958918661416395237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8814527890449763777053965 3305447958918661416395237)
                  ·
                    refine ⟨619771492297249015574107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3305447958918661416395237 619771492297249015574107)
                    ·
                      rfl

theorem cell23_3621002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 3, 1, 3, 4].length) (baseStart_3621002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3621002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3621002 prefixEnd_3621002 := by exact prefixLift 3621002
  have htrace : WordTrace (prefixWord ++ tailWord_3621002) baseStart_3621002 baseEnd_3621002 := by
    simpa [prefixWord, tailWord_3621002, baseEnd_3621002] using wordTrace_append hprefix tailTrace_3621002
  have hstable : (prefixWord ++ tailWord_3621002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3621002).length < 2 ^ (prefixWord ++ tailWord_3621002).sum := by decide
  have hdescent : baseEnd_3621002 < baseStart_3621002 := by decide
  rcases family_descends (prefixWord ++ tailWord_3621002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3621035 : List Nat := [1, 1, 1, 1, 2, 1, 1, 1, 7, 5, 2]
def baseStart_3621035 : Nat := 118140960795 + 3621035 * 2 ^ 59
def prefixEnd_3621035 : Nat := 4983230072969 + 3 ^ 40 * 3621035 * 2
def baseEnd_3621035 : Nat := 1859331421753345417609669

theorem tailTrace_3621035 : CollatzResearch.WordTrace tailWord_3621035 prefixEnd_3621035 1859331421753345417609669 := by
  unfold tailWord_3621035
  simp only [CollatzResearch.WordTrace]
  refine ⟨132069996436616093387896559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88046664291077395591931039 132069996436616093387896559)
  ·
    refine ⟨198104994654924140081844839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132069996436616093387896559 198104994654924140081844839)
    ·
      refine ⟨297157491982386210122767259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198104994654924140081844839 297157491982386210122767259)
      ·
        refine ⟨445736237973579315184150889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 297157491982386210122767259 445736237973579315184150889)
        ·
          refine ⟨334302178480184486388113167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 445736237973579315184150889 334302178480184486388113167)
          ·
            refine ⟨501453267720276729582169751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 334302178480184486388113167 501453267720276729582169751)
            ·
              refine ⟨752179901580415094373254627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 501453267720276729582169751 752179901580415094373254627)
              ·
                refine ⟨1128269852370622641559881941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 752179901580415094373254627 1128269852370622641559881941)
                ·
                  refine ⟨26443824664936468161559733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1128269852370622641559881941 26443824664936468161559733)
                  ·
                    refine ⟨2479108562337793890146225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 26443824664936468161559733 2479108562337793890146225)
                    ·
                      refine ⟨1859331421753345417609669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2479108562337793890146225 1859331421753345417609669)
                      ·
                        rfl

theorem cell23_3621035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 7, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 7, 5, 2].length) (baseStart_3621035 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3621035 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3621035 prefixEnd_3621035 := by exact prefixLift 3621035
  have htrace : WordTrace (prefixWord ++ tailWord_3621035) baseStart_3621035 baseEnd_3621035 := by
    simpa [prefixWord, tailWord_3621035, baseEnd_3621035] using wordTrace_append hprefix tailTrace_3621035
  have hstable : (prefixWord ++ tailWord_3621035).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3621035).length < 2 ^ (prefixWord ++ tailWord_3621035).sum := by decide
  have hdescent : baseEnd_3621035 < baseStart_3621035 := by decide
  rcases family_descends (prefixWord ++ tailWord_3621035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3621116 : List Nat := [2, 2, 2, 1, 4, 2, 2, 1, 3, 2, 2]
def baseStart_3621116 : Nat := 118140960795 + 3621116 * 2 ^ 59
def prefixEnd_3621116 : Nat := 4983230072969 + 3 ^ 40 * 3621116 * 2
def baseEnd_3621116 : Nat := 1859373013686359600696797

theorem tailTrace_3621116 : CollatzResearch.WordTrace tailWord_3621116 prefixEnd_3621116 1859373013686359600696797 := by
  unfold tailWord_3621116
  simp only [CollatzResearch.WordTrace]
  refine ⟨66036475374661322110797601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88048633832881762814396801 66036475374661322110797601)
  ·
    refine ⟨49527356530995991583098201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66036475374661322110797601 49527356530995991583098201)
    ·
      refine ⟨37145517398246993687323651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49527356530995991583098201 37145517398246993687323651)
      ·
        refine ⟨55718276097370490530985477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37145517398246993687323651 55718276097370490530985477)
        ·
          refine ⟨10447176768256966974559777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 55718276097370490530985477 10447176768256966974559777)
          ·
            refine ⟨7835382576192725230919833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10447176768256966974559777 7835382576192725230919833)
            ·
              refine ⟨5876536932144543923189875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7835382576192725230919833 5876536932144543923189875)
              ·
                refine ⟨8814805398216815884784813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5876536932144543923189875 8814805398216815884784813)
                ·
                  refine ⟨3305552024331305956794305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8814805398216815884784813 3305552024331305956794305)
                  ·
                    refine ⟨2479164018248479467595729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3305552024331305956794305 2479164018248479467595729)
                    ·
                      refine ⟨1859373013686359600696797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2479164018248479467595729 1859373013686359600696797)
                      ·
                        rfl

theorem cell23_3621116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 2, 1, 3, 2, 2].length) (baseStart_3621116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3621116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3621116 prefixEnd_3621116 := by exact prefixLift 3621116
  have htrace : WordTrace (prefixWord ++ tailWord_3621116) baseStart_3621116 baseEnd_3621116 := by
    simpa [prefixWord, tailWord_3621116, baseEnd_3621116] using wordTrace_append hprefix tailTrace_3621116
  have hstable : (prefixWord ++ tailWord_3621116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3621116).length < 2 ^ (prefixWord ++ tailWord_3621116).sum := by decide
  have hdescent : baseEnd_3621116 < baseStart_3621116 := by decide
  rcases family_descends (prefixWord ++ tailWord_3621116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3621223 : List Nat := [1, 1, 5, 1, 3, 2, 2, 2, 2, 2, 2]
def baseStart_3621223 : Nat := 118140960795 + 3621223 * 2 ^ 59
def prefixEnd_3621223 : Nat := 4983230072969 + 3 ^ 40 * 3621223 * 2
def baseEnd_3621223 : Nat := 1859427956116390682058805

theorem tailTrace_3621223 : CollatzResearch.WordTrace tailWord_3621223 prefixEnd_3621223 1859427956116390682058805 := by
  unfold tailWord_3621223
  simp only [CollatzResearch.WordTrace]
  refine ⟨132076853359935001495740323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88051235573290000997160215 132076853359935001495740323)
  ·
    refine ⟨198115280039902502243610485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132076853359935001495740323 198115280039902502243610485)
    ·
      refine ⟨18573307503740859585338483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 198115280039902502243610485 18573307503740859585338483)
      ·
        refine ⟨27859961255611289378007725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18573307503740859585338483 27859961255611289378007725)
        ·
          refine ⟨10447485470854233516752897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27859961255611289378007725 10447485470854233516752897)
          ·
            refine ⟨7835614103140675137564673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10447485470854233516752897 7835614103140675137564673)
            ·
              refine ⟨5876710577355506353173505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7835614103140675137564673 5876710577355506353173505)
              ·
                refine ⟨4407532933016629764880129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5876710577355506353173505 4407532933016629764880129)
                ·
                  refine ⟨3305649699762472323660097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4407532933016629764880129 3305649699762472323660097)
                  ·
                    refine ⟨2479237274821854242745073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3305649699762472323660097 2479237274821854242745073)
                    ·
                      refine ⟨1859427956116390682058805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2479237274821854242745073 1859427956116390682058805)
                      ·
                        rfl

theorem cell23_3621223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 2, 2, 2, 2, 2].length) (baseStart_3621223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3621223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3621223 prefixEnd_3621223 := by exact prefixLift 3621223
  have htrace : WordTrace (prefixWord ++ tailWord_3621223) baseStart_3621223 baseEnd_3621223 := by
    simpa [prefixWord, tailWord_3621223, baseEnd_3621223] using wordTrace_append hprefix tailTrace_3621223
  have hstable : (prefixWord ++ tailWord_3621223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3621223).length < 2 ^ (prefixWord ++ tailWord_3621223).sum := by decide
  have hdescent : baseEnd_3621223 < baseStart_3621223 := by decide
  rcases family_descends (prefixWord ++ tailWord_3621223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3621229 : List Nat := [1, 5, 1, 1, 1, 2, 3, 4, 5]
def baseStart_3621229 : Nat := 118140960795 + 3621229 * 2 ^ 59
def prefixEnd_3621229 : Nat := 4983230072969 + 3 ^ 40 * 3621229 * 2
def baseEnd_3621229 : Nat := 206603448555590850953753

theorem tailTrace_3621229 : CollatzResearch.WordTrace tailWord_3621229 prefixEnd_3621229 206603448555590850953753 := by
  unfold tailWord_3621229
  simp only [CollatzResearch.WordTrace]
  refine ⟨132077072197913264520458741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88051381465275509680305827 132077072197913264520458741)
  ·
    refine ⟨12382225518554368548793007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 132077072197913264520458741 12382225518554368548793007)
    ·
      refine ⟨18573338277831552823189511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12382225518554368548793007 18573338277831552823189511)
      ·
        refine ⟨27860007416747329234784267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18573338277831552823189511 27860007416747329234784267)
        ·
          refine ⟨41790011125120993852176401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27860007416747329234784267 41790011125120993852176401)
          ·
            refine ⟨31342508343840745389132301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41790011125120993852176401 31342508343840745389132301)
            ·
              refine ⟨11753440628940279520924613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31342508343840745389132301 11753440628940279520924613)
              ·
                refine ⟨2203770117926302410173365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11753440628940279520924613 2203770117926302410173365)
                ·
                  refine ⟨206603448555590850953753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2203770117926302410173365 206603448555590850953753)
                  ·
                    rfl

theorem cell23_3621229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 3, 4, 5].length) (baseStart_3621229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3621229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3621229 prefixEnd_3621229 := by exact prefixLift 3621229
  have htrace : WordTrace (prefixWord ++ tailWord_3621229) baseStart_3621229 baseEnd_3621229 := by
    simpa [prefixWord, tailWord_3621229, baseEnd_3621229] using wordTrace_append hprefix tailTrace_3621229
  have hstable : (prefixWord ++ tailWord_3621229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3621229).length < 2 ^ (prefixWord ++ tailWord_3621229).sum := by decide
  have hdescent : baseEnd_3621229 < baseStart_3621229 := by decide
  rcases family_descends (prefixWord ++ tailWord_3621229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3621259 : List Nat := [1, 1, 1, 1, 4, 6, 1, 1, 2, 5]
def baseStart_3621259 : Nat := 118140960795 + 3621259 * 2 ^ 59
def prefixEnd_3621259 : Nat := 4983230072969 + 3 ^ 40 * 3621259 * 2
def baseEnd_3621259 : Nat := 619815480473317513736213

theorem tailTrace_3621259 : CollatzResearch.WordTrace tailWord_3621259 prefixEnd_3621259 619815480473317513736213 := by
  unfold tailWord_3621259
  simp only [CollatzResearch.WordTrace]
  refine ⟨132078166387804579644050831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88052110925203053096033887 132078166387804579644050831)
  ·
    refine ⟨198117249581706869466076247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132078166387804579644050831 198117249581706869466076247)
    ·
      refine ⟨297175874372560304199114371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198117249581706869466076247 297175874372560304199114371)
      ·
        refine ⟨445763811558840456298671557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 297175874372560304199114371 445763811558840456298671557)
        ·
          refine ⟨83580714667282585556000917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 445763811558840456298671557 83580714667282585556000917)
          ·
            refine ⟨3917846000028871197937543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 83580714667282585556000917 3917846000028871197937543)
            ·
              refine ⟨5876769000043306796906315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3917846000028871197937543 5876769000043306796906315)
              ·
                refine ⟨8815153500064960195359473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5876769000043306796906315 8815153500064960195359473)
                ·
                  refine ⟨6611365125048720146519605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8815153500064960195359473 6611365125048720146519605)
                  ·
                    refine ⟨619815480473317513736213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6611365125048720146519605 619815480473317513736213)
                    ·
                      rfl

theorem cell23_3621259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 6, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 6, 1, 1, 2, 5].length) (baseStart_3621259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3621259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3621259 prefixEnd_3621259 := by exact prefixLift 3621259
  have htrace : WordTrace (prefixWord ++ tailWord_3621259) baseStart_3621259 baseEnd_3621259 := by
    simpa [prefixWord, tailWord_3621259, baseEnd_3621259] using wordTrace_append hprefix tailTrace_3621259
  have hstable : (prefixWord ++ tailWord_3621259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3621259).length < 2 ^ (prefixWord ++ tailWord_3621259).sum := by decide
  have hdescent : baseEnd_3621259 < baseStart_3621259 := by decide
  rcases family_descends (prefixWord ++ tailWord_3621259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3621265 : List Nat := [1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 9]
def baseStart_3621265 : Nat := 118140960795 + 3621265 * 2 ^ 59
def prefixEnd_3621265 : Nat := 4983230072969 + 3 ^ 40 * 3621265 * 2
def baseEnd_3621265 : Nat := 1859449522303879517733611

theorem tailTrace_3621265 : CollatzResearch.WordTrace tailWord_3621265 prefixEnd_3621265 1859449522303879517733611 := by
  unfold tailWord_3621265
  simp only [CollatzResearch.WordTrace]
  refine ⟨132078385225782842668769249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88052256817188561779179499 132078385225782842668769249)
  ·
    refine ⟨99058788919337132001576937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132078385225782842668769249 99058788919337132001576937)
    ·
      refine ⟨74294091689502849001182703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99058788919337132001576937 74294091689502849001182703)
      ·
        refine ⟨111441137534254273501774055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74294091689502849001182703 111441137534254273501774055)
        ·
          refine ⟨167161706301381410252661083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111441137534254273501774055 167161706301381410252661083)
          ·
            refine ⟨250742559452072115378991625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 167161706301381410252661083 250742559452072115378991625)
            ·
              refine ⟨188056919589054086534243719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 250742559452072115378991625 188056919589054086534243719)
              ·
                refine ⟨282085379383581129801365579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 188056919589054086534243719 282085379383581129801365579)
                ·
                  refine ⟨423128069075371694702048369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 282085379383581129801365579 423128069075371694702048369)
                  ·
                    refine ⟨317346051806528771026536277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 423128069075371694702048369 317346051806528771026536277)
                    ·
                      refine ⟨1859449522303879517733611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 317346051806528771026536277 1859449522303879517733611)
                      ·
                        rfl

theorem cell23_3621265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 9].length) (baseStart_3621265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3621265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3621265 prefixEnd_3621265 := by exact prefixLift 3621265
  have htrace : WordTrace (prefixWord ++ tailWord_3621265) baseStart_3621265 baseEnd_3621265 := by
    simpa [prefixWord, tailWord_3621265, baseEnd_3621265] using wordTrace_append hprefix tailTrace_3621265
  have hstable : (prefixWord ++ tailWord_3621265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3621265).length < 2 ^ (prefixWord ++ tailWord_3621265).sum := by decide
  have hdescent : baseEnd_3621265 < baseStart_3621265 := by decide
  rcases family_descends (prefixWord ++ tailWord_3621265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3621279 : List Nat := [1, 1, 2, 5, 1, 1, 1, 1, 4, 4, 2]
def baseStart_3621279 : Nat := 118140960795 + 3621279 * 2 ^ 59
def prefixEnd_3621279 : Nat := 4983230072969 + 3 ^ 40 * 3621279 * 2
def baseEnd_3621279 : Nat := 1859456711033042462958547

theorem tailTrace_3621279 : CollatzResearch.WordTrace tailWord_3621279 prefixEnd_3621279 1859456711033042462958547 := by
  unfold tailWord_3621279
  simp only [CollatzResearch.WordTrace]
  refine ⟨132078895847732123059778891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88052597231821415373185927 132078895847732123059778891)
  ·
    refine ⟨198118343771598184589668337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132078895847732123059778891 198118343771598184589668337)
    ·
      refine ⟨148588757828698638442251253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 198118343771598184589668337 148588757828698638442251253)
      ·
        refine ⟨13930196046440497353961055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 148588757828698638442251253 13930196046440497353961055)
        ·
          refine ⟨20895294069660746030941583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13930196046440497353961055 20895294069660746030941583)
          ·
            refine ⟨31342941104491119046412375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20895294069660746030941583 31342941104491119046412375)
            ·
              refine ⟨47014411656736678569618563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31342941104491119046412375 47014411656736678569618563)
              ·
                refine ⟨70521617485105017854427845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47014411656736678569618563 70521617485105017854427845)
                ·
                  refine ⟨13222803278457190847705221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 70521617485105017854427845 13222803278457190847705221)
                  ·
                    refine ⟨2479275614710723283944729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13222803278457190847705221 2479275614710723283944729)
                    ·
                      refine ⟨1859456711033042462958547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2479275614710723283944729 1859456711033042462958547)
                      ·
                        rfl

theorem cell23_3621279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 1, 4, 4, 2].length) (baseStart_3621279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3621279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3621279 prefixEnd_3621279 := by exact prefixLift 3621279
  have htrace : WordTrace (prefixWord ++ tailWord_3621279) baseStart_3621279 baseEnd_3621279 := by
    simpa [prefixWord, tailWord_3621279, baseEnd_3621279] using wordTrace_append hprefix tailTrace_3621279
  have hstable : (prefixWord ++ tailWord_3621279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3621279).length < 2 ^ (prefixWord ++ tailWord_3621279).sum := by decide
  have hdescent : baseEnd_3621279 < baseStart_3621279 := by decide
  rcases family_descends (prefixWord ++ tailWord_3621279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3621312 : List Nat := [2, 1, 1, 2, 3, 1, 1, 1, 1, 7, 3]
def baseStart_3621312 : Nat := 118140960795 + 3621312 * 2 ^ 59
def prefixEnd_3621312 : Nat := 4983230072969 + 3 ^ 40 * 3621312 * 2
def baseEnd_3621312 : Nat := 1859473655894640833845895

theorem tailTrace_3621312 : CollatzResearch.WordTrace tailWord_3621312 prefixEnd_3621312 1859473655894640833845895 := by
  unfold tailWord_3621312
  simp only [CollatzResearch.WordTrace]
  refine ⟨66040049728306284847865095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88053399637741713130486793 66040049728306284847865095)
  ·
    refine ⟨99060074592459427271797643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66040049728306284847865095 99060074592459427271797643)
    ·
      refine ⟨148590111888689140907696465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99060074592459427271797643 148590111888689140907696465)
      ·
        refine ⟨111442583916516855680772349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 148590111888689140907696465 111442583916516855680772349)
        ·
          refine ⟨41790968968693820880289631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 111442583916516855680772349 41790968968693820880289631)
          ·
            refine ⟨62686453453040731320434447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41790968968693820880289631 62686453453040731320434447)
            ·
              refine ⟨94029680179561096980651671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62686453453040731320434447 94029680179561096980651671)
              ·
                refine ⟨141044520269341645470977507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 94029680179561096980651671 141044520269341645470977507)
                ·
                  refine ⟨211566780404012468206466261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 141044520269341645470977507 211566780404012468206466261)
                  ·
                    refine ⟨4958596415719042223589053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 211566780404012468206466261 4958596415719042223589053)
                    ·
                      refine ⟨1859473655894640833845895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4958596415719042223589053 1859473655894640833845895)
                      ·
                        rfl

theorem cell23_3621312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 1, 1, 7, 3].length) (baseStart_3621312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3621312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3621312 prefixEnd_3621312 := by exact prefixLift 3621312
  have htrace : WordTrace (prefixWord ++ tailWord_3621312) baseStart_3621312 baseEnd_3621312 := by
    simpa [prefixWord, tailWord_3621312, baseEnd_3621312] using wordTrace_append hprefix tailTrace_3621312
  have hstable : (prefixWord ++ tailWord_3621312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3621312).length < 2 ^ (prefixWord ++ tailWord_3621312).sum := by decide
  have hdescent : baseEnd_3621312 < baseStart_3621312 := by decide
  rcases family_descends (prefixWord ++ tailWord_3621312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3621329 : List Nat := [1, 2, 2, 1, 2, 1, 1, 4, 5, 1, 3]
def baseStart_3621329 : Nat := 118140960795 + 3621329 * 2 ^ 59
def prefixEnd_3621329 : Nat := 4983230072969 + 3 ^ 40 * 3621329 * 2
def baseEnd_3621329 : Nat := 1859482385065767267333317

theorem tailTrace_3621329 : CollatzResearch.WordTrace tailWord_3621329 prefixEnd_3621329 1859482385065767267333317 := by
  unfold tailWord_3621329
  simp only [CollatzResearch.WordTrace]
  refine ⟨132080719497550981599099041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88053812998367321066066027 132080719497550981599099041)
  ·
    refine ⟨99060539623163236199324281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132080719497550981599099041 99060539623163236199324281)
    ·
      refine ⟨74295404717372427149493211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99060539623163236199324281 74295404717372427149493211)
      ·
        refine ⟨111443107076058640724239817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74295404717372427149493211 111443107076058640724239817)
        ·
          refine ⟨83582330307043980543179863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 111443107076058640724239817 83582330307043980543179863)
          ·
            refine ⟨125373495460565970814769795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83582330307043980543179863 125373495460565970814769795)
            ·
              refine ⟨188060243190848956222154693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 125373495460565970814769795 188060243190848956222154693)
              ·
                refine ⟨35261295598284179291654005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 188060243190848956222154693 35261295598284179291654005)
                ·
                  refine ⟨3305746462339141808592563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 35261295598284179291654005 3305746462339141808592563)
                  ·
                    refine ⟨4958619693508712712888845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3305746462339141808592563 4958619693508712712888845)
                    ·
                      refine ⟨1859482385065767267333317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4958619693508712712888845 1859482385065767267333317)
                      ·
                        rfl

theorem cell23_3621329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 4, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 4, 5, 1, 3].length) (baseStart_3621329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3621329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3621329 prefixEnd_3621329 := by exact prefixLift 3621329
  have htrace : WordTrace (prefixWord ++ tailWord_3621329) baseStart_3621329 baseEnd_3621329 := by
    simpa [prefixWord, tailWord_3621329, baseEnd_3621329] using wordTrace_append hprefix tailTrace_3621329
  have hstable : (prefixWord ++ tailWord_3621329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3621329).length < 2 ^ (prefixWord ++ tailWord_3621329).sum := by decide
  have hdescent : baseEnd_3621329 < baseStart_3621329 := by decide
  rcases family_descends (prefixWord ++ tailWord_3621329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3621369 : List Nat := [1, 2, 1, 3, 1, 2, 2, 1, 2, 6, 2]
def baseStart_3621369 : Nat := 118140960795 + 3621369 * 2 ^ 59
def prefixEnd_3621369 : Nat := 4983230072969 + 3 ^ 40 * 3621369 * 2
def baseEnd_3621369 : Nat := 1859502924291947110833133

theorem tailTrace_3621369 : CollatzResearch.WordTrace tailWord_3621369 prefixEnd_3621369 1859502924291947110833133 := by
  unfold tailWord_3621369
  simp only [CollatzResearch.WordTrace]
  refine ⟨132082178417406068430555161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88054785611604045620370107 132082178417406068430555161)
  ·
    refine ⟨99061633813054551322916371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132082178417406068430555161 99061633813054551322916371)
    ·
      refine ⟨148592450719581826984374557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99061633813054551322916371 148592450719581826984374557)
      ·
        refine ⟨55722169019843185119140459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 148592450719581826984374557 55722169019843185119140459)
        ·
          refine ⟨83583253529764777678710689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55722169019843185119140459 83583253529764777678710689)
          ·
            refine ⟨62687440147323583259033017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83583253529764777678710689 62687440147323583259033017)
            ·
              refine ⟨47015580110492687444274763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62687440147323583259033017 47015580110492687444274763)
              ·
                refine ⟨70523370165739031166412145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47015580110492687444274763 70523370165739031166412145)
                ·
                  refine ⟨52892527624304273374809109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 70523370165739031166412145 52892527624304273374809109)
                  ·
                    refine ⟨2479337232389262814444177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 52892527624304273374809109 2479337232389262814444177)
                    ·
                      refine ⟨1859502924291947110833133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2479337232389262814444177 1859502924291947110833133)
                      ·
                        rfl

theorem cell23_3621369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 1, 2, 6, 2].length) (baseStart_3621369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3621369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3621369 prefixEnd_3621369 := by exact prefixLift 3621369
  have htrace : WordTrace (prefixWord ++ tailWord_3621369) baseStart_3621369 baseEnd_3621369 := by
    simpa [prefixWord, tailWord_3621369, baseEnd_3621369] using wordTrace_append hprefix tailTrace_3621369
  have hstable : (prefixWord ++ tailWord_3621369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3621369).length < 2 ^ (prefixWord ++ tailWord_3621369).sum := by decide
  have hdescent : baseEnd_3621369 < baseStart_3621369 := by decide
  rcases family_descends (prefixWord ++ tailWord_3621369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3621383 : List Nat := [1, 1, 4, 3, 3, 1, 3, 1, 1, 5]
def baseStart_3621383 : Nat := 118140960795 + 3621383 * 2 ^ 59
def prefixEnd_3621383 : Nat := 4983230072969 + 3 ^ 40 * 3621383 * 2
def baseEnd_3621383 : Nat := 619836704340370018686023

theorem tailTrace_3621383 : CollatzResearch.WordTrace tailWord_3621383 prefixEnd_3621383 619836704340370018686023 := by
  unfold tailWord_3621383
  simp only [CollatzResearch.WordTrace]
  refine ⟨132082689039355348821564803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88055126026236899214376535 132082689039355348821564803)
  ·
    refine ⟨198124033559033023232347205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132082689039355348821564803 198124033559033023232347205)
    ·
      refine ⟨37148256292318691856065101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 198124033559033023232347205 37148256292318691856065101)
      ·
        refine ⟨13930596109619509446024413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37148256292318691856065101 13930596109619509446024413)
        ·
          refine ⟨5223973541107316042259155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13930596109619509446024413 5223973541107316042259155)
          ·
            refine ⟨7835960311660974063388733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5223973541107316042259155 7835960311660974063388733)
            ·
              refine ⟨2938485116872865273770775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7835960311660974063388733 2938485116872865273770775)
              ·
                refine ⟨4407727675309297910656163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2938485116872865273770775 4407727675309297910656163)
                ·
                  refine ⟨6611591512963946865984245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4407727675309297910656163 6611591512963946865984245)
                  ·
                    refine ⟨619836704340370018686023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6611591512963946865984245 619836704340370018686023)
                    ·
                      rfl

theorem cell23_3621383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 3, 1, 1, 5].length) (baseStart_3621383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3621383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3621383 prefixEnd_3621383 := by exact prefixLift 3621383
  have htrace : WordTrace (prefixWord ++ tailWord_3621383) baseStart_3621383 baseEnd_3621383 := by
    simpa [prefixWord, tailWord_3621383, baseEnd_3621383] using wordTrace_append hprefix tailTrace_3621383
  have hstable : (prefixWord ++ tailWord_3621383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3621383).length < 2 ^ (prefixWord ++ tailWord_3621383).sum := by decide
  have hdescent : baseEnd_3621383 < baseStart_3621383 := by decide
  rcases family_descends (prefixWord ++ tailWord_3621383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3621416 : List Nat := [2, 1, 5, 2, 1, 1, 1, 3, 1, 2, 4]
def baseStart_3621416 : Nat := 118140960795 + 3621416 * 2 ^ 59
def prefixEnd_3621416 : Nat := 4983230072969 + 3 ^ 40 * 3621416 * 2
def baseEnd_3621416 : Nat := 1859527057882708426945417

theorem tailTrace_3621416 : CollatzResearch.WordTrace tailWord_3621416 prefixEnd_3621416 1859527057882708426945417 := by
  unfold tailWord_3621416
  simp only [CollatzResearch.WordTrace]
  refine ⟨66041946324117897728758051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88055928432157196971677401 66041946324117897728758051)
  ·
    refine ⟨99062919486176846593137077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66041946324117897728758051 99062919486176846593137077)
    ·
      refine ⟨9287148701829079368106601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 99062919486176846593137077 9287148701829079368106601)
      ·
        refine ⟨6965361526371809526079951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9287148701829079368106601 6965361526371809526079951)
        ·
          refine ⟨10448042289557714289119927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6965361526371809526079951 10448042289557714289119927)
          ·
            refine ⟨15672063434336571433679891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10448042289557714289119927 15672063434336571433679891)
            ·
              refine ⟨23508095151504857150519837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15672063434336571433679891 23508095151504857150519837)
              ·
                refine ⟨8815535681814321431444939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23508095151504857150519837 8815535681814321431444939)
                ·
                  refine ⟨13223303522721482147167409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8815535681814321431444939 13223303522721482147167409)
                  ·
                    refine ⟨9917477642041111610375557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13223303522721482147167409 9917477642041111610375557)
                    ·
                      refine ⟨1859527057882708426945417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9917477642041111610375557 1859527057882708426945417)
                      ·
                        rfl

theorem cell23_3621416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 1, 3, 1, 2, 4].length) (baseStart_3621416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3621416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3621416 prefixEnd_3621416 := by exact prefixLift 3621416
  have htrace : WordTrace (prefixWord ++ tailWord_3621416) baseStart_3621416 baseEnd_3621416 := by
    simpa [prefixWord, tailWord_3621416, baseEnd_3621416] using wordTrace_append hprefix tailTrace_3621416
  have hstable : (prefixWord ++ tailWord_3621416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3621416).length < 2 ^ (prefixWord ++ tailWord_3621416).sum := by decide
  have hdescent : baseEnd_3621416 < baseStart_3621416 := by decide
  rcases family_descends (prefixWord ++ tailWord_3621416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3621436 : List Nat := [2, 2, 2, 2, 3, 1, 2, 2, 1, 3, 3]
def baseStart_3621436 : Nat := 118140960795 + 3621436 * 2 ^ 59
def prefixEnd_3621436 : Nat := 4983230072969 + 3 ^ 40 * 3621436 * 2
def baseEnd_3621436 : Nat := 1859537327495798348695325

theorem tailTrace_3621436 : CollatzResearch.WordTrace tailWord_3621436 prefixEnd_3621436 1859537327495798348695325 := by
  unfold tailWord_3621436
  simp only [CollatzResearch.WordTrace]
  refine ⟨66042311054081669436622081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88056414738775559248829441 66042311054081669436622081)
  ·
    refine ⟨49531733290561252077466561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66042311054081669436622081 49531733290561252077466561)
    ·
      refine ⟨37148799967920939058099921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49531733290561252077466561 37148799967920939058099921)
      ·
        refine ⟨27861599975940704293574941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37148799967920939058099921 27861599975940704293574941)
        ·
          refine ⟨10448099990977764110090603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27861599975940704293574941 10448099990977764110090603)
          ·
            refine ⟨15672149986466646165135905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10448099990977764110090603 15672149986466646165135905)
            ·
              refine ⟨11754112489849984623851929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15672149986466646165135905 11754112489849984623851929)
              ·
                refine ⟨8815584367387488467888947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11754112489849984623851929 8815584367387488467888947)
                ·
                  refine ⟨13223376551081232701833421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8815584367387488467888947 13223376551081232701833421)
                  ·
                    refine ⟨4958766206655462263187533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13223376551081232701833421 4958766206655462263187533)
                    ·
                      refine ⟨1859537327495798348695325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4958766206655462263187533 1859537327495798348695325)
                      ·
                        rfl

theorem cell23_3621436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 2, 2, 1, 3, 3].length) (baseStart_3621436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3621436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3621436 prefixEnd_3621436 := by exact prefixLift 3621436
  have htrace : WordTrace (prefixWord ++ tailWord_3621436) baseStart_3621436 baseEnd_3621436 := by
    simpa [prefixWord, tailWord_3621436, baseEnd_3621436] using wordTrace_append hprefix tailTrace_3621436
  have hstable : (prefixWord ++ tailWord_3621436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3621436).length < 2 ^ (prefixWord ++ tailWord_3621436).sum := by decide
  have hdescent : baseEnd_3621436 < baseStart_3621436 := by decide
  rcases family_descends (prefixWord ++ tailWord_3621436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3621437 : List Nat := [1, 4, 1, 3, 2, 2, 2, 3, 1, 2, 2]
def baseStart_3621437 : Nat := 118140960795 + 3621437 * 2 ^ 59
def prefixEnd_3621437 : Nat := 4983230072969 + 3 ^ 40 * 3621437 * 2
def baseEnd_3621437 : Nat := 1859537840976452844782821

theorem tailTrace_3621437 : CollatzResearch.WordTrace tailWord_3621437 prefixEnd_3621437 1859537840976452844782821 := by
  unfold tailWord_3621437
  simp only [CollatzResearch.WordTrace]
  refine ⟨132084658581159716044030565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88056439054106477362687043 132084658581159716044030565)
  ·
    refine ⟨24765873483967446758255731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 132084658581159716044030565 24765873483967446758255731)
    ·
      refine ⟨37148810225951170137383597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24765873483967446758255731 37148810225951170137383597)
      ·
        refine ⟨13930803834731688801518849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37148810225951170137383597 13930803834731688801518849)
        ·
          refine ⟨10448102876048766601139137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13930803834731688801518849 10448102876048766601139137)
          ·
            refine ⟨7836077157036574950854353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10448102876048766601139137 7836077157036574950854353)
            ·
              refine ⟨5877057867777431213140765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7836077157036574950854353 5877057867777431213140765)
              ·
                refine ⟨2203896700416536704927787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5877057867777431213140765 2203896700416536704927787)
                ·
                  refine ⟨3305845050624805057391681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2203896700416536704927787 3305845050624805057391681)
                  ·
                    refine ⟨2479383787968603793043761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3305845050624805057391681 2479383787968603793043761)
                    ·
                      refine ⟨1859537840976452844782821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2479383787968603793043761 1859537840976452844782821)
                      ·
                        rfl

theorem cell23_3621437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 2, 3, 1, 2, 2].length) (baseStart_3621437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3621437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3621437 prefixEnd_3621437 := by exact prefixLift 3621437
  have htrace : WordTrace (prefixWord ++ tailWord_3621437) baseStart_3621437 baseEnd_3621437 := by
    simpa [prefixWord, tailWord_3621437, baseEnd_3621437] using wordTrace_append hprefix tailTrace_3621437
  have hstable : (prefixWord ++ tailWord_3621437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3621437).length < 2 ^ (prefixWord ++ tailWord_3621437).sum := by decide
  have hdescent : baseEnd_3621437 < baseStart_3621437 := by decide
  rcases family_descends (prefixWord ++ tailWord_3621437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3621479 : List Nat := [1, 1, 5, 1, 1, 1, 1, 4, 2, 1, 5]
def baseStart_3621479 : Nat := 118140960795 + 3621479 * 2 ^ 59
def prefixEnd_3621479 : Nat := 4983230072969 + 3 ^ 40 * 3621479 * 2
def baseEnd_3621479 : Nat := 1859559407163941680457627

theorem tailTrace_3621479 : CollatzResearch.WordTrace tailWord_3621479 prefixEnd_3621479 1859559407163941680457627 := by
  unfold tailWord_3621479
  simp only [CollatzResearch.WordTrace]
  refine ⟨132086190447007557217059491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88057460298005038144706327 132086190447007557217059491)
  ·
    refine ⟨198129285670511335825589237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132086190447007557217059491 198129285670511335825589237)
    ·
      refine ⟨18574620531610437733648991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 198129285670511335825589237 18574620531610437733648991)
      ·
        refine ⟨27861930797415656600473487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18574620531610437733648991 27861930797415656600473487)
        ·
          refine ⟨41792896196123484900710231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27861930797415656600473487 41792896196123484900710231)
          ·
            refine ⟨62689344294185227351065347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41792896196123484900710231 62689344294185227351065347)
            ·
              refine ⟨94034016441277841026598021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62689344294185227351065347 94034016441277841026598021)
              ·
                refine ⟨17631378082739595192487129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 94034016441277841026598021 17631378082739595192487129)
                ·
                  refine ⟨13223533562054696394365347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17631378082739595192487129 13223533562054696394365347)
                  ·
                    refine ⟨19835300343082044591548021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13223533562054696394365347 19835300343082044591548021)
                    ·
                      refine ⟨1859559407163941680457627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19835300343082044591548021 1859559407163941680457627)
                      ·
                        rfl

theorem cell23_3621479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 4, 2, 1, 5].length) (baseStart_3621479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3621479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3621479 prefixEnd_3621479 := by exact prefixLift 3621479
  have htrace : WordTrace (prefixWord ++ tailWord_3621479) baseStart_3621479 baseEnd_3621479 := by
    simpa [prefixWord, tailWord_3621479, baseEnd_3621479] using wordTrace_append hprefix tailTrace_3621479
  have hstable : (prefixWord ++ tailWord_3621479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3621479).length < 2 ^ (prefixWord ++ tailWord_3621479).sum := by decide
  have hdescent : baseEnd_3621479 < baseStart_3621479 := by decide
  rcases family_descends (prefixWord ++ tailWord_3621479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3621529 : List Nat := [1, 2, 1, 2, 1, 2, 3, 2, 4, 5]
def baseStart_3621529 : Nat := 118140960795 + 3621529 * 2 ^ 59
def prefixEnd_3621529 : Nat := 4983230072969 + 3 ^ 40 * 3621529 * 2
def baseEnd_3621529 : Nat := 619861693732222161610799

theorem tailTrace_3621529 : CollatzResearch.WordTrace tailWord_3621529 prefixEnd_3621529 619861693732222161610799 := by
  unfold tailWord_3621529
  simp only [CollatzResearch.WordTrace]
  refine ⟨132088014096826415756379641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88058676064550943837586427 132088014096826415756379641)
  ·
    refine ⟨99066010572619811817284731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132088014096826415756379641 99066010572619811817284731)
    ·
      refine ⟨148599015858929717725927097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99066010572619811817284731 148599015858929717725927097)
      ·
        refine ⟨111449261894197288294445323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 148599015858929717725927097 111449261894197288294445323)
        ·
          refine ⟨167173892841295932441667985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111449261894197288294445323 167173892841295932441667985)
          ·
            refine ⟨125380419630971949331250989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 167173892841295932441667985 125380419630971949331250989)
            ·
              refine ⟨47017657361614480999219121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 125380419630971949331250989 47017657361614480999219121)
              ·
                refine ⟨35263243021210860749414341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47017657361614480999219121 35263243021210860749414341)
                ·
                  refine ⟨6611858066477036390515189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35263243021210860749414341 6611858066477036390515189)
                  ·
                    refine ⟨619861693732222161610799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6611858066477036390515189 619861693732222161610799)
                    ·
                      rfl

theorem cell23_3621529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 2, 4, 5].length) (baseStart_3621529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3621529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3621529 prefixEnd_3621529 := by exact prefixLift 3621529
  have htrace : WordTrace (prefixWord ++ tailWord_3621529) baseStart_3621529 baseEnd_3621529 := by
    simpa [prefixWord, tailWord_3621529, baseEnd_3621529] using wordTrace_append hprefix tailTrace_3621529
  have hstable : (prefixWord ++ tailWord_3621529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3621529).length < 2 ^ (prefixWord ++ tailWord_3621529).sum := by decide
  have hdescent : baseEnd_3621529 < baseStart_3621529 := by decide
  rcases family_descends (prefixWord ++ tailWord_3621529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3621579 : List Nat := [1, 1, 1, 1, 3, 2, 1, 1, 4, 4, 4]
def baseStart_3621579 : Nat := 118140960795 + 3621579 * 2 ^ 59
def prefixEnd_3621579 : Nat := 4983230072969 + 3 ^ 40 * 3621579 * 2
def baseEnd_3621579 : Nat := 1859610755229391289207167

theorem tailTrace_3621579 : CollatzResearch.WordTrace tailWord_3621579 prefixEnd_3621579 1859610755229391289207167 := by
  unfold tailWord_3621579
  simp only [CollatzResearch.WordTrace]
  refine ⟨132089837746645274295699791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88059891831096849530466527 132089837746645274295699791)
  ·
    refine ⟨198134756619967911443549687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132089837746645274295699791 198134756619967911443549687)
    ·
      refine ⟨297202134929951867165324531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198134756619967911443549687 297202134929951867165324531)
      ·
        refine ⟨445803202394927800747986797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 297202134929951867165324531 445803202394927800747986797)
        ·
          refine ⟨167176200898097925280495049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 445803202394927800747986797 167176200898097925280495049)
          ·
            refine ⟨125382150673573443960371287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 167176200898097925280495049 125382150673573443960371287)
            ·
              refine ⟨188073226010360165940556931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 125382150673573443960371287 188073226010360165940556931)
              ·
                refine ⟨282109839015540248910835397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 188073226010360165940556931 282109839015540248910835397)
                ·
                  refine ⟨52895594815413796670781637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 282109839015540248910835397 52895594815413796670781637)
                  ·
                    refine ⟨9917924027890086875771557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 52895594815413796670781637 9917924027890086875771557)
                    ·
                      refine ⟨1859610755229391289207167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9917924027890086875771557 1859610755229391289207167)
                      ·
                        rfl

theorem cell23_3621579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 1, 4, 4, 4].length) (baseStart_3621579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3621579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3621579 prefixEnd_3621579 := by exact prefixLift 3621579
  have htrace : WordTrace (prefixWord ++ tailWord_3621579) baseStart_3621579 baseEnd_3621579 := by
    simpa [prefixWord, tailWord_3621579, baseEnd_3621579] using wordTrace_append hprefix tailTrace_3621579
  have hstable : (prefixWord ++ tailWord_3621579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3621579).length < 2 ^ (prefixWord ++ tailWord_3621579).sum := by decide
  have hdescent : baseEnd_3621579 < baseStart_3621579 := by decide
  rcases family_descends (prefixWord ++ tailWord_3621579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3621603 : List Nat := [1, 1, 1, 7, 1, 2, 1, 1, 1, 4, 3]
def baseStart_3621603 : Nat := 118140960795 + 3621603 * 2 ^ 59
def prefixEnd_3621603 : Nat := 4983230072969 + 3 ^ 40 * 3621603 * 2
def baseEnd_3621603 : Nat := 1859623078765099195307057

theorem tailTrace_3621603 : CollatzResearch.WordTrace tailWord_3621603 prefixEnd_3621603 1859623078765099195307057 := by
  unfold tailWord_3621603
  simp only [CollatzResearch.WordTrace]
  refine ⟨132090713098558326394573463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88060475399038884263048975 132090713098558326394573463)
  ·
    refine ⟨198136069647837489591860195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132090713098558326394573463 198136069647837489591860195)
    ·
      refine ⟨297204104471756234387790293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198136069647837489591860195 297204104471756234387790293)
      ·
        refine ⟨6965721198556786743463835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 297204104471756234387790293 6965721198556786743463835)
        ·
          refine ⟨10448581797835180115195753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6965721198556786743463835 10448581797835180115195753)
          ·
            refine ⟨7836436348376385086396815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10448581797835180115195753 7836436348376385086396815)
            ·
              refine ⟨11754654522564577629595223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7836436348376385086396815 11754654522564577629595223)
              ·
                refine ⟨17631981783846866444392835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11754654522564577629595223 17631981783846866444392835)
                ·
                  refine ⟨26447972675770299666589253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17631981783846866444392835 26447972675770299666589253)
                  ·
                    refine ⟨4958994876706931187485485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26447972675770299666589253 4958994876706931187485485)
                    ·
                      refine ⟨1859623078765099195307057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4958994876706931187485485 1859623078765099195307057)
                      ·
                        rfl

theorem cell23_3621603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 1, 1, 1, 4, 3].length) (baseStart_3621603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3621603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3621603 prefixEnd_3621603 := by exact prefixLift 3621603
  have htrace : WordTrace (prefixWord ++ tailWord_3621603) baseStart_3621603 baseEnd_3621603 := by
    simpa [prefixWord, tailWord_3621603, baseEnd_3621603] using wordTrace_append hprefix tailTrace_3621603
  have hstable : (prefixWord ++ tailWord_3621603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3621603).length < 2 ^ (prefixWord ++ tailWord_3621603).sum := by decide
  have hdescent : baseEnd_3621603 < baseStart_3621603 := by decide
  rcases family_descends (prefixWord ++ tailWord_3621603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3621653 : List Nat := [1, 3, 2, 1, 2, 2, 4, 2, 1, 5]
def baseStart_3621653 : Nat := 118140960795 + 3621653 * 2 ^ 59
def prefixEnd_3621653 : Nat := 4983230072969 + 3 ^ 40 * 3621653 * 2
def baseEnd_3621653 : Nat := 619882917599274666560609

theorem tailTrace_3621653 : CollatzResearch.WordTrace tailWord_3621653 prefixEnd_3621653 619882917599274666560609 := by
  unfold tailWord_3621653
  simp only [CollatzResearch.WordTrace]
  refine ⟨132092536748377184933893613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88061691165584789955929075 132092536748377184933893613)
  ·
    refine ⟨49534701280641444350210105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 132092536748377184933893613 49534701280641444350210105)
    ·
      refine ⟨37151025960481083262657579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49534701280641444350210105 37151025960481083262657579)
      ·
        refine ⟨55726538940721624893986369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37151025960481083262657579 55726538940721624893986369)
        ·
          refine ⟨41794904205541218670489777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55726538940721624893986369 41794904205541218670489777)
          ·
            refine ⟨31346178154155914002867333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41794904205541218670489777 31346178154155914002867333)
            ·
              refine ⟨5877408403904233875537625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31346178154155914002867333 5877408403904233875537625)
              ·
                refine ⟨4408056302928175406653219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5877408403904233875537625 4408056302928175406653219)
                ·
                  refine ⟨6612084454392263109979829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4408056302928175406653219 6612084454392263109979829)
                  ·
                    refine ⟨619882917599274666560609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6612084454392263109979829 619882917599274666560609)
                    ·
                      rfl

theorem cell23_3621653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 4, 2, 1, 5].length) (baseStart_3621653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3621653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3621653 prefixEnd_3621653 := by exact prefixLift 3621653
  have htrace : WordTrace (prefixWord ++ tailWord_3621653) baseStart_3621653 baseEnd_3621653 := by
    simpa [prefixWord, tailWord_3621653, baseEnd_3621653] using wordTrace_append hprefix tailTrace_3621653
  have hstable : (prefixWord ++ tailWord_3621653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3621653).length < 2 ^ (prefixWord ++ tailWord_3621653).sum := by decide
  have hdescent : baseEnd_3621653 < baseStart_3621653 := by decide
  rcases family_descends (prefixWord ++ tailWord_3621653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3621661 : List Nat := [1, 4, 2, 4, 2, 1, 1, 3, 1, 4]
def baseStart_3621661 : Nat := 118140960795 + 3621661 * 2 ^ 59
def prefixEnd_3621661 : Nat := 4983230072969 + 3 ^ 40 * 3621661 * 2
def baseEnd_3621661 : Nat := 619884286881019989460597

theorem tailTrace_3621661 : CollatzResearch.WordTrace tailWord_3621661 prefixEnd_3621661 619884286881019989460597 := by
  unfold tailWord_3621661
  simp only [CollatzResearch.WordTrace]
  refine ⟨132092828532348202300184837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88061885688232134866789891 132092828532348202300184837)
  ·
    refine ⟨24767405349815287931284657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 132092828532348202300184837 24767405349815287931284657)
    ·
      refine ⟨18575554012361465948463493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24767405349815287931284657 18575554012361465948463493)
      ·
        refine ⟨3482916377317774865336905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18575554012361465948463493 3482916377317774865336905)
        ·
          refine ⟨2612187282988331149002679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3482916377317774865336905 2612187282988331149002679)
          ·
            refine ⟨3918280924482496723504019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2612187282988331149002679 3918280924482496723504019)
            ·
              refine ⟨5877421386723745085256029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3918280924482496723504019 5877421386723745085256029)
              ·
                refine ⟨2204033020021404406971011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5877421386723745085256029 2204033020021404406971011)
                ·
                  refine ⟨3306049530032106610456517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2204033020021404406971011 3306049530032106610456517)
                  ·
                    refine ⟨619884286881019989460597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3306049530032106610456517 619884286881019989460597)
                    ·
                      rfl

theorem cell23_3621661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 2, 1, 1, 3, 1, 4].length) (baseStart_3621661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3621661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3621661 prefixEnd_3621661 := by exact prefixLift 3621661
  have htrace : WordTrace (prefixWord ++ tailWord_3621661) baseStart_3621661 baseEnd_3621661 := by
    simpa [prefixWord, tailWord_3621661, baseEnd_3621661] using wordTrace_append hprefix tailTrace_3621661
  have hstable : (prefixWord ++ tailWord_3621661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3621661).length < 2 ^ (prefixWord ++ tailWord_3621661).sum := by decide
  have hdescent : baseEnd_3621661 < baseStart_3621661 := by decide
  rcases family_descends (prefixWord ++ tailWord_3621661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3621683 : List Nat := [1, 1, 1, 2, 6, 1, 2, 1, 4, 4]
def baseStart_3621683 : Nat := 118140960795 + 3621683 * 2 ^ 59
def prefixEnd_3621683 : Nat := 4983230072969 + 3 ^ 40 * 3621683 * 2
def baseEnd_3621683 : Nat := 619888052405819627435563

theorem tailTrace_3621683 : CollatzResearch.WordTrace tailWord_3621683 prefixEnd_3621683 619888052405819627435563 := by
  unfold tailWord_3621683
  simp only [CollatzResearch.WordTrace]
  refine ⟨132093630938268500057485703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88062420625512333371657135 132093630938268500057485703)
  ·
    refine ⟨198140446407402750086228555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132093630938268500057485703 198140446407402750086228555)
    ·
      refine ⟨297210669611104125129342833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198140446407402750086228555 297210669611104125129342833)
      ·
        refine ⟨222908002208328093847007125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 297210669611104125129342833 222908002208328093847007125)
        ·
          refine ⟨10448812603515379399078459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 222908002208328093847007125 10448812603515379399078459)
          ·
            refine ⟨15673218905273069098617689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10448812603515379399078459 15673218905273069098617689)
            ·
              refine ⟨11754914178954801823963267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15673218905273069098617689 11754914178954801823963267)
              ·
                refine ⟨17632371268432202735944901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11754914178954801823963267 17632371268432202735944901)
                ·
                  refine ⟨3306069612831038012989669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17632371268432202735944901 3306069612831038012989669)
                  ·
                    refine ⟨619888052405819627435563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3306069612831038012989669 619888052405819627435563)
                    ·
                      rfl

theorem cell23_3621683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 2, 1, 4, 4].length) (baseStart_3621683 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3621683 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3621683 prefixEnd_3621683 := by exact prefixLift 3621683
  have htrace : WordTrace (prefixWord ++ tailWord_3621683) baseStart_3621683 baseEnd_3621683 := by
    simpa [prefixWord, tailWord_3621683, baseEnd_3621683] using wordTrace_append hprefix tailTrace_3621683
  have hstable : (prefixWord ++ tailWord_3621683).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3621683).length < 2 ^ (prefixWord ++ tailWord_3621683).sum := by decide
  have hdescent : baseEnd_3621683 < baseStart_3621683 := by decide
  rcases family_descends (prefixWord ++ tailWord_3621683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3621684 : List Nat := [2, 5, 1, 1, 3, 2, 1, 1, 3, 1, 3]
def baseStart_3621684 : Nat := 118140960795 + 3621684 * 2 ^ 59
def prefixEnd_3621684 : Nat := 4983230072969 + 3 ^ 40 * 3621684 * 2
def baseEnd_3621684 : Nat := 1859664670698113378394185

theorem tailTrace_3621684 : CollatzResearch.WordTrace tailWord_3621684 prefixEnd_3621684 1859664670698113378394185 := by
  unfold tailWord_3621684
  simp only [CollatzResearch.WordTrace]
  refine ⟨66046833705632438614136053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88062444940843251485514737 66046833705632438614136053)
  ·
    refine ⟨6191890659903041120075255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 66046833705632438614136053 6191890659903041120075255)
    ·
      refine ⟨9287835989854561680112883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6191890659903041120075255 9287835989854561680112883)
      ·
        refine ⟨13931753984781842520169325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9287835989854561680112883 13931753984781842520169325)
        ·
          refine ⟨5224407744293190945063497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13931753984781842520169325 5224407744293190945063497)
          ·
            refine ⟨3918305808219893208797623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5224407744293190945063497 3918305808219893208797623)
            ·
              refine ⟨5877458712329839813196435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3918305808219893208797623 5877458712329839813196435)
              ·
                refine ⟨8816188068494759719794653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5877458712329839813196435 8816188068494759719794653)
                ·
                  refine ⟨3306070525685534894922995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8816188068494759719794653 3306070525685534894922995)
                  ·
                    refine ⟨4959105788528302342384493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3306070525685534894922995 4959105788528302342384493)
                    ·
                      refine ⟨1859664670698113378394185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4959105788528302342384493 1859664670698113378394185)
                      ·
                        rfl

theorem cell23_3621684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 2, 1, 1, 3, 1, 3].length) (baseStart_3621684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3621684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3621684 prefixEnd_3621684 := by exact prefixLift 3621684
  have htrace : WordTrace (prefixWord ++ tailWord_3621684) baseStart_3621684 baseEnd_3621684 := by
    simpa [prefixWord, tailWord_3621684, baseEnd_3621684] using wordTrace_append hprefix tailTrace_3621684
  have hstable : (prefixWord ++ tailWord_3621684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3621684).length < 2 ^ (prefixWord ++ tailWord_3621684).sum := by decide
  have hdescent : baseEnd_3621684 < baseStart_3621684 := by decide
  rcases family_descends (prefixWord ++ tailWord_3621684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3621850 : List Nat := [3, 1, 1, 2, 4, 2, 1, 2, 2, 5]
def baseStart_3621850 : Nat := 118140960795 + 3621850 * 2 ^ 59
def prefixEnd_3621850 : Nat := 4983230072969 + 3 ^ 40 * 3621850 * 2
def baseEnd_3621850 : Nat := 619916636162253242972807

theorem tailTrace_3621850 : CollatzResearch.WordTrace tailWord_3621850 prefixEnd_3621850 619916636162253242972807 := by
  unfold tailWord_3621850
  simp only [CollatzResearch.WordTrace]
  refine ⟨33024930482165871894703751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88066481285775658385876669 33024930482165871894703751)
  ·
    refine ⟨49537395723248807842055627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33024930482165871894703751 49537395723248807842055627)
    ·
      refine ⟨74306093584873211763083441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49537395723248807842055627 74306093584873211763083441)
      ·
        refine ⟨55729570188654908822312581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74306093584873211763083441 55729570188654908822312581)
        ·
          refine ⟨10449294410372795404183609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 55729570188654908822312581 10449294410372795404183609)
          ·
            refine ⟨7836970807779596553137707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10449294410372795404183609 7836970807779596553137707)
            ·
              refine ⟨11755456211669394829706561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7836970807779596553137707 11755456211669394829706561)
              ·
                refine ⟨8816592158752046122279921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11755456211669394829706561 8816592158752046122279921)
                ·
                  refine ⟨6612444119064034591709941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8816592158752046122279921 6612444119064034591709941)
                  ·
                    refine ⟨619916636162253242972807, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6612444119064034591709941 619916636162253242972807)
                    ·
                      rfl

theorem cell23_3621850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 1, 2, 2, 5].length) (baseStart_3621850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3621850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3621850 prefixEnd_3621850 := by exact prefixLift 3621850
  have htrace : WordTrace (prefixWord ++ tailWord_3621850) baseStart_3621850 baseEnd_3621850 := by
    simpa [prefixWord, tailWord_3621850, baseEnd_3621850] using wordTrace_append hprefix tailTrace_3621850
  have hstable : (prefixWord ++ tailWord_3621850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3621850).length < 2 ^ (prefixWord ++ tailWord_3621850).sum := by decide
  have hdescent : baseEnd_3621850 < baseStart_3621850 := by decide
  rcases family_descends (prefixWord ++ tailWord_3621850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3621903 : List Nat := [1, 1, 2, 1, 1, 1, 2, 1, 3, 7, 3]
def baseStart_3621903 : Nat := 118140960795 + 3621903 * 2 ^ 59
def prefixEnd_3621903 : Nat := 4983230072969 + 3 ^ 40 * 3621903 * 2
def baseEnd_3621903 : Nat := 1859777122961448021555677

theorem tailTrace_3621903 : CollatzResearch.WordTrace tailWord_3621903 prefixEnd_3621903 1859777122961448021555677 := by
  unfold tailWord_3621903
  simp only [CollatzResearch.WordTrace]
  refine ⟨132101654997471477630494363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88067769998314318420329575 132101654997471477630494363)
  ·
    refine ⟨198152482496207216445741545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132101654997471477630494363 198152482496207216445741545)
    ·
      refine ⟨148614361872155412334306159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 198152482496207216445741545 148614361872155412334306159)
      ·
        refine ⟨222921542808233118501459239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148614361872155412334306159 222921542808233118501459239)
        ·
          refine ⟨334382314212349677752188859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 222921542808233118501459239 334382314212349677752188859)
          ·
            refine ⟨501573471318524516628283289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 334382314212349677752188859 501573471318524516628283289)
            ·
              refine ⟨376180103488893387471212467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 501573471318524516628283289 376180103488893387471212467)
              ·
                refine ⟨564270155233340081206818701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 376180103488893387471212467 564270155233340081206818701)
                ·
                  refine ⟨211601308212502530452557013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 564270155233340081206818701 211601308212502530452557013)
                  ·
                    refine ⟨4959405661230528057481805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 211601308212502530452557013 4959405661230528057481805)
                    ·
                      refine ⟨1859777122961448021555677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4959405661230528057481805 1859777122961448021555677)
                      ·
                        rfl

theorem cell23_3621903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 1, 3, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 1, 3, 7, 3].length) (baseStart_3621903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3621903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3621903 prefixEnd_3621903 := by exact prefixLift 3621903
  have htrace : WordTrace (prefixWord ++ tailWord_3621903) baseStart_3621903 baseEnd_3621903 := by
    simpa [prefixWord, tailWord_3621903, baseEnd_3621903] using wordTrace_append hprefix tailTrace_3621903
  have hstable : (prefixWord ++ tailWord_3621903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3621903).length < 2 ^ (prefixWord ++ tailWord_3621903).sum := by decide
  have hdescent : baseEnd_3621903 < baseStart_3621903 := by decide
  rcases family_descends (prefixWord ++ tailWord_3621903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3621927 : List Nat := [1, 1, 7, 1, 1, 1, 2, 3, 6]
def baseStart_3621927 : Nat := 118140960795 + 3621927 * 2 ^ 59
def prefixEnd_3621927 : Nat := 4983230072969 + 3 ^ 40 * 3621927 * 2
def baseEnd_3621927 : Nat := 206643271833017325295063

theorem tailTrace_3621927 : CollatzResearch.WordTrace tailWord_3621927 prefixEnd_3621927 206643271833017325295063 := by
  unfold tailWord_3621927
  simp only [CollatzResearch.WordTrace]
  refine ⟨132102530349384529729368035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88068353566256353152912023 132102530349384529729368035)
  ·
    refine ⟨198153795524076794594052053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132102530349384529729368035 198153795524076794594052053)
    ·
      refine ⟨4644229582595549873298095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 198153795524076794594052053 4644229582595549873298095)
      ·
        refine ⟨6966344373893324809947143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4644229582595549873298095 6966344373893324809947143)
        ·
          refine ⟨10449516560839987214920715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6966344373893324809947143 10449516560839987214920715)
          ·
            refine ⟨15674274841259980822381073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10449516560839987214920715 15674274841259980822381073)
            ·
              refine ⟨11755706130944985616785805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15674274841259980822381073 11755706130944985616785805)
              ·
                refine ⟨4408389799104369606294677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11755706130944985616785805 4408389799104369606294677)
                ·
                  refine ⟨206643271833017325295063, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4408389799104369606294677 206643271833017325295063)
                  ·
                    rfl

theorem cell23_3621927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 2, 3, 6].length) (baseStart_3621927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3621927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3621927 prefixEnd_3621927 := by exact prefixLift 3621927
  have htrace : WordTrace (prefixWord ++ tailWord_3621927) baseStart_3621927 baseEnd_3621927 := by
    simpa [prefixWord, tailWord_3621927, baseEnd_3621927] using wordTrace_append hprefix tailTrace_3621927
  have hstable : (prefixWord ++ tailWord_3621927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3621927).length < 2 ^ (prefixWord ++ tailWord_3621927).sum := by decide
  have hdescent : baseEnd_3621927 < baseStart_3621927 := by decide
  rcases family_descends (prefixWord ++ tailWord_3621927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3621937 : List Nat := [1, 2, 2, 3, 1, 2, 3, 2, 3, 1, 3]
def baseStart_3621937 : Nat := 118140960795 + 3621937 * 2 ^ 59
def prefixEnd_3621937 : Nat := 4983230072969 + 3 ^ 40 * 3621937 * 2
def baseEnd_3621937 : Nat := 1859794581303700888530521

theorem tailTrace_3621937 : CollatzResearch.WordTrace tailWord_3621937 prefixEnd_3621937 1859794581303700888530521 := by
  unfold tailWord_3621937
  simp only [CollatzResearch.WordTrace]
  refine ⟨132102895079348301437232065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88068596719565534291488043 132102895079348301437232065)
  ·
    refine ⟨99077171309511226077924049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132102895079348301437232065 99077171309511226077924049)
    ·
      refine ⟨74307878482133419558443037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99077171309511226077924049 74307878482133419558443037)
      ·
        refine ⟨27865454430800032334416139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74307878482133419558443037 27865454430800032334416139)
        ·
          refine ⟨41798181646200048501624209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27865454430800032334416139 41798181646200048501624209)
          ·
            refine ⟨31348636234650036376218157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41798181646200048501624209 31348636234650036376218157)
            ·
              refine ⟨11755738587993763641081809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31348636234650036376218157 11755738587993763641081809)
              ·
                refine ⟨8816803940995322730811357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11755738587993763641081809 8816803940995322730811357)
                ·
                  refine ⟨3306301477873246024054259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8816803940995322730811357 3306301477873246024054259)
                  ·
                    refine ⟨4959452216809869036081389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3306301477873246024054259 4959452216809869036081389)
                    ·
                      refine ⟨1859794581303700888530521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4959452216809869036081389 1859794581303700888530521)
                      ·
                        rfl

theorem cell23_3621937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 3, 2, 3, 1, 3].length) (baseStart_3621937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3621937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3621937 prefixEnd_3621937 := by exact prefixLift 3621937
  have htrace : WordTrace (prefixWord ++ tailWord_3621937) baseStart_3621937 baseEnd_3621937 := by
    simpa [prefixWord, tailWord_3621937, baseEnd_3621937] using wordTrace_append hprefix tailTrace_3621937
  have hstable : (prefixWord ++ tailWord_3621937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3621937).length < 2 ^ (prefixWord ++ tailWord_3621937).sum := by decide
  have hdescent : baseEnd_3621937 < baseStart_3621937 := by decide
  rcases family_descends (prefixWord ++ tailWord_3621937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3621957 : List Nat := [1, 3, 1, 1, 1, 3, 6, 1, 1, 5]
def baseStart_3621957 : Nat := 118140960795 + 3621957 * 2 ^ 59
def prefixEnd_3621957 : Nat := 4983230072969 + 3 ^ 40 * 3621957 * 2
def baseEnd_3621957 : Nat := 619934950305596936760143

theorem tailTrace_3621957 : CollatzResearch.WordTrace tailWord_3621957 prefixEnd_3621957 619934950305596936760143 := by
  unfold tailWord_3621957
  simp only [CollatzResearch.WordTrace]
  refine ⟨132103624539275844852960125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88069083026183896568640083 132103624539275844852960125)
  ·
    refine ⟨49538859202228441819860047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 132103624539275844852960125 49538859202228441819860047)
    ·
      refine ⟨74308288803342662729790071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49538859202228441819860047 74308288803342662729790071)
      ·
        refine ⟨111462433205013994094685107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74308288803342662729790071 111462433205013994094685107)
        ·
          refine ⟨167193649807520991142027661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111462433205013994094685107 167193649807520991142027661)
          ·
            refine ⟨62697618677820371678260373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 167193649807520991142027661 62697618677820371678260373)
            ·
              refine ⟨2938950875522829922418455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 62697618677820371678260373 2938950875522829922418455)
              ·
                refine ⟨4408426313284244883627683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2938950875522829922418455 4408426313284244883627683)
                ·
                  refine ⟨6612639469926367325441525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4408426313284244883627683 6612639469926367325441525)
                  ·
                    refine ⟨619934950305596936760143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6612639469926367325441525 619934950305596936760143)
                    ·
                      rfl

theorem cell23_3621957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 6, 1, 1, 5].length) (baseStart_3621957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3621957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3621957 prefixEnd_3621957 := by exact prefixLift 3621957
  have htrace : WordTrace (prefixWord ++ tailWord_3621957) baseStart_3621957 baseEnd_3621957 := by
    simpa [prefixWord, tailWord_3621957, baseEnd_3621957] using wordTrace_append hprefix tailTrace_3621957
  have hstable : (prefixWord ++ tailWord_3621957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3621957).length < 2 ^ (prefixWord ++ tailWord_3621957).sum := by decide
  have hdescent : baseEnd_3621957 < baseStart_3621957 := by decide
  rcases family_descends (prefixWord ++ tailWord_3621957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3621983 : List Nat := [1, 1, 2, 3, 1, 1, 4, 10]
def baseStart_3621983 : Nat := 118140960795 + 3621983 * 2 ^ 59
def prefixEnd_3621983 : Nat := 4983230072969 + 3 ^ 40 * 3621983 * 2
def baseEnd_3621983 : Nat := 68882155607918804020567

theorem tailTrace_3621983 : CollatzResearch.WordTrace tailWord_3621983 prefixEnd_3621983 68882155607918804020567 := by
  unfold tailWord_3621983
  simp only [CollatzResearch.WordTrace]
  refine ⟨132104572837181651293406603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88069715224787767528937735 132104572837181651293406603)
  ·
    refine ⟨198156859255772476940109905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132104572837181651293406603 198156859255772476940109905)
    ·
      refine ⟨148617644441829357705082429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 198156859255772476940109905 148617644441829357705082429)
      ·
        refine ⟨55731616665686009139405911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 148617644441829357705082429 55731616665686009139405911)
        ·
          refine ⟨83597424998529013709108867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55731616665686009139405911 83597424998529013709108867)
          ·
            refine ⟨125396137497793520563663301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83597424998529013709108867 125396137497793520563663301)
            ·
              refine ⟨23511775780836285105686869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 125396137497793520563663301 23511775780836285105686869)
              ·
                refine ⟨68882155607918804020567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 23511775780836285105686869 68882155607918804020567)
                ·
                  rfl

theorem cell23_3621983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 4, 10].length) (baseStart_3621983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3621983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3621983 prefixEnd_3621983 := by exact prefixLift 3621983
  have htrace : WordTrace (prefixWord ++ tailWord_3621983) baseStart_3621983 baseEnd_3621983 := by
    simpa [prefixWord, tailWord_3621983, baseEnd_3621983] using wordTrace_append hprefix tailTrace_3621983
  have hstable : (prefixWord ++ tailWord_3621983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3621983).length < 2 ^ (prefixWord ++ tailWord_3621983).sum := by decide
  have hdescent : baseEnd_3621983 < baseStart_3621983 := by decide
  rcases family_descends (prefixWord ++ tailWord_3621983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3621994 : List Nat := [3, 1, 3, 2, 2, 2, 2, 2, 1, 1, 4]
def baseStart_3621994 : Nat := 118140960795 + 3621994 * 2 ^ 59
def prefixEnd_3621994 : Nat := 4983230072969 + 3 ^ 40 * 3621994 * 2
def baseEnd_3621994 : Nat := 1859823849701007165517759

theorem tailTrace_3621994 : CollatzResearch.WordTrace tailWord_3621994 prefixEnd_3621994 1859823849701007165517759 := by
  unfold tailWord_3621994
  simp only [CollatzResearch.WordTrace]
  refine ⟨33026243510035450043014259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88069982693427866781371357 33026243510035450043014259)
  ·
    refine ⟨49539365265053175064521389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33026243510035450043014259 49539365265053175064521389)
    ·
      refine ⟨18577261974394940649195521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49539365265053175064521389 18577261974394940649195521)
      ·
        refine ⟨13932946480796205486896641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18577261974394940649195521 13932946480796205486896641)
        ·
          refine ⟨10449709860597154115172481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13932946480796205486896641 10449709860597154115172481)
          ·
            refine ⟨7837282395447865586379361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10449709860597154115172481 7837282395447865586379361)
            ·
              refine ⟨5877961796585899189784521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7837282395447865586379361 5877961796585899189784521)
              ·
                refine ⟨4408471347439424392338391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5877961796585899189784521 4408471347439424392338391)
                ·
                  refine ⟨6612707021159136588507587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4408471347439424392338391 6612707021159136588507587)
                  ·
                    refine ⟨9919060531738704882761381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6612707021159136588507587 9919060531738704882761381)
                    ·
                      refine ⟨1859823849701007165517759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9919060531738704882761381 1859823849701007165517759)
                      ·
                        rfl

theorem cell23_3621994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 2, 2, 1, 1, 4].length) (baseStart_3621994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3621994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3621994 prefixEnd_3621994 := by exact prefixLift 3621994
  have htrace : WordTrace (prefixWord ++ tailWord_3621994) baseStart_3621994 baseEnd_3621994 := by
    simpa [prefixWord, tailWord_3621994, baseEnd_3621994] using wordTrace_append hprefix tailTrace_3621994
  have hstable : (prefixWord ++ tailWord_3621994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3621994).length < 2 ^ (prefixWord ++ tailWord_3621994).sum := by decide
  have hdescent : baseEnd_3621994 < baseStart_3621994 := by decide
  rcases family_descends (prefixWord ++ tailWord_3621994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3622003 : List Nat := [1, 1, 1, 2, 2, 1, 1, 1, 3, 4, 6]
def baseStart_3622003 : Nat := 118140960795 + 3622003 * 2 ^ 59
def prefixEnd_3622003 : Nat := 4983230072969 + 3 ^ 40 * 3622003 * 2
def baseEnd_3622003 : Nat := 1859828471026897630305217

theorem tailTrace_3622003 : CollatzResearch.WordTrace tailWord_3622003 prefixEnd_3622003 1859828471026897630305217 := by
  unfold tailWord_3622003
  simp only [CollatzResearch.WordTrace]
  refine ⟨132105302297109194709134663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88070201531406129806089775 132105302297109194709134663)
  ·
    refine ⟨198157953445663792063701995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132105302297109194709134663 198157953445663792063701995)
    ·
      refine ⟨297236930168495688095552993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198157953445663792063701995 297236930168495688095552993)
      ·
        refine ⟨222927697626371766071664745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 297236930168495688095552993 222927697626371766071664745)
        ·
          refine ⟨167195773219778824553748559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 222927697626371766071664745 167195773219778824553748559)
          ·
            refine ⟨250793659829668236830622839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 167195773219778824553748559 250793659829668236830622839)
            ·
              refine ⟨376190489744502355245934259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 250793659829668236830622839 376190489744502355245934259)
              ·
                refine ⟨564285734616753532868901389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 376190489744502355245934259 564285734616753532868901389)
                ·
                  refine ⟨211607150481282574825838021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 564285734616753532868901389 211607150481282574825838021)
                  ·
                    refine ⟨39676340715240482779844629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 211607150481282574825838021 39676340715240482779844629)
                    ·
                      refine ⟨1859828471026897630305217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 39676340715240482779844629 1859828471026897630305217)
                      ·
                        rfl

theorem cell23_3622003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 1, 3, 4, 6].length) (baseStart_3622003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3622003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3622003 prefixEnd_3622003 := by exact prefixLift 3622003
  have htrace : WordTrace (prefixWord ++ tailWord_3622003) baseStart_3622003 baseEnd_3622003 := by
    simpa [prefixWord, tailWord_3622003, baseEnd_3622003] using wordTrace_append hprefix tailTrace_3622003
  have hstable : (prefixWord ++ tailWord_3622003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3622003).length < 2 ^ (prefixWord ++ tailWord_3622003).sum := by decide
  have hdescent : baseEnd_3622003 < baseStart_3622003 := by decide
  rcases family_descends (prefixWord ++ tailWord_3622003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3622005 : List Nat := [1, 3, 4, 3, 1, 2, 1, 3, 1, 1, 3]
def baseStart_3622005 : Nat := 118140960795 + 3622005 * 2 ^ 59
def prefixEnd_3622005 : Nat := 4983230072969 + 3 ^ 40 * 3622005 * 2
def baseEnd_3622005 : Nat := 1859829497988206622480209

theorem tailTrace_3622005 : CollatzResearch.WordTrace tailWord_3622005 prefixEnd_3622005 1859829497988206622480209 := by
  unfold tailWord_3622005
  simp only [CollatzResearch.WordTrace]
  refine ⟨132105375243101949050707469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88070250162067966033804979 132105375243101949050707469)
  ·
    refine ⟨49539515716163230894015301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 132105375243101949050707469 49539515716163230894015301)
    ·
      refine ⟨9288659196780605792627869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 49539515716163230894015301 9288659196780605792627869)
      ·
        refine ⟨3483247198792727172235451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9288659196780605792627869 3483247198792727172235451)
        ·
          refine ⟨5224870798189090758353177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3483247198792727172235451 5224870798189090758353177)
          ·
            refine ⟨3918653098641818068764883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5224870798189090758353177 3918653098641818068764883)
            ·
              refine ⟨5877979647962727103147325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3918653098641818068764883 5877979647962727103147325)
              ·
                refine ⟨2204242367986022663680247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5877979647962727103147325 2204242367986022663680247)
                ·
                  refine ⟨3306363551979033995520371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2204242367986022663680247 3306363551979033995520371)
                  ·
                    refine ⟨4959545327968550993280557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3306363551979033995520371 4959545327968550993280557)
                    ·
                      refine ⟨1859829497988206622480209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4959545327968550993280557 1859829497988206622480209)
                      ·
                        rfl

theorem cell23_3622005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 2, 1, 3, 1, 1, 3].length) (baseStart_3622005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3622005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3622005 prefixEnd_3622005 := by exact prefixLift 3622005
  have htrace : WordTrace (prefixWord ++ tailWord_3622005) baseStart_3622005 baseEnd_3622005 := by
    simpa [prefixWord, tailWord_3622005, baseEnd_3622005] using wordTrace_append hprefix tailTrace_3622005
  have hstable : (prefixWord ++ tailWord_3622005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3622005).length < 2 ^ (prefixWord ++ tailWord_3622005).sum := by decide
  have hdescent : baseEnd_3622005 < baseStart_3622005 := by decide
  rcases family_descends (prefixWord ++ tailWord_3622005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3622067 : List Nat := [1, 1, 1, 2, 3, 2, 3, 1, 3, 4, 2]
def baseStart_3622067 : Nat := 118140960795 + 3622067 * 2 ^ 59
def prefixEnd_3622067 : Nat := 4983230072969 + 3 ^ 40 * 3622067 * 2
def baseEnd_3622067 : Nat := 1859861333788785379904923

theorem tailTrace_3622067 : CollatzResearch.WordTrace tailWord_3622067 prefixEnd_3622067 1859861333788785379904923 := by
  unfold tailWord_3622067
  simp only [CollatzResearch.WordTrace]
  refine ⟨132107636568877333639464455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88071757712584889092976303 132107636568877333639464455)
  ·
    refine ⟨198161454853316000459196683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132107636568877333639464455 198161454853316000459196683)
    ·
      refine ⟨297242182279974000688795025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198161454853316000459196683 297242182279974000688795025)
      ·
        refine ⟨222931636709980500516596269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 297242182279974000688795025 222931636709980500516596269)
        ·
          refine ⟨83599363766242687693723601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 222931636709980500516596269 83599363766242687693723601)
          ·
            refine ⟨62699522824682015770292701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83599363766242687693723601 62699522824682015770292701)
            ·
              refine ⟨23512321059255755913859763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62699522824682015770292701 23512321059255755913859763)
              ·
                refine ⟨35268481588883633870789645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23512321059255755913859763 35268481588883633870789645)
                ·
                  refine ⟨13225680595831362701546117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35268481588883633870789645 13225680595831362701546117)
                  ·
                    refine ⟨2479815111718380506539897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13225680595831362701546117 2479815111718380506539897)
                    ·
                      refine ⟨1859861333788785379904923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2479815111718380506539897 1859861333788785379904923)
                      ·
                        rfl

theorem cell23_3622067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 3, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 3, 1, 3, 4, 2].length) (baseStart_3622067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3622067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3622067 prefixEnd_3622067 := by exact prefixLift 3622067
  have htrace : WordTrace (prefixWord ++ tailWord_3622067) baseStart_3622067 baseEnd_3622067 := by
    simpa [prefixWord, tailWord_3622067, baseEnd_3622067] using wordTrace_append hprefix tailTrace_3622067
  have hstable : (prefixWord ++ tailWord_3622067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3622067).length < 2 ^ (prefixWord ++ tailWord_3622067).sum := by decide
  have hdescent : baseEnd_3622067 < baseStart_3622067 := by decide
  rcases family_descends (prefixWord ++ tailWord_3622067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3622071 : List Nat := [1, 1, 3, 1, 4, 1, 5, 1, 1, 3, 2]
def baseStart_3622071 : Nat := 118140960795 + 3622071 * 2 ^ 59
def prefixEnd_3622071 : Nat := 4983230072969 + 3 ^ 40 * 3622071 * 2
def baseEnd_3622071 : Nat := 1859863387711403364254905

theorem tailTrace_3622071 : CollatzResearch.WordTrace tailWord_3622071 prefixEnd_3622071 1859863387711403364254905 := by
  unfold tailWord_3622071
  simp only [CollatzResearch.WordTrace]
  refine ⟨132107782460862842322610067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88071854973908561548406711 132107782460862842322610067)
  ·
    refine ⟨198161673691294263483915101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132107782460862842322610067 198161673691294263483915101)
    ·
      refine ⟨74310627634235348806468163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 198161673691294263483915101 74310627634235348806468163)
      ·
        refine ⟨111465941451353023209702245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74310627634235348806468163 111465941451353023209702245)
        ·
          refine ⟨20899864022128691851819171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 111465941451353023209702245 20899864022128691851819171)
          ·
            refine ⟨31349796033193037777728757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20899864022128691851819171 31349796033193037777728757)
            ·
              refine ⟨2939043378111847291662071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 31349796033193037777728757 2939043378111847291662071)
              ·
                refine ⟨4408565067167770937493107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2939043378111847291662071 4408565067167770937493107)
                ·
                  refine ⟨6612847600751656406239661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4408565067167770937493107 6612847600751656406239661)
                  ·
                    refine ⟨2479817850281871152339873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6612847600751656406239661 2479817850281871152339873)
                    ·
                      refine ⟨1859863387711403364254905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2479817850281871152339873 1859863387711403364254905)
                      ·
                        rfl

theorem cell23_3622071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 5, 1, 1, 3, 2].length) (baseStart_3622071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3622071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3622071 prefixEnd_3622071 := by exact prefixLift 3622071
  have htrace : WordTrace (prefixWord ++ tailWord_3622071) baseStart_3622071 baseEnd_3622071 := by
    simpa [prefixWord, tailWord_3622071, baseEnd_3622071] using wordTrace_append hprefix tailTrace_3622071
  have hstable : (prefixWord ++ tailWord_3622071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3622071).length < 2 ^ (prefixWord ++ tailWord_3622071).sum := by decide
  have hdescent : baseEnd_3622071 < baseStart_3622071 := by decide
  rcases family_descends (prefixWord ++ tailWord_3622071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3622101 : List Nat := [1, 3, 2, 4, 1, 2, 2, 1, 1, 4, 2]
def baseStart_3622101 : Nat := 118140960795 + 3622101 * 2 ^ 59
def prefixEnd_3622101 : Nat := 4983230072969 + 3 ^ 40 * 3622101 * 2
def baseEnd_3622101 : Nat := 1859878792131038246879767

theorem tailTrace_3622101 : CollatzResearch.WordTrace tailWord_3622101 prefixEnd_3622101 1859878792131038246879767 := by
  unfold tailWord_3622101
  simp only [CollatzResearch.WordTrace]
  refine ⟨132108876650754157446202157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88072584433836104964134771 132108876650754157446202157)
  ·
    refine ⟨49540828744032809042325809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 132108876650754157446202157 49540828744032809042325809)
    ·
      refine ⟨37155621558024606781744357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49540828744032809042325809 37155621558024606781744357)
      ·
        refine ⟨6966679042129613771577067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37155621558024606781744357 6966679042129613771577067)
        ·
          refine ⟨10450018563194420657365601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6966679042129613771577067 10450018563194420657365601)
          ·
            refine ⟨7837513922395815493024201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10450018563194420657365601 7837513922395815493024201)
            ·
              refine ⟨5878135441796861619768151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7837513922395815493024201 5878135441796861619768151)
              ·
                refine ⟨8817203162695292429652227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5878135441796861619768151 8817203162695292429652227)
                ·
                  refine ⟨13225804744042938644478341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8817203162695292429652227 13225804744042938644478341)
                  ·
                    refine ⟨2479838389508050995839689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13225804744042938644478341 2479838389508050995839689)
                    ·
                      refine ⟨1859878792131038246879767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2479838389508050995839689 1859878792131038246879767)
                      ·
                        rfl

theorem cell23_3622101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 2, 1, 1, 4, 2].length) (baseStart_3622101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3622101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3622101 prefixEnd_3622101 := by exact prefixLift 3622101
  have htrace : WordTrace (prefixWord ++ tailWord_3622101) baseStart_3622101 baseEnd_3622101 := by
    simpa [prefixWord, tailWord_3622101, baseEnd_3622101] using wordTrace_append hprefix tailTrace_3622101
  have hstable : (prefixWord ++ tailWord_3622101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3622101).length < 2 ^ (prefixWord ++ tailWord_3622101).sum := by decide
  have hdescent : baseEnd_3622101 < baseStart_3622101 := by decide
  rcases family_descends (prefixWord ++ tailWord_3622101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3622124 : List Nat := [2, 2, 1, 1, 2, 5, 2, 3, 5]
def baseStart_3622124 : Nat := 118140960795 + 3622124 * 2 ^ 59
def prefixEnd_3622124 : Nat := 4983230072969 + 3 ^ 40 * 3622124 * 2
def baseEnd_3622124 : Nat := 206654511354010184099129

theorem tailTrace_3622124 : CollatzResearch.WordTrace tailWord_3622124 prefixEnd_3622124 206654511354010184099129 := by
  unfold tailWord_3622124
  simp only [CollatzResearch.WordTrace]
  refine ⟨66054857764835416187144713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88073143686447221582859617 66054857764835416187144713)
  ·
    refine ⟨49541143323626562140358535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66054857764835416187144713 49541143323626562140358535)
    ·
      refine ⟨74311714985439843210537803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49541143323626562140358535 74311714985439843210537803)
      ·
        refine ⟨111467572478159764815806705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74311714985439843210537803 111467572478159764815806705)
        ·
          refine ⟨83600679358619823611855029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 111467572478159764815806705 83600679358619823611855029)
          ·
            refine ⟨7837563689870608463611409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 83600679358619823611855029 7837563689870608463611409)
            ·
              refine ⟨5878172767402956347708557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7837563689870608463611409 5878172767402956347708557)
              ·
                refine ⟨2204314787776108630390709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5878172767402956347708557 2204314787776108630390709)
                ·
                  refine ⟨206654511354010184099129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2204314787776108630390709 206654511354010184099129)
                  ·
                    rfl

theorem cell23_3622124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 2, 3, 5].length) (baseStart_3622124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3622124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3622124 prefixEnd_3622124 := by exact prefixLift 3622124
  have htrace : WordTrace (prefixWord ++ tailWord_3622124) baseStart_3622124 baseEnd_3622124 := by
    simpa [prefixWord, tailWord_3622124, baseEnd_3622124] using wordTrace_append hprefix tailTrace_3622124
  have hstable : (prefixWord ++ tailWord_3622124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3622124).length < 2 ^ (prefixWord ++ tailWord_3622124).sum := by decide
  have hdescent : baseEnd_3622124 < baseStart_3622124 := by decide
  rcases family_descends (prefixWord ++ tailWord_3622124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3622160 : List Nat := [2, 1, 1, 1, 1, 1, 1, 1, 6, 3, 5]
def baseStart_3622160 : Nat := 118140960795 + 3622160 * 2 ^ 59
def prefixEnd_3622160 : Nat := 4983230072969 + 3 ^ 40 * 3622160 * 2
def baseEnd_3622160 : Nat := 1859909087489653516041995

theorem tailTrace_3622160 : CollatzResearch.WordTrace tailWord_3622160 prefixEnd_3622160 1859909087489653516041995 := by
  unfold tailWord_3622160
  simp only [CollatzResearch.WordTrace]
  refine ⟨66055514278770205261299967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88074019038360273681733289 66055514278770205261299967)
  ·
    refine ⟨99083271418155307891949951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66055514278770205261299967 99083271418155307891949951)
    ·
      refine ⟨148624907127232961837924927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99083271418155307891949951 148624907127232961837924927)
      ·
        refine ⟨222937360690849442756887391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148624907127232961837924927 222937360690849442756887391)
        ·
          refine ⟨334406041036274164135331087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 222937360690849442756887391 334406041036274164135331087)
          ·
            refine ⟨501609061554411246202996631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 334406041036274164135331087 501609061554411246202996631)
            ·
              refine ⟨752413592331616869304494947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 501609061554411246202996631 752413592331616869304494947)
              ·
                refine ⟨1128620388497425303956742421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 752413592331616869304494947 1128620388497425303956742421)
                ·
                  refine ⟨52904080710816811122972301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1128620388497425303956742421 52904080710816811122972301)
                  ·
                    refine ⟨19839030266556304171114613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 52904080710816811122972301 19839030266556304171114613)
                    ·
                      refine ⟨1859909087489653516041995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19839030266556304171114613 1859909087489653516041995)
                      ·
                        rfl

theorem cell23_3622160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 6, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 6, 3, 5].length) (baseStart_3622160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3622160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3622160 prefixEnd_3622160 := by exact prefixLift 3622160
  have htrace : WordTrace (prefixWord ++ tailWord_3622160) baseStart_3622160 baseEnd_3622160 := by
    simpa [prefixWord, tailWord_3622160, baseEnd_3622160] using wordTrace_append hprefix tailTrace_3622160
  have hstable : (prefixWord ++ tailWord_3622160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3622160).length < 2 ^ (prefixWord ++ tailWord_3622160).sum := by decide
  have hdescent : baseEnd_3622160 < baseStart_3622160 := by decide
  rcases family_descends (prefixWord ++ tailWord_3622160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3622194 : List Nat := [3, 2, 1, 1, 4, 1, 1, 1, 4, 2, 3]
def baseStart_3622194 : Nat := 118140960795 + 3622194 * 2 ^ 59
def prefixEnd_3622194 : Nat := 4983230072969 + 3 ^ 40 * 3622194 * 2
def baseEnd_3622194 : Nat := 1859926545831906383016839

theorem tailTrace_3622194 : CollatzResearch.WordTrace tailWord_3622194 prefixEnd_3622194 1859926545831906383016839 := by
  unfold tailWord_3622194
  simp only [CollatzResearch.WordTrace]
  refine ⟨33028067159854308582334409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88074845759611489552891757 33028067159854308582334409)
  ·
    refine ⟨24771050369890731436750807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33028067159854308582334409 24771050369890731436750807)
    ·
      refine ⟨37156575554836097155126211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24771050369890731436750807 37156575554836097155126211)
      ·
        refine ⟨55734863332254145732689317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37156575554836097155126211 55734863332254145732689317)
        ·
          refine ⟨10450286874797652324879247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 55734863332254145732689317 10450286874797652324879247)
          ·
            refine ⟨15675430312196478487318871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10450286874797652324879247 15675430312196478487318871)
            ·
              refine ⟨23513145468294717730978307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15675430312196478487318871 23513145468294717730978307)
              ·
                refine ⟨35269718202442076596467461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23513145468294717730978307 35269718202442076596467461)
                ·
                  refine ⟨6613072162957889361837649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35269718202442076596467461 6613072162957889361837649)
                  ·
                    refine ⟨4959804122218417021378237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6613072162957889361837649 4959804122218417021378237)
                    ·
                      refine ⟨1859926545831906383016839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4959804122218417021378237 1859926545831906383016839)
                      ·
                        rfl

theorem cell23_3622194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 1, 1, 4, 2, 3].length) (baseStart_3622194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3622194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3622194 prefixEnd_3622194 := by exact prefixLift 3622194
  have htrace : WordTrace (prefixWord ++ tailWord_3622194) baseStart_3622194 baseEnd_3622194 := by
    simpa [prefixWord, tailWord_3622194, baseEnd_3622194] using wordTrace_append hprefix tailTrace_3622194
  have hstable : (prefixWord ++ tailWord_3622194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3622194).length < 2 ^ (prefixWord ++ tailWord_3622194).sum := by decide
  have hdescent : baseEnd_3622194 < baseStart_3622194 := by decide
  rcases family_descends (prefixWord ++ tailWord_3622194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3622197 : List Nat := [1, 3, 3, 1, 2, 2, 2, 1, 8]
def baseStart_3622197 : Nat := 118140960795 + 3622197 * 2 ^ 59
def prefixEnd_3622197 : Nat := 4983230072969 + 3 ^ 40 * 3622197 * 2
def baseEnd_3622197 : Nat := 206658676252652207919925

theorem tailTrace_3622197 : CollatzResearch.WordTrace tailWord_3622197 prefixEnd_3622197 206658676252652207919925 := by
  unfold tailWord_3622197
  simp only [CollatzResearch.WordTrace]
  refine ⟨132112378058406365841696845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88074918705604243894464563 132112378058406365841696845)
  ·
    refine ⟨49542141771902387190636317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 132112378058406365841696845 49542141771902387190636317)
    ·
      refine ⟨18578303164463395196488619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49542141771902387190636317 18578303164463395196488619)
      ·
        refine ⟨27867454746695092794732929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18578303164463395196488619 27867454746695092794732929)
        ·
          refine ⟨20900591060021319596049697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27867454746695092794732929 20900591060021319596049697)
          ·
            refine ⟨15675443295015989697037273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20900591060021319596049697 15675443295015989697037273)
            ·
              refine ⟨11756582471261992272777955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15675443295015989697037273 11756582471261992272777955)
              ·
                refine ⟨17634873706892988409166933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11756582471261992272777955 17634873706892988409166933)
                ·
                  refine ⟨206658676252652207919925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 17634873706892988409166933 206658676252652207919925)
                  ·
                    rfl

theorem cell23_3622197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 2, 1, 8].length) (baseStart_3622197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3622197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3622197 prefixEnd_3622197 := by exact prefixLift 3622197
  have htrace : WordTrace (prefixWord ++ tailWord_3622197) baseStart_3622197 baseEnd_3622197 := by
    simpa [prefixWord, tailWord_3622197, baseEnd_3622197] using wordTrace_append hprefix tailTrace_3622197
  have hstable : (prefixWord ++ tailWord_3622197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3622197).length < 2 ^ (prefixWord ++ tailWord_3622197).sum := by decide
  have hdescent : baseEnd_3622197 < baseStart_3622197 := by decide
  rcases family_descends (prefixWord ++ tailWord_3622197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3622224 : List Nat := [2, 1, 1, 1, 1, 5, 2, 1, 5, 1, 3]
def baseStart_3622224 : Nat := 118140960795 + 3622224 * 2 ^ 59
def prefixEnd_3622224 : Nat := 4983230072969 + 3 ^ 40 * 3622224 * 2
def baseEnd_3622224 : Nat := 1859941950251541265641701

theorem tailTrace_3622224 : CollatzResearch.WordTrace tailWord_3622224 prefixEnd_3622224 1859941950251541265641701 := by
  unfold tailWord_3622224
  simp only [CollatzResearch.WordTrace]
  refine ⟨66056681414654274726464863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88075575219539032968619817 66056681414654274726464863)
  ·
    refine ⟨99085022121981412089697295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66056681414654274726464863 99085022121981412089697295)
    ·
      refine ⟨148627533182972118134545943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99085022121981412089697295 148627533182972118134545943)
      ·
        refine ⟨222941299774458177201818915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148627533182972118134545943 222941299774458177201818915)
        ·
          refine ⟨334411949661687265802728373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 222941299774458177201818915 334411949661687265802728373)
          ·
            refine ⟨31351120280783181169005785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 334411949661687265802728373 31351120280783181169005785)
            ·
              refine ⟨23513340210587385876754339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31351120280783181169005785 23513340210587385876754339)
              ·
                refine ⟨35270010315881078815131509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23513340210587385876754339 35270010315881078815131509)
                ·
                  refine ⟨3306563467113851138918579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 35270010315881078815131509 3306563467113851138918579)
                  ·
                    refine ⟨4959845200670776708377869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3306563467113851138918579 4959845200670776708377869)
                    ·
                      refine ⟨1859941950251541265641701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4959845200670776708377869 1859941950251541265641701)
                      ·
                        rfl

theorem cell23_3622224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 2, 1, 5, 1, 3].length) (baseStart_3622224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3622224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3622224 prefixEnd_3622224 := by exact prefixLift 3622224
  have htrace : WordTrace (prefixWord ++ tailWord_3622224) baseStart_3622224 baseEnd_3622224 := by
    simpa [prefixWord, tailWord_3622224, baseEnd_3622224] using wordTrace_append hprefix tailTrace_3622224
  have hstable : (prefixWord ++ tailWord_3622224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3622224).length < 2 ^ (prefixWord ++ tailWord_3622224).sum := by decide
  have hdescent : baseEnd_3622224 < baseStart_3622224 := by decide
  rcases family_descends (prefixWord ++ tailWord_3622224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3622227 : List Nat := [1, 1, 1, 2, 1, 1, 7, 1, 3, 5]
def baseStart_3622227 : Nat := 118140960795 + 3622227 * 2 ^ 59
def prefixEnd_3622227 : Nat := 4983230072969 + 3 ^ 40 * 3622227 * 2
def baseEnd_3622227 : Nat := 619981163564501584634729

theorem tailTrace_3622227 : CollatzResearch.WordTrace tailWord_3622227 prefixEnd_3622227 619981163564501584634729 := by
  unfold tailWord_3622227
  simp only [CollatzResearch.WordTrace]
  refine ⟨132113472248297680965288935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88075648165531787310192623 132113472248297680965288935)
  ·
    refine ⟨198170208372446521447933403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132113472248297680965288935 198170208372446521447933403)
    ·
      refine ⟨297255312558669782171900105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198170208372446521447933403 297255312558669782171900105)
      ·
        refine ⟨222941484419002336628925079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 297255312558669782171900105 222941484419002336628925079)
        ·
          refine ⟨334412226628503504943387619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 222941484419002336628925079 334412226628503504943387619)
          ·
            refine ⟨501618339942755257415081429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 334412226628503504943387619 501618339942755257415081429)
            ·
              refine ⟨11756679842408326345665971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 501618339942755257415081429 11756679842408326345665971)
              ·
                refine ⟨17635019763612489518498957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11756679842408326345665971 17635019763612489518498957)
                ·
                  refine ⟨6613132411354683569437109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17635019763612489518498957 6613132411354683569437109)
                  ·
                    refine ⟨619981163564501584634729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6613132411354683569437109 619981163564501584634729)
                    ·
                      rfl

theorem cell23_3622227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 7, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 7, 1, 3, 5].length) (baseStart_3622227 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3622227 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3622227 prefixEnd_3622227 := by exact prefixLift 3622227
  have htrace : WordTrace (prefixWord ++ tailWord_3622227) baseStart_3622227 baseEnd_3622227 := by
    simpa [prefixWord, tailWord_3622227, baseEnd_3622227] using wordTrace_append hprefix tailTrace_3622227
  have hstable : (prefixWord ++ tailWord_3622227).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3622227).length < 2 ^ (prefixWord ++ tailWord_3622227).sum := by decide
  have hdescent : baseEnd_3622227 < baseStart_3622227 := by decide
  rcases family_descends (prefixWord ++ tailWord_3622227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3622234 : List Nat := [3, 1, 1, 2, 1, 2, 2, 3, 1, 5, 2]
def baseStart_3622234 : Nat := 118140960795 + 3622234 * 2 ^ 59
def prefixEnd_3622234 : Nat := 4983230072969 + 3 ^ 40 * 3622234 * 2
def baseEnd_3622234 : Nat := 1859947085058086226516655

theorem tailTrace_3622234 : CollatzResearch.WordTrace tailWord_3622234 prefixEnd_3622234 1859947085058086226516655 := by
  unfold tailWord_3622234
  simp only [CollatzResearch.WordTrace]
  refine ⟨33028431889818080290198439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88075818372848214107195837 33028431889818080290198439)
  ·
    refine ⟨49542647834727120435297659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33028431889818080290198439 49542647834727120435297659)
    ·
      refine ⟨74313971752090680652946489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49542647834727120435297659 74313971752090680652946489)
      ·
        refine ⟨55735478814068010489709867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74313971752090680652946489 55735478814068010489709867)
        ·
          refine ⟨83603218221102015734564801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55735478814068010489709867 83603218221102015734564801)
          ·
            refine ⟨62702413665826511800923601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83603218221102015734564801 62702413665826511800923601)
            ·
              refine ⟨47026810249369883850692701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62702413665826511800923601 47026810249369883850692701)
              ·
                refine ⟨17635053843513706444009763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47026810249369883850692701 17635053843513706444009763)
                ·
                  refine ⟨26452580765270559666014645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17635053843513706444009763 26452580765270559666014645)
                  ·
                    refine ⟨2479929446744114968688873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 26452580765270559666014645 2479929446744114968688873)
                    ·
                      refine ⟨1859947085058086226516655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2479929446744114968688873 1859947085058086226516655)
                      ·
                        rfl

theorem cell23_3622234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 3, 1, 5, 2].length) (baseStart_3622234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3622234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3622234 prefixEnd_3622234 := by exact prefixLift 3622234
  have htrace : WordTrace (prefixWord ++ tailWord_3622234) baseStart_3622234 baseEnd_3622234 := by
    simpa [prefixWord, tailWord_3622234, baseEnd_3622234] using wordTrace_append hprefix tailTrace_3622234
  have hstable : (prefixWord ++ tailWord_3622234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3622234).length < 2 ^ (prefixWord ++ tailWord_3622234).sum := by decide
  have hdescent : baseEnd_3622234 < baseStart_3622234 := by decide
  rcases family_descends (prefixWord ++ tailWord_3622234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3622258 : List Nat := [3, 2, 1, 2, 1, 2, 3, 4, 1, 1, 3]
def baseStart_3622258 : Nat := 118140960795 + 3622258 * 2 ^ 59
def prefixEnd_3622258 : Nat := 4983230072969 + 3 ^ 40 * 3622258 * 2
def baseEnd_3622258 : Nat := 1859959408593794132616545

theorem tailTrace_3622258 : CollatzResearch.WordTrace tailWord_3622258 prefixEnd_3622258 1859959408593794132616545 := by
  unfold tailWord_3622258
  simp only [CollatzResearch.WordTrace]
  refine ⟨33028650727796343314916857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88076401940790248839778285 33028650727796343314916857)
  ·
    refine ⟨24771488045847257486187643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33028650727796343314916857 24771488045847257486187643)
    ·
      refine ⟨37157232068770886229281465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24771488045847257486187643 37157232068770886229281465)
      ·
        refine ⟨27867924051578164671961099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37157232068770886229281465 27867924051578164671961099)
        ·
          refine ⟨41801886077367247007941649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27867924051578164671961099 41801886077367247007941649)
          ·
            refine ⟨31351414558025435255956237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41801886077367247007941649 31351414558025435255956237)
            ·
              refine ⟨11756780459259538220983589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31351414558025435255956237 11756780459259538220983589)
              ·
                refine ⟨2204396336111163416434423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11756780459259538220983589 2204396336111163416434423)
                ·
                  refine ⟨3306594504166745124651635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2204396336111163416434423 3306594504166745124651635)
                  ·
                    refine ⟨4959891756250117686977453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3306594504166745124651635 4959891756250117686977453)
                    ·
                      refine ⟨1859959408593794132616545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4959891756250117686977453 1859959408593794132616545)
                      ·
                        rfl

theorem cell23_3622258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 3, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 3, 4, 1, 1, 3].length) (baseStart_3622258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3622258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3622258 prefixEnd_3622258 := by exact prefixLift 3622258
  have htrace : WordTrace (prefixWord ++ tailWord_3622258) baseStart_3622258 baseEnd_3622258 := by
    simpa [prefixWord, tailWord_3622258, baseEnd_3622258] using wordTrace_append hprefix tailTrace_3622258
  have hstable : (prefixWord ++ tailWord_3622258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3622258).length < 2 ^ (prefixWord ++ tailWord_3622258).sum := by decide
  have hdescent : baseEnd_3622258 < baseStart_3622258 := by decide
  rcases family_descends (prefixWord ++ tailWord_3622258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3622267 : List Nat := [1, 1, 1, 1, 1, 6, 2, 1, 3, 1, 5]
def baseStart_3622267 : Nat := 118140960795 + 3622267 * 2 ^ 59
def prefixEnd_3622267 : Nat := 4983230072969 + 3 ^ 40 * 3622267 * 2
def baseEnd_3622267 : Nat := 1859964029919684597404003

theorem tailTrace_3622267 : CollatzResearch.WordTrace tailWord_3622267 prefixEnd_3622267 1859964029919684597404003 := by
  unfold tailWord_3622267
  simp only [CollatzResearch.WordTrace]
  refine ⟨132114931168152767796745055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88076620778768511864496703 132114931168152767796745055)
  ·
    refine ⟨198172396752229151695117583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132114931168152767796745055 198172396752229151695117583)
    ·
      refine ⟨297258595128343727542676375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198172396752229151695117583 297258595128343727542676375)
      ·
        refine ⟨445887892692515591314014563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 297258595128343727542676375 445887892692515591314014563)
        ·
          refine ⟨668831839038773386971021845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 445887892692515591314014563 668831839038773386971021845)
          ·
            refine ⟨31351492454942502514266649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 668831839038773386971021845 31351492454942502514266649)
            ·
              refine ⟨23513619341206876885699987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31351492454942502514266649 23513619341206876885699987)
              ·
                refine ⟨35270429011810315328549981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23513619341206876885699987 35270429011810315328549981)
                ·
                  refine ⟨13226410879428868248206243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35270429011810315328549981 13226410879428868248206243)
                  ·
                    refine ⟨19839616319143302372309365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13226410879428868248206243 19839616319143302372309365)
                    ·
                      refine ⟨1859964029919684597404003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19839616319143302372309365 1859964029919684597404003)
                      ·
                        rfl

theorem cell23_3622267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 2, 1, 3, 1, 5].length) (baseStart_3622267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3622267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3622267 prefixEnd_3622267 := by exact prefixLift 3622267
  have htrace : WordTrace (prefixWord ++ tailWord_3622267) baseStart_3622267 baseEnd_3622267 := by
    simpa [prefixWord, tailWord_3622267, baseEnd_3622267] using wordTrace_append hprefix tailTrace_3622267
  have hstable : (prefixWord ++ tailWord_3622267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3622267).length < 2 ^ (prefixWord ++ tailWord_3622267).sum := by decide
  have hdescent : baseEnd_3622267 < baseStart_3622267 := by decide
  rcases family_descends (prefixWord ++ tailWord_3622267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3622277 : List Nat := [1, 3, 1, 1, 3, 1, 2, 3, 1, 1, 6]
def baseStart_3622277 : Nat := 118140960795 + 3622277 * 2 ^ 59
def prefixEnd_3622277 : Nat := 4983230072969 + 3 ^ 40 * 3622277 * 2
def baseEnd_3622277 : Nat := 1859969164726229558278957

theorem tailTrace_3622277 : CollatzResearch.WordTrace tailWord_3622277 prefixEnd_3622277 1859969164726229558278957 := by
  unfold tailWord_3622277
  simp only [CollatzResearch.WordTrace]
  refine ⟨132115295898116539504609085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88076863932077693003072723 132115295898116539504609085)
  ·
    refine ⟨49543235961793702314228407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 132115295898116539504609085 49543235961793702314228407)
    ·
      refine ⟨74314853942690553471342611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49543235961793702314228407 74314853942690553471342611)
      ·
        refine ⟨111472280914035830207013917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74314853942690553471342611 111472280914035830207013917)
        ·
          refine ⟨41802105342763436327630219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 111472280914035830207013917 41802105342763436327630219)
          ·
            refine ⟨62703158014145154491445329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41802105342763436327630219 62703158014145154491445329)
            ·
              refine ⟨47027368510608865868583997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62703158014145154491445329 47027368510608865868583997)
              ·
                refine ⟨17635263191478324700718999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47027368510608865868583997 17635263191478324700718999)
                ·
                  refine ⟨26452894787217487051078499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17635263191478324700718999 26452894787217487051078499)
                  ·
                    refine ⟨39679342180826230576617749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26452894787217487051078499 39679342180826230576617749)
                    ·
                      refine ⟨1859969164726229558278957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 39679342180826230576617749 1859969164726229558278957)
                      ·
                        rfl

theorem cell23_3622277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 3, 1, 1, 6].length) (baseStart_3622277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3622277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3622277 prefixEnd_3622277 := by exact prefixLift 3622277
  have htrace : WordTrace (prefixWord ++ tailWord_3622277) baseStart_3622277 baseEnd_3622277 := by
    simpa [prefixWord, tailWord_3622277, baseEnd_3622277] using wordTrace_append hprefix tailTrace_3622277
  have hstable : (prefixWord ++ tailWord_3622277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3622277).length < 2 ^ (prefixWord ++ tailWord_3622277).sum := by decide
  have hdescent : baseEnd_3622277 < baseStart_3622277 := by decide
  rcases family_descends (prefixWord ++ tailWord_3622277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3622284 : List Nat := [2, 2, 1, 2, 1, 3, 1, 3, 3, 2, 3]
def baseStart_3622284 : Nat := 118140960795 + 3622284 * 2 ^ 59
def prefixEnd_3622284 : Nat := 4983230072969 + 3 ^ 40 * 3622284 * 2
def baseEnd_3622284 : Nat := 1859972759090811030891425

theorem tailTrace_3622284 : CollatzResearch.WordTrace tailWord_3622284 prefixEnd_3622284 1859972759090811030891425 := by
  unfold tailWord_3622284
  simp only [CollatzResearch.WordTrace]
  refine ⟨66057775604545589850056953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88077034139394119800075937 66057775604545589850056953)
  ·
    refine ⟨49543331703409192387542715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66057775604545589850056953 49543331703409192387542715)
    ·
      refine ⟨74314997555113788581314073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49543331703409192387542715 74314997555113788581314073)
      ·
        refine ⟨55736248166335341435985555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74314997555113788581314073 55736248166335341435985555)
        ·
          refine ⟨83604372249503012153978333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55736248166335341435985555 83604372249503012153978333)
          ·
            refine ⟨31351639593563629557741875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 83604372249503012153978333 31351639593563629557741875)
            ·
              refine ⟨47027459390345444336612813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31351639593563629557741875 47027459390345444336612813)
              ·
                refine ⟨17635297271379541626229805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47027459390345444336612813 17635297271379541626229805)
                ·
                  refine ⟨6613236476767328109836177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17635297271379541626229805 6613236476767328109836177)
                  ·
                    refine ⟨4959927357575496082377133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6613236476767328109836177 4959927357575496082377133)
                    ·
                      refine ⟨1859972759090811030891425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4959927357575496082377133 1859972759090811030891425)
                      ·
                        rfl

theorem cell23_3622284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 3, 3, 2, 3].length) (baseStart_3622284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3622284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3622284 prefixEnd_3622284 := by exact prefixLift 3622284
  have htrace : WordTrace (prefixWord ++ tailWord_3622284) baseStart_3622284 baseEnd_3622284 := by
    simpa [prefixWord, tailWord_3622284, baseEnd_3622284] using wordTrace_append hprefix tailTrace_3622284
  have hstable : (prefixWord ++ tailWord_3622284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3622284).length < 2 ^ (prefixWord ++ tailWord_3622284).sum := by decide
  have hdescent : baseEnd_3622284 < baseStart_3622284 := by decide
  rcases family_descends (prefixWord ++ tailWord_3622284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3622347 : List Nat := [1, 1, 1, 1, 3, 3, 2, 2, 1, 8]
def baseStart_3622347 : Nat := 118140960795 + 3622347 * 2 ^ 59
def prefixEnd_3622347 : Nat := 4983230072969 + 3 ^ 40 * 3622347 * 2
def baseEnd_3622347 : Nat := 620001702790681428134545

theorem tailTrace_3622347 : CollatzResearch.WordTrace tailWord_3622347 prefixEnd_3622347 620001702790681428134545 := by
  unfold tailWord_3622347
  simp only [CollatzResearch.WordTrace]
  refine ⟨132117849007862941459657295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88078566005241960973104863 132117849007862941459657295)
  ·
    refine ⟨198176773511794412189485943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132117849007862941459657295 198176773511794412189485943)
    ·
      refine ⟨297265160267691618284228915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198176773511794412189485943 297265160267691618284228915)
      ·
        refine ⟨445897740401537427426343373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 297265160267691618284228915 445897740401537427426343373)
        ·
          refine ⟨167211652650576535284878765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 445897740401537427426343373 167211652650576535284878765)
          ·
            refine ⟨62704369743966200731829537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 167211652650576535284878765 62704369743966200731829537)
            ·
              refine ⟨47028277307974650548872153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62704369743966200731829537 47028277307974650548872153)
              ·
                refine ⟨35271207980980987911654115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47028277307974650548872153 35271207980980987911654115)
                ·
                  refine ⟨52906811971471481867481173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35271207980980987911654115 52906811971471481867481173)
                  ·
                    refine ⟨620001702790681428134545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 52906811971471481867481173 620001702790681428134545)
                    ·
                      rfl

theorem cell23_3622347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 2, 1, 8].length) (baseStart_3622347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3622347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3622347 prefixEnd_3622347 := by exact prefixLift 3622347
  have htrace : WordTrace (prefixWord ++ tailWord_3622347) baseStart_3622347 baseEnd_3622347 := by
    simpa [prefixWord, tailWord_3622347, baseEnd_3622347] using wordTrace_append hprefix tailTrace_3622347
  have hstable : (prefixWord ++ tailWord_3622347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3622347).length < 2 ^ (prefixWord ++ tailWord_3622347).sum := by decide
  have hdescent : baseEnd_3622347 < baseStart_3622347 := by decide
  rcases family_descends (prefixWord ++ tailWord_3622347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3622431 : List Nat := [1, 1, 2, 4, 1, 1, 3, 1, 2, 5, 2]
def baseStart_3622431 : Nat := 118140960795 + 3622431 * 2 ^ 59
def prefixEnd_3622431 : Nat := 4983230072969 + 3 ^ 40 * 3622431 * 2
def baseEnd_3622431 : Nat := 1860048240747021955753249

theorem tailTrace_3622431 : CollatzResearch.WordTrace tailWord_3622431 prefixEnd_3622431 1860048240747021955753249 := by
  unfold tailWord_3622431
  simp only [CollatzResearch.WordTrace]
  refine ⟨132120912739558623805715147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88080608493039082537143431 132120912739558623805715147)
  ·
    refine ⟨198181369109337935708572721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132120912739558623805715147 198181369109337935708572721)
    ·
      refine ⟨148636026832003451781429541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 198181369109337935708572721 148636026832003451781429541)
      ·
        refine ⟨27869255031000647209018039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 148636026832003451781429541 27869255031000647209018039)
        ·
          refine ⟨41803882546500970813527059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27869255031000647209018039 41803882546500970813527059)
          ·
            refine ⟨62705823819751456220290589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41803882546500970813527059 62705823819751456220290589)
            ·
              refine ⟨23514683932406796082608971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62705823819751456220290589 23514683932406796082608971)
              ·
                refine ⟨35272025898610194123913457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23514683932406796082608971 35272025898610194123913457)
                ·
                  refine ⟨26454019423957645592935093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35272025898610194123913457 26454019423957645592935093)
                  ·
                    refine ⟨2480064320996029274337665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 26454019423957645592935093 2480064320996029274337665)
                    ·
                      refine ⟨1860048240747021955753249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2480064320996029274337665 1860048240747021955753249)
                      ·
                        rfl

theorem cell23_3622431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 3, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 3, 1, 2, 5, 2].length) (baseStart_3622431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3622431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3622431 prefixEnd_3622431 := by exact prefixLift 3622431
  have htrace : WordTrace (prefixWord ++ tailWord_3622431) baseStart_3622431 baseEnd_3622431 := by
    simpa [prefixWord, tailWord_3622431, baseEnd_3622431] using wordTrace_append hprefix tailTrace_3622431
  have hstable : (prefixWord ++ tailWord_3622431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3622431).length < 2 ^ (prefixWord ++ tailWord_3622431).sum := by decide
  have hdescent : baseEnd_3622431 < baseStart_3622431 := by decide
  rcases family_descends (prefixWord ++ tailWord_3622431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3622474 : List Nat := [3, 1, 2, 1, 1, 3, 1, 1, 1, 3, 6]
def baseStart_3622474 : Nat := 118140960795 + 3622474 * 2 ^ 59
def prefixEnd_3622474 : Nat := 4983230072969 + 3 ^ 40 * 3622474 * 2
def baseEnd_3622474 : Nat := 1860070320415165287515551

theorem tailTrace_3622474 : CollatzResearch.WordTrace tailWord_3622474 prefixEnd_3622474 1860070320415165287515551 := by
  unfold tailWord_3622474
  simp only [CollatzResearch.WordTrace]
  refine ⟨33030620269600710537382619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88081654052268561433020317 33030620269600710537382619)
  ·
    refine ⟨49545930404401065806073929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33030620269600710537382619 49545930404401065806073929)
    ·
      refine ⟨37159447803300799354555447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49545930404401065806073929 37159447803300799354555447)
      ·
        refine ⟨55739171704951199031833171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37159447803300799354555447 55739171704951199031833171)
        ·
          refine ⟨83608757557426798547749757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55739171704951199031833171 83608757557426798547749757)
          ·
            refine ⟨31353284084035049455406159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 83608757557426798547749757 31353284084035049455406159)
            ·
              refine ⟨47029926126052574183109239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31353284084035049455406159 47029926126052574183109239)
              ·
                refine ⟨70544889189078861274663859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47029926126052574183109239 70544889189078861274663859)
                ·
                  refine ⟨105817333783618291911995789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 70544889189078861274663859 105817333783618291911995789)
                  ·
                    refine ⟨39681500168856859466998421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 105817333783618291911995789 39681500168856859466998421)
                    ·
                      refine ⟨1860070320415165287515551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 39681500168856859466998421 1860070320415165287515551)
                      ·
                        rfl

theorem cell23_3622474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 1, 1, 3, 6].length) (baseStart_3622474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3622474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3622474 prefixEnd_3622474 := by exact prefixLift 3622474
  have htrace : WordTrace (prefixWord ++ tailWord_3622474) baseStart_3622474 baseEnd_3622474 := by
    simpa [prefixWord, tailWord_3622474, baseEnd_3622474] using wordTrace_append hprefix tailTrace_3622474
  have hstable : (prefixWord ++ tailWord_3622474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3622474).length < 2 ^ (prefixWord ++ tailWord_3622474).sum := by decide
  have hdescent : baseEnd_3622474 < baseStart_3622474 := by decide
  rcases family_descends (prefixWord ++ tailWord_3622474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3622481 : List Nat := [1, 2, 2, 1, 3, 2, 2, 1, 4, 2, 3]
def baseStart_3622481 : Nat := 118140960795 + 3622481 * 2 ^ 59
def prefixEnd_3622481 : Nat := 4983230072969 + 3 ^ 40 * 3622481 * 2
def baseEnd_3622481 : Nat := 1860073914779746760128019

theorem tailTrace_3622481 : CollatzResearch.WordTrace tailWord_3622481 prefixEnd_3622481 1860073914779746760128019 := by
  unfold tailWord_3622481
  simp only [CollatzResearch.WordTrace]
  refine ⟨132122736389377482345035297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88081824259584988230023531 132122736389377482345035297)
  ·
    refine ⟨99092052292033111758776473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132122736389377482345035297 99092052292033111758776473)
    ·
      refine ⟨74319039219024833819082355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99092052292033111758776473 74319039219024833819082355)
      ·
        refine ⟨111478558828537250728623533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74319039219024833819082355 111478558828537250728623533)
        ·
          refine ⟨41804459560701469023233825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 111478558828537250728623533 41804459560701469023233825)
          ·
            refine ⟨31353344670526101767425369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41804459560701469023233825 31353344670526101767425369)
            ·
              refine ⟨23515008502894576325569027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31353344670526101767425369 23515008502894576325569027)
              ·
                refine ⟨35272512754341864488353541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23515008502894576325569027 35272512754341864488353541)
                ·
                  refine ⟨6613596141439099591566289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35272512754341864488353541 6613596141439099591566289)
                  ·
                    refine ⟨4960197106079324693674717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6613596141439099591566289 4960197106079324693674717)
                    ·
                      refine ⟨1860073914779746760128019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4960197106079324693674717 1860073914779746760128019)
                      ·
                        rfl

theorem cell23_3622481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 2, 1, 4, 2, 3].length) (baseStart_3622481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3622481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3622481 prefixEnd_3622481 := by exact prefixLift 3622481
  have htrace : WordTrace (prefixWord ++ tailWord_3622481) baseStart_3622481 baseEnd_3622481 := by
    simpa [prefixWord, tailWord_3622481, baseEnd_3622481] using wordTrace_append hprefix tailTrace_3622481
  have hstable : (prefixWord ++ tailWord_3622481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3622481).length < 2 ^ (prefixWord ++ tailWord_3622481).sum := by decide
  have hdescent : baseEnd_3622481 < baseStart_3622481 := by decide
  rcases family_descends (prefixWord ++ tailWord_3622481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3622588 : List Nat := [2, 2, 2, 3, 1, 2, 3, 1, 1, 1, 5]
def baseStart_3622588 : Nat := 118140960795 + 3622588 * 2 ^ 59
def prefixEnd_3622588 : Nat := 4983230072969 + 3 ^ 40 * 3622588 * 2
def baseEnd_3622588 : Nat := 1860128857209777841490027

theorem tailTrace_3622588 : CollatzResearch.WordTrace tailWord_3622588 prefixEnd_3622588 1860128857209777841490027 := by
  unfold tailWord_3622588
  simp only [CollatzResearch.WordTrace]
  refine ⟨66063319499994919809590209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88084425999993226412786945 66063319499994919809590209)
  ·
    refine ⟨49547489624996189857192657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66063319499994919809590209 49547489624996189857192657)
    ·
      refine ⟨37160617218747142392894493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49547489624996189857192657 37160617218747142392894493)
      ·
        refine ⟨13935231457030178397335435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37160617218747142392894493 13935231457030178397335435)
        ·
          refine ⟨20902847185545267596003153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13935231457030178397335435 20902847185545267596003153)
          ·
            refine ⟨15677135389158950697002365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20902847185545267596003153 15677135389158950697002365)
            ·
              refine ⟨5878925770934606511375887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15677135389158950697002365 5878925770934606511375887)
              ·
                refine ⟨8818388656401909767063831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5878925770934606511375887 8818388656401909767063831)
                ·
                  refine ⟨13227582984602864650595747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8818388656401909767063831 13227582984602864650595747)
                  ·
                    refine ⟨19841374476904296975893621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13227582984602864650595747 19841374476904296975893621)
                    ·
                      refine ⟨1860128857209777841490027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19841374476904296975893621 1860128857209777841490027)
                      ·
                        rfl

theorem cell23_3622588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 3, 1, 1, 1, 5].length) (baseStart_3622588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3622588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3622588 prefixEnd_3622588 := by exact prefixLift 3622588
  have htrace : WordTrace (prefixWord ++ tailWord_3622588) baseStart_3622588 baseEnd_3622588 := by
    simpa [prefixWord, tailWord_3622588, baseEnd_3622588] using wordTrace_append hprefix tailTrace_3622588
  have hstable : (prefixWord ++ tailWord_3622588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3622588).length < 2 ^ (prefixWord ++ tailWord_3622588).sum := by decide
  have hdescent : baseEnd_3622588 < baseStart_3622588 := by decide
  rcases family_descends (prefixWord ++ tailWord_3622588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3622618 : List Nat := [3, 1, 1, 2, 2, 3, 1, 3, 1, 3, 3]
def baseStart_3622618 : Nat := 118140960795 + 3622618 * 2 ^ 59
def prefixEnd_3622618 : Nat := 4983230072969 + 3 ^ 40 * 3622618 * 2
def baseEnd_3622618 : Nat := 1860144261629412724114889

theorem tailTrace_3622618 : CollatzResearch.WordTrace tailWord_3622618 prefixEnd_3622618 1860144261629412724114889 := by
  unfold tailWord_3622618
  simp only [CollatzResearch.WordTrace]
  refine ⟨33031933297470288685693127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88085155459920769828515005 33031933297470288685693127)
  ·
    refine ⟨49547899946205433028539691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33031933297470288685693127 49547899946205433028539691)
    ·
      refine ⟨74321849919308149542809537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49547899946205433028539691 74321849919308149542809537)
      ·
        refine ⟨55741387439481112157107153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74321849919308149542809537 55741387439481112157107153)
        ·
          refine ⟨41806040579610834117830365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55741387439481112157107153 41806040579610834117830365)
          ·
            refine ⟨15677265217354062794186387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41806040579610834117830365 15677265217354062794186387)
            ·
              refine ⟨23515897826031094191279581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15677265217354062794186387 23515897826031094191279581)
              ·
                refine ⟨8818461684761660321729843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23515897826031094191279581 8818461684761660321729843)
                ·
                  refine ⟨13227692527142490482594765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8818461684761660321729843 13227692527142490482594765)
                  ·
                    refine ⟨4960384697678433930973037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13227692527142490482594765 4960384697678433930973037)
                    ·
                      refine ⟨1860144261629412724114889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4960384697678433930973037 1860144261629412724114889)
                      ·
                        rfl

theorem cell23_3622618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 1, 3, 1, 3, 3].length) (baseStart_3622618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3622618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3622618 prefixEnd_3622618 := by exact prefixLift 3622618
  have htrace : WordTrace (prefixWord ++ tailWord_3622618) baseStart_3622618 baseEnd_3622618 := by
    simpa [prefixWord, tailWord_3622618, baseEnd_3622618] using wordTrace_append hprefix tailTrace_3622618
  have hstable : (prefixWord ++ tailWord_3622618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3622618).length < 2 ^ (prefixWord ++ tailWord_3622618).sum := by decide
  have hdescent : baseEnd_3622618 < baseStart_3622618 := by decide
  rcases family_descends (prefixWord ++ tailWord_3622618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3622661 : List Nat := [1, 3, 1, 1, 2, 1, 1, 1, 6, 1, 5]
def baseStart_3622661 : Nat := 118140960795 + 3622661 * 2 ^ 59
def prefixEnd_3622661 : Nat := 4983230072969 + 3 ^ 40 * 3622661 * 2
def baseEnd_3622661 : Nat := 1860166341297556055877191

theorem tailTrace_3622661 : CollatzResearch.WordTrace tailWord_3622661 prefixEnd_3622661 1860166341297556055877191 := by
  unfold tailWord_3622661
  simp only [CollatzResearch.WordTrace]
  refine ⟨132129301528725373086587837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88086201019150248724391891 132129301528725373086587837)
  ·
    refine ⟨49548488073272014907470439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 132129301528725373086587837 49548488073272014907470439)
    ·
      refine ⟨74322732109908022361205659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49548488073272014907470439 74322732109908022361205659)
      ·
        refine ⟨111484098164862033541808489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74322732109908022361205659 111484098164862033541808489)
        ·
          refine ⟨83613073623646525156356367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 111484098164862033541808489 83613073623646525156356367)
          ·
            refine ⟨125419610435469787734534551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83613073623646525156356367 125419610435469787734534551)
            ·
              refine ⟨188129415653204681601801827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 125419610435469787734534551 188129415653204681601801827)
              ·
                refine ⟨282194123479807022402702741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 188129415653204681601801827 282194123479807022402702741)
                ·
                  refine ⟨13227849538115954175126691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 282194123479807022402702741 13227849538115954175126691)
                  ·
                    refine ⟨19841774307173931262690037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13227849538115954175126691 19841774307173931262690037)
                    ·
                      refine ⟨1860166341297556055877191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19841774307173931262690037 1860166341297556055877191)
                      ·
                        rfl

theorem cell23_3622661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 1, 6, 1, 5].length) (baseStart_3622661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3622661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3622661 prefixEnd_3622661 := by exact prefixLift 3622661
  have htrace : WordTrace (prefixWord ++ tailWord_3622661) baseStart_3622661 baseEnd_3622661 := by
    simpa [prefixWord, tailWord_3622661, baseEnd_3622661] using wordTrace_append hprefix tailTrace_3622661
  have hstable : (prefixWord ++ tailWord_3622661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3622661).length < 2 ^ (prefixWord ++ tailWord_3622661).sum := by decide
  have hdescent : baseEnd_3622661 < baseStart_3622661 := by decide
  rcases family_descends (prefixWord ++ tailWord_3622661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3622671 : List Nat := [1, 1, 2, 1, 1, 1, 4, 3, 1, 4, 4]
def baseStart_3622671 : Nat := 118140960795 + 3622671 * 2 ^ 59
def prefixEnd_3622671 : Nat := 4983230072969 + 3 ^ 40 * 3622671 * 2
def baseEnd_3622671 : Nat := 1860171476104101016752145

theorem tailTrace_3622671 : CollatzResearch.WordTrace tailWord_3622671 prefixEnd_3622671 1860171476104101016752145 := by
  unfold tailWord_3622671
  simp only [CollatzResearch.WordTrace]
  refine ⟨132129666258689144794451867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88086444172459429862967911 132129666258689144794451867)
  ·
    refine ⟨198194499388033717191677801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132129666258689144794451867 198194499388033717191677801)
    ·
      refine ⟨148645874541025287893758351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 198194499388033717191677801 148645874541025287893758351)
      ·
        refine ⟨222968811811537931840637527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148645874541025287893758351 222968811811537931840637527)
        ·
          refine ⟨334453217717306897760956291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 222968811811537931840637527 334453217717306897760956291)
          ·
            refine ⟨501679826575960346641434437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 334453217717306897760956291 501679826575960346641434437)
            ·
              refine ⟨94064967482992564995268957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 501679826575960346641434437 94064967482992564995268957)
              ·
                refine ⟨35274362806122211873225859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 94064967482992564995268957 35274362806122211873225859)
                ·
                  refine ⟨52911544209183317809838789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35274362806122211873225859 52911544209183317809838789)
                  ·
                    refine ⟨9920914539221872089344773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 52911544209183317809838789 9920914539221872089344773)
                    ·
                      refine ⟨1860171476104101016752145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9920914539221872089344773 1860171476104101016752145)
                      ·
                        rfl

theorem cell23_3622671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 3, 1, 4, 4].length) (baseStart_3622671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3622671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3622671 prefixEnd_3622671 := by exact prefixLift 3622671
  have htrace : WordTrace (prefixWord ++ tailWord_3622671) baseStart_3622671 baseEnd_3622671 := by
    simpa [prefixWord, tailWord_3622671, baseEnd_3622671] using wordTrace_append hprefix tailTrace_3622671
  have hstable : (prefixWord ++ tailWord_3622671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3622671).length < 2 ^ (prefixWord ++ tailWord_3622671).sum := by decide
  have hdescent : baseEnd_3622671 < baseStart_3622671 := by decide
  rcases family_descends (prefixWord ++ tailWord_3622671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3622676 : List Nat := [2, 4, 4, 1, 2, 1, 2, 7]
def baseStart_3622676 : Nat := 118140960795 + 3622676 * 2 ^ 59
def prefixEnd_3622676 : Nat := 4983230072969 + 3 ^ 40 * 3622676 * 2
def baseEnd_3622676 : Nat := 68895334944717536932949

theorem tailTrace_3622676 : CollatzResearch.WordTrace tailWord_3622676 prefixEnd_3622676 68895334944717536932949 := by
  unfold tailWord_3622676
  simp only [CollatzResearch.WordTrace]
  refine ⟨66064924311835515324191941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88086565749114020432255921 66064924311835515324191941)
  ·
    refine ⟨12387173308469159123285989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 66064924311835515324191941 12387173308469159123285989)
    ·
      refine ⟨2322594995337967335616123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12387173308469159123285989 2322594995337967335616123)
      ·
        refine ⟨3483892493006951003424185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2322594995337967335616123 3483892493006951003424185)
        ·
          refine ⟨2612919369755213252568139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3483892493006951003424185 2612919369755213252568139)
          ·
            refine ⟨3919379054632819878852209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2612919369755213252568139 3919379054632819878852209)
            ·
              refine ⟨2939534290974614909139157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3919379054632819878852209 2939534290974614909139157)
              ·
                refine ⟨68895334944717536932949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2939534290974614909139157 68895334944717536932949)
                ·
                  rfl

theorem cell23_3622676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 2, 1, 2, 7].length) (baseStart_3622676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3622676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3622676 prefixEnd_3622676 := by exact prefixLift 3622676
  have htrace : WordTrace (prefixWord ++ tailWord_3622676) baseStart_3622676 baseEnd_3622676 := by
    simpa [prefixWord, tailWord_3622676, baseEnd_3622676] using wordTrace_append hprefix tailTrace_3622676
  have hstable : (prefixWord ++ tailWord_3622676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3622676).length < 2 ^ (prefixWord ++ tailWord_3622676).sum := by decide
  have hdescent : baseEnd_3622676 < baseStart_3622676 := by decide
  rcases family_descends (prefixWord ++ tailWord_3622676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3622692 : List Nat := [2, 3, 1, 3, 2, 1, 1, 2, 4, 2, 2]
def baseStart_3622692 : Nat := 118140960795 + 3622692 * 2 ^ 59
def prefixEnd_3622692 : Nat := 4983230072969 + 3 ^ 40 * 3622692 * 2
def baseEnd_3622692 : Nat := 1860182259197845434589549

theorem tailTrace_3622692 : CollatzResearch.WordTrace tailWord_3622692 prefixEnd_3622692 1860182259197845434589549 := by
  unfold tailWord_3622692
  simp only [CollatzResearch.WordTrace]
  refine ⟨66065216095806532690483165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88086954794408710253977553 66065216095806532690483165)
  ·
    refine ⟨24774456035927449758931187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66065216095806532690483165 24774456035927449758931187)
    ·
      refine ⟨37161684053891174638396781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24774456035927449758931187 37161684053891174638396781)
      ·
        refine ⟨13935631520209190489398793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37161684053891174638396781 13935631520209190489398793)
        ·
          refine ⟨10451723640156892867049095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13935631520209190489398793 10451723640156892867049095)
          ·
            refine ⟨15677585460235339300573643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10451723640156892867049095 15677585460235339300573643)
            ·
              refine ⟨23516378190353008950860465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15677585460235339300573643 23516378190353008950860465)
              ·
                refine ⟨17637283642764756713145349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23516378190353008950860465 17637283642764756713145349)
                ·
                  refine ⟨3306990683018391883714753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17637283642764756713145349 3306990683018391883714753)
                  ·
                    refine ⟨2480243012263793912786065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3306990683018391883714753 2480243012263793912786065)
                    ·
                      refine ⟨1860182259197845434589549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2480243012263793912786065 1860182259197845434589549)
                      ·
                        rfl

theorem cell23_3622692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 1, 2, 4, 2, 2].length) (baseStart_3622692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3622692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3622692 prefixEnd_3622692 := by exact prefixLift 3622692
  have htrace : WordTrace (prefixWord ++ tailWord_3622692) baseStart_3622692 baseEnd_3622692 := by
    simpa [prefixWord, tailWord_3622692, baseEnd_3622692] using wordTrace_append hprefix tailTrace_3622692
  have hstable : (prefixWord ++ tailWord_3622692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3622692).length < 2 ^ (prefixWord ++ tailWord_3622692).sum := by decide
  have hdescent : baseEnd_3622692 < baseStart_3622692 := by decide
  rcases family_descends (prefixWord ++ tailWord_3622692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3622711 : List Nat := [1, 1, 3, 1, 2, 1, 2, 2, 3, 7]
def baseStart_3622711 : Nat := 118140960795 + 3622711 * 2 ^ 59
def prefixEnd_3622711 : Nat := 4983230072969 + 3 ^ 40 * 3622711 * 2
def baseEnd_3622711 : Nat := 620064005110093620083987

theorem tailTrace_3622711 : CollatzResearch.WordTrace tailWord_3622711 prefixEnd_3622711 620064005110093620083987 := by
  unfold tailWord_3622711
  simp only [CollatzResearch.WordTrace]
  refine ⟨132131125178544231625907987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88087416785696154417271991 132131125178544231625907987)
  ·
    refine ⟨198196687767816347438861981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132131125178544231625907987 198196687767816347438861981)
    ·
      refine ⟨74323757912931130289573243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 198196687767816347438861981 74323757912931130289573243)
      ·
        refine ⟨111485636869396695434359865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74323757912931130289573243 111485636869396695434359865)
        ·
          refine ⟨83614227652047521575769899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 111485636869396695434359865 83614227652047521575769899)
          ·
            refine ⟨125421341478071282363654849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83614227652047521575769899 125421341478071282363654849)
            ·
              refine ⟨94066006108553461772741137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 125421341478071282363654849 94066006108553461772741137)
              ·
                refine ⟨70549504581415096329555853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 94066006108553461772741137 70549504581415096329555853)
                ·
                  refine ⟨26456064218030661123583445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 70549504581415096329555853 26456064218030661123583445)
                  ·
                    refine ⟨620064005110093620083987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 26456064218030661123583445 620064005110093620083987)
                    ·
                      rfl

theorem cell23_3622711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 2, 3, 7].length) (baseStart_3622711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3622711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3622711 prefixEnd_3622711 := by exact prefixLift 3622711
  have htrace : WordTrace (prefixWord ++ tailWord_3622711) baseStart_3622711 baseEnd_3622711 := by
    simpa [prefixWord, tailWord_3622711, baseEnd_3622711] using wordTrace_append hprefix tailTrace_3622711
  have hstable : (prefixWord ++ tailWord_3622711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3622711).length < 2 ^ (prefixWord ++ tailWord_3622711).sum := by decide
  have hdescent : baseEnd_3622711 < baseStart_3622711 := by decide
  rcases family_descends (prefixWord ++ tailWord_3622711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3622765 : List Nat := [1, 5, 1, 1, 1, 1, 4, 2, 2, 1, 4]
def baseStart_3622765 : Nat := 118140960795 + 3622765 * 2 ^ 59
def prefixEnd_3622765 : Nat := 4983230072969 + 3 ^ 40 * 3622765 * 2
def baseEnd_3622765 : Nat := 1860219743285623648976713

theorem tailTrace_3622765 : CollatzResearch.WordTrace tailWord_3622765 prefixEnd_3622765 1860219743285623648976713 := by
  unfold tailWord_3622765
  simp only [CollatzResearch.WordTrace]
  refine ⟨132133094720348598848373749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88088729813565732565582499 132133094720348598848373749)
  ·
    refine ⟨12387477630032681142035039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 132133094720348598848373749 12387477630032681142035039)
    ·
      refine ⟨18581216445049021713052559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12387477630032681142035039 18581216445049021713052559)
      ·
        refine ⟨27871824667573532569578839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18581216445049021713052559 27871824667573532569578839)
        ·
          refine ⟨41807737001360298854368259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27871824667573532569578839 41807737001360298854368259)
          ·
            refine ⟨62711605502040448281552389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41807737001360298854368259 62711605502040448281552389)
            ·
              refine ⟨11758426031632584052791073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 62711605502040448281552389 11758426031632584052791073)
              ·
                refine ⟨8818819523724438039593305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11758426031632584052791073 8818819523724438039593305)
                ·
                  refine ⟨6614114642793328529694979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8818819523724438039593305 6614114642793328529694979)
                  ·
                    refine ⟨9921171964189992794542469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6614114642793328529694979 9921171964189992794542469)
                    ·
                      refine ⟨1860219743285623648976713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9921171964189992794542469 1860219743285623648976713)
                      ·
                        rfl

theorem cell23_3622765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 4, 2, 2, 1, 4].length) (baseStart_3622765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3622765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3622765 prefixEnd_3622765 := by exact prefixLift 3622765
  have htrace : WordTrace (prefixWord ++ tailWord_3622765) baseStart_3622765 baseEnd_3622765 := by
    simpa [prefixWord, tailWord_3622765, baseEnd_3622765] using wordTrace_append hprefix tailTrace_3622765
  have hstable : (prefixWord ++ tailWord_3622765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3622765).length < 2 ^ (prefixWord ++ tailWord_3622765).sum := by decide
  have hdescent : baseEnd_3622765 < baseStart_3622765 := by decide
  rcases family_descends (prefixWord ++ tailWord_3622765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3622768 : List Nat := [2, 1, 1, 1, 4, 1, 1, 2, 3, 4, 3]
def baseStart_3622768 : Nat := 118140960795 + 3622768 * 2 ^ 59
def prefixEnd_3622768 : Nat := 4983230072969 + 3 ^ 40 * 3622768 * 2
def baseEnd_3622768 : Nat := 1860221283727587137239199

theorem tailTrace_3622768 : CollatzResearch.WordTrace tailWord_3622768 prefixEnd_3622768 1860221283727587137239199 := by
  unfold tailWord_3622768
  simp only [CollatzResearch.WordTrace]
  refine ⟨66066602069668865180366479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88088802759558486907155305 66066602069668865180366479)
  ·
    refine ⟨99099903104503297770549719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66066602069668865180366479 99099903104503297770549719)
    ·
      refine ⟨148649854656754946655824579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99099903104503297770549719 148649854656754946655824579)
      ·
        refine ⟨222974781985132419983736869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148649854656754946655824579 222974781985132419983736869)
        ·
          refine ⟨41807771622212328746950663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 222974781985132419983736869 41807771622212328746950663)
          ·
            refine ⟨62711657433318493120425995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41807771622212328746950663 62711657433318493120425995)
            ·
              refine ⟨94067486149977739680638993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62711657433318493120425995 94067486149977739680638993)
              ·
                refine ⟨70550614612483304760479245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 94067486149977739680638993 70550614612483304760479245)
                ·
                  refine ⟨26456480479681239285179717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 70550614612483304760479245 26456480479681239285179717)
                  ·
                    refine ⟨4960590089940232365971197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26456480479681239285179717 4960590089940232365971197)
                    ·
                      refine ⟨1860221283727587137239199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4960590089940232365971197 1860221283727587137239199)
                      ·
                        rfl

theorem cell23_3622768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 2, 3, 4, 3].length) (baseStart_3622768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3622768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3622768 prefixEnd_3622768 := by exact prefixLift 3622768
  have htrace : WordTrace (prefixWord ++ tailWord_3622768) baseStart_3622768 baseEnd_3622768 := by
    simpa [prefixWord, tailWord_3622768, baseEnd_3622768] using wordTrace_append hprefix tailTrace_3622768
  have hstable : (prefixWord ++ tailWord_3622768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3622768).length < 2 ^ (prefixWord ++ tailWord_3622768).sum := by decide
  have hdescent : baseEnd_3622768 < baseStart_3622768 := by decide
  rcases family_descends (prefixWord ++ tailWord_3622768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3622792 : List Nat := [2, 1, 3, 3, 3, 1, 1, 2, 3, 4]
def baseStart_3622792 : Nat := 118140960795 + 3622792 * 2 ^ 59
def prefixEnd_3622792 : Nat := 4983230072969 + 3 ^ 40 * 3622792 * 2
def baseEnd_3622792 : Nat := 620077869087765014446363

theorem tailTrace_3622792 : CollatzResearch.WordTrace tailWord_3622792 prefixEnd_3622792 620077869087765014446363 := by
  unfold tailWord_3622792
  simp only [CollatzResearch.WordTrace]
  refine ⟨66067039745625391229803315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88089386327500521639737753 66067039745625391229803315)
  ·
    refine ⟨99100559618438086844704973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66067039745625391229803315 99100559618438086844704973)
    ·
      refine ⟨37162709856914282566764365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 99100559618438086844704973 37162709856914282566764365)
      ·
        refine ⟨13936016196342855962536637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37162709856914282566764365 13936016196342855962536637)
        ·
          refine ⟨5226006073628570985951239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13936016196342855962536637 5226006073628570985951239)
          ·
            refine ⟨7839009110442856478926859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5226006073628570985951239 7839009110442856478926859)
            ·
              refine ⟨11758513665664284718390289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7839009110442856478926859 11758513665664284718390289)
              ·
                refine ⟨8818885249248213538792717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11758513665664284718390289 8818885249248213538792717)
                ·
                  refine ⟨3307081968468080077047269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8818885249248213538792717 3307081968468080077047269)
                  ·
                    refine ⟨620077869087765014446363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3307081968468080077047269 620077869087765014446363)
                    ·
                      rfl

theorem cell23_3622792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 1, 2, 3, 4].length) (baseStart_3622792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3622792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3622792 prefixEnd_3622792 := by exact prefixLift 3622792
  have htrace : WordTrace (prefixWord ++ tailWord_3622792) baseStart_3622792 baseEnd_3622792 := by
    simpa [prefixWord, tailWord_3622792, baseEnd_3622792] using wordTrace_append hprefix tailTrace_3622792
  have hstable : (prefixWord ++ tailWord_3622792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3622792).length < 2 ^ (prefixWord ++ tailWord_3622792).sum := by decide
  have hdescent : baseEnd_3622792 < baseStart_3622792 := by decide
  rcases family_descends (prefixWord ++ tailWord_3622792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3622802 : List Nat := [3, 2, 3, 2, 1, 2, 1, 1, 1, 4, 3]
def baseStart_3622802 : Nat := 118140960795 + 3622802 * 2 ^ 59
def prefixEnd_3622802 : Nat := 4983230072969 + 3 ^ 40 * 3622802 * 2
def baseEnd_3622802 : Nat := 1860238742069840004214043

theorem tailTrace_3622802 : CollatzResearch.WordTrace tailWord_3622802 prefixEnd_3622802 1860238742069840004214043 := by
  unfold tailWord_3622802
  simp only [CollatzResearch.WordTrace]
  refine ⟨33033611055303638541867665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88089629480809702778313773 33033611055303638541867665)
  ·
    refine ⟨24775208291477728906400749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33033611055303638541867665 24775208291477728906400749)
    ·
      refine ⟨9290703109304148339900281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24775208291477728906400749 9290703109304148339900281)
      ·
        refine ⟨6968027331978111254925211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9290703109304148339900281 6968027331978111254925211)
        ·
          refine ⟨10452040997967166882387817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6968027331978111254925211 10452040997967166882387817)
          ·
            refine ⟨7839030748475375161790863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10452040997967166882387817 7839030748475375161790863)
            ·
              refine ⟨11758546122713062742686295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7839030748475375161790863 11758546122713062742686295)
              ·
                refine ⟨17637819184069594114029443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11758546122713062742686295 17637819184069594114029443)
                ·
                  refine ⟨26456728776104391171044165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17637819184069594114029443 26456728776104391171044165)
                  ·
                    refine ⟨4960636645519573344570781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26456728776104391171044165 4960636645519573344570781)
                    ·
                      refine ⟨1860238742069840004214043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4960636645519573344570781 1860238742069840004214043)
                      ·
                        rfl

theorem cell23_3622802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 1, 1, 1, 4, 3].length) (baseStart_3622802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3622802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3622802 prefixEnd_3622802 := by exact prefixLift 3622802
  have htrace : WordTrace (prefixWord ++ tailWord_3622802) baseStart_3622802 baseEnd_3622802 := by
    simpa [prefixWord, tailWord_3622802, baseEnd_3622802] using wordTrace_append hprefix tailTrace_3622802
  have hstable : (prefixWord ++ tailWord_3622802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3622802).length < 2 ^ (prefixWord ++ tailWord_3622802).sum := by decide
  have hdescent : baseEnd_3622802 < baseStart_3622802 := by decide
  rcases family_descends (prefixWord ++ tailWord_3622802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3622855 : List Nat := [1, 1, 4, 1, 1, 2, 1, 1, 1, 8, 2]
def baseStart_3622855 : Nat := 118140960795 + 3622855 * 2 ^ 59
def prefixEnd_3622855 : Nat := 4983230072969 + 3 ^ 40 * 3622855 * 2
def baseEnd_3622855 : Nat := 1860265956544528296851299

theorem tailTrace_3622855 : CollatzResearch.WordTrace tailWord_3622855 prefixEnd_3622855 1860265956544528296851299 := by
  unfold tailWord_3622855
  simp only [CollatzResearch.WordTrace]
  refine ⟨132136377290022544219150019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88090918193348362812766679 132136377290022544219150019)
  ·
    refine ⟨198204565935033816328725029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132136377290022544219150019 198204565935033816328725029)
    ·
      refine ⟨37163356112818840561635943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 198204565935033816328725029 37163356112818840561635943)
      ·
        refine ⟨55745034169228260842453915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37163356112818840561635943 55745034169228260842453915)
        ·
          refine ⟨83617551253842391263680873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55745034169228260842453915 83617551253842391263680873)
          ·
            refine ⟨62713163440381793447760655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83617551253842391263680873 62713163440381793447760655)
            ·
              refine ⟨94069745160572690171640983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62713163440381793447760655 94069745160572690171640983)
              ·
                refine ⟨141104617740859035257461475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 94069745160572690171640983 141104617740859035257461475)
                ·
                  refine ⟨211656926611288552886192213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 141104617740859035257461475 211656926611288552886192213)
                  ·
                    refine ⟨2480354608726037729135065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 211656926611288552886192213 2480354608726037729135065)
                    ·
                      refine ⟨1860265956544528296851299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2480354608726037729135065 1860265956544528296851299)
                      ·
                        rfl

theorem cell23_3622855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 1, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 1, 1, 8, 2].length) (baseStart_3622855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3622855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3622855 prefixEnd_3622855 := by exact prefixLift 3622855
  have htrace : WordTrace (prefixWord ++ tailWord_3622855) baseStart_3622855 baseEnd_3622855 := by
    simpa [prefixWord, tailWord_3622855, baseEnd_3622855] using wordTrace_append hprefix tailTrace_3622855
  have hstable : (prefixWord ++ tailWord_3622855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3622855).length < 2 ^ (prefixWord ++ tailWord_3622855).sum := by decide
  have hdescent : baseEnd_3622855 < baseStart_3622855 := by decide
  rcases family_descends (prefixWord ++ tailWord_3622855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3622928 : List Nat := [2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 8]
def baseStart_3622928 : Nat := 118140960795 + 3622928 * 2 ^ 59
def prefixEnd_3622928 : Nat := 4983230072969 + 3 ^ 40 * 3622928 * 2
def baseEnd_3622928 : Nat := 1860303440632306511238463

theorem tailTrace_3622928 : CollatzResearch.WordTrace tailWord_3622928 prefixEnd_3622928 1860303440632306511238463 := by
  unfold tailWord_3622928
  simp only [CollatzResearch.WordTrace]
  refine ⟨66069519909379038843278719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88092693212505385124371625 66069519909379038843278719)
  ·
    refine ⟨99104279864068558264918079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66069519909379038843278719 99104279864068558264918079)
    ·
      refine ⟨148656419796102837397377119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99104279864068558264918079 148656419796102837397377119)
      ·
        refine ⟨222984629694154256096065679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148656419796102837397377119 222984629694154256096065679)
        ·
          refine ⟨334476944541231384144098519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 222984629694154256096065679 334476944541231384144098519)
          ·
            refine ⟨501715416811847076216147779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 334476944541231384144098519 501715416811847076216147779)
            ·
              refine ⟨752573125217770614324221669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 501715416811847076216147779 752573125217770614324221669)
              ·
                refine ⟨141107460978331990185791563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 752573125217770614324221669 141107460978331990185791563)
                ·
                  refine ⟨211661191467497985278687345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 141107460978331990185791563 211661191467497985278687345)
                  ·
                    refine ⟨158745893600623488959015509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 211661191467497985278687345 158745893600623488959015509)
                    ·
                      refine ⟨1860303440632306511238463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 158745893600623488959015509 1860303440632306511238463)
                      ·
                        rfl

theorem cell23_3622928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 8].length) (baseStart_3622928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3622928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3622928 prefixEnd_3622928 := by exact prefixLift 3622928
  have htrace : WordTrace (prefixWord ++ tailWord_3622928) baseStart_3622928 baseEnd_3622928 := by
    simpa [prefixWord, tailWord_3622928, baseEnd_3622928] using wordTrace_append hprefix tailTrace_3622928
  have hstable : (prefixWord ++ tailWord_3622928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3622928).length < 2 ^ (prefixWord ++ tailWord_3622928).sum := by decide
  have hdescent : baseEnd_3622928 < baseStart_3622928 := by decide
  rcases family_descends (prefixWord ++ tailWord_3622928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3622940 : List Nat := [2, 2, 3, 1, 3, 3, 2, 2, 1, 2, 2]
def baseStart_3622940 : Nat := 118140960795 + 3622940 * 2 ^ 59
def prefixEnd_3622940 : Nat := 4983230072969 + 3 ^ 40 * 3622940 * 2
def baseEnd_3622940 : Nat := 1860309602400160464288409

theorem tailTrace_3622940 : CollatzResearch.WordTrace tailWord_3622940 prefixEnd_3622940 1860309602400160464288409 := by
  unfold tailWord_3622940
  simp only [CollatzResearch.WordTrace]
  refine ⟨66069738747357301867997137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88092984996476402490662849 66069738747357301867997137)
  ·
    refine ⟨49552304060517976400997853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66069738747357301867997137 49552304060517976400997853)
    ·
      refine ⟨18582114022694241150374195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49552304060517976400997853 18582114022694241150374195)
      ·
        refine ⟨27873171034041361725561293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18582114022694241150374195 27873171034041361725561293)
        ·
          refine ⟨10452439137765510647085485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27873171034041361725561293 10452439137765510647085485)
          ·
            refine ⟨3919664676662066492657057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10452439137765510647085485 3919664676662066492657057)
            ·
              refine ⟨2939748507496549869492793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3919664676662066492657057 2939748507496549869492793)
              ·
                refine ⟨2204811380622412402119595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2939748507496549869492793 2204811380622412402119595)
                ·
                  refine ⟨3307217070933618603179393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2204811380622412402119595 3307217070933618603179393)
                  ·
                    refine ⟨2480412803200213952384545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3307217070933618603179393 2480412803200213952384545)
                    ·
                      refine ⟨1860309602400160464288409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2480412803200213952384545 1860309602400160464288409)
                      ·
                        rfl

theorem cell23_3622940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 3, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 3, 2, 2, 1, 2, 2].length) (baseStart_3622940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3622940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3622940 prefixEnd_3622940 := by exact prefixLift 3622940
  have htrace : WordTrace (prefixWord ++ tailWord_3622940) baseStart_3622940 baseEnd_3622940 := by
    simpa [prefixWord, tailWord_3622940, baseEnd_3622940] using wordTrace_append hprefix tailTrace_3622940
  have hstable : (prefixWord ++ tailWord_3622940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3622940).length < 2 ^ (prefixWord ++ tailWord_3622940).sum := by decide
  have hdescent : baseEnd_3622940 < baseStart_3622940 := by decide
  rcases family_descends (prefixWord ++ tailWord_3622940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3622965 : List Nat := [1, 3, 3, 1, 1, 1, 2, 1, 4, 1, 5]
def baseStart_3622965 : Nat := 118140960795 + 3622965 * 2 ^ 59
def prefixEnd_3622965 : Nat := 4983230072969 + 3 ^ 40 * 3622965 * 2
def baseEnd_3622965 : Nat := 1860322439416522866475793

theorem tailTrace_3622965 : CollatzResearch.WordTrace tailWord_3622965 prefixEnd_3622965 1860322439416522866475793 := by
  unfold tailWord_3622965
  simp only [CollatzResearch.WordTrace]
  refine ⟨132140389319624033005654349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88093592879749355337102899 132140389319624033005654349)
  ·
    refine ⟨49552645994859012377120381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 132140389319624033005654349 49552645994859012377120381)
    ·
      refine ⟨18582242248072129641420143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49552645994859012377120381 18582242248072129641420143)
      ·
        refine ⟨27873363372108194462130215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18582242248072129641420143 27873363372108194462130215)
        ·
          refine ⟨41810045058162291693195323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27873363372108194462130215 41810045058162291693195323)
          ·
            refine ⟨62715067587243437539792985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41810045058162291693195323 62715067587243437539792985)
            ·
              refine ⟨47036300690432578154844739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62715067587243437539792985 47036300690432578154844739)
              ·
                refine ⟨70554451035648867232267109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47036300690432578154844739 70554451035648867232267109)
                ·
                  refine ⟨13228959569184162606050083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 70554451035648867232267109 13228959569184162606050083)
                  ·
                    refine ⟨19843439353776243909075125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13228959569184162606050083 19843439353776243909075125)
                    ·
                      refine ⟨1860322439416522866475793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19843439353776243909075125 1860322439416522866475793)
                      ·
                        rfl

theorem cell23_3622965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 1, 4, 1, 5].length) (baseStart_3622965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3622965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3622965 prefixEnd_3622965 := by exact prefixLift 3622965
  have htrace : WordTrace (prefixWord ++ tailWord_3622965) baseStart_3622965 baseEnd_3622965 := by
    simpa [prefixWord, tailWord_3622965, baseEnd_3622965] using wordTrace_append hprefix tailTrace_3622965
  have hstable : (prefixWord ++ tailWord_3622965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3622965).length < 2 ^ (prefixWord ++ tailWord_3622965).sum := by decide
  have hdescent : baseEnd_3622965 < baseStart_3622965 := by decide
  rcases family_descends (prefixWord ++ tailWord_3622965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3622966 : List Nat := [5, 1, 2, 1, 1, 1, 2, 4, 1, 3, 2]
def baseStart_3622966 : Nat := 118140960795 + 3622966 * 2 ^ 59
def prefixEnd_3622966 : Nat := 4983230072969 + 3 ^ 40 * 3622966 * 2
def baseEnd_3622966 : Nat := 1860322952897177362563289

theorem tailTrace_3622966 : CollatzResearch.WordTrace tailWord_3622966 prefixEnd_3622966 1860322952897177362563289 := by
  unfold tailWord_3622966
  simp only [CollatzResearch.WordTrace]
  refine ⟨8258776612038775636027547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 88093617195080273450960501 8258776612038775636027547)
  ·
    refine ⟨12388164918058163454041321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8258776612038775636027547 12388164918058163454041321)
    ·
      refine ⟨9291123688543622590530991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12388164918058163454041321 9291123688543622590530991)
      ·
        refine ⟨13936685532815433885796487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9291123688543622590530991 13936685532815433885796487)
        ·
          refine ⟨20905028299223150828694731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13936685532815433885796487 20905028299223150828694731)
          ·
            refine ⟨31357542448834726243042097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20905028299223150828694731 31357542448834726243042097)
            ·
              refine ⟨23518156836626044682281573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31357542448834726243042097 23518156836626044682281573)
              ·
                refine ⟨4409654406867383377927795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23518156836626044682281573 4409654406867383377927795)
                ·
                  refine ⟨6614481610301075066891693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4409654406867383377927795 6614481610301075066891693)
                  ·
                    refine ⟨2480430603862903150084385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6614481610301075066891693 2480430603862903150084385)
                    ·
                      refine ⟨1860322952897177362563289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2480430603862903150084385 1860322952897177362563289)
                      ·
                        rfl

theorem cell23_3622966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 2, 4, 1, 3, 2].length) (baseStart_3622966 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3622966 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3622966 prefixEnd_3622966 := by exact prefixLift 3622966
  have htrace : WordTrace (prefixWord ++ tailWord_3622966) baseStart_3622966 baseEnd_3622966 := by
    simpa [prefixWord, tailWord_3622966, baseEnd_3622966] using wordTrace_append hprefix tailTrace_3622966
  have hstable : (prefixWord ++ tailWord_3622966).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3622966).length < 2 ^ (prefixWord ++ tailWord_3622966).sum := by decide
  have hdescent : baseEnd_3622966 < baseStart_3622966 := by decide
  rcases family_descends (prefixWord ++ tailWord_3622966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3623002 : List Nat := [3, 1, 1, 2, 1, 1, 3, 6, 5]
def baseStart_3623002 : Nat := 118140960795 + 3623002 * 2 ^ 59
def prefixEnd_3623002 : Nat := 4983230072969 + 3 ^ 40 * 3623002 * 2
def baseEnd_3623002 : Nat := 206704604244526580190347

theorem tailTrace_3623002 : CollatzResearch.WordTrace tailWord_3623002 prefixEnd_3623002 206704604244526580190347 := by
  unfold tailWord_3623002
  simp only [CollatzResearch.WordTrace]
  refine ⟨33035434705122497081187815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88094492546993325549834173 33035434705122497081187815)
  ·
    refine ⟨49553152057683745621781723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33035434705122497081187815 49553152057683745621781723)
    ·
      refine ⟨74329728086525618432672585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49553152057683745621781723 74329728086525618432672585)
      ·
        refine ⟨55747296064894213824504439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74329728086525618432672585 55747296064894213824504439)
        ·
          refine ⟨83620944097341320736756659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55747296064894213824504439 83620944097341320736756659)
          ·
            refine ⟨125431416146011981105134989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83620944097341320736756659 125431416146011981105134989)
            ·
              refine ⟨47036781054754492914425621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 125431416146011981105134989 47036781054754492914425621)
              ·
                refine ⟨2204849111941616855363701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 47036781054754492914425621 2204849111941616855363701)
                ·
                  refine ⟨206704604244526580190347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2204849111941616855363701 206704604244526580190347)
                  ·
                    rfl

theorem cell23_3623002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 6, 5].length) (baseStart_3623002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3623002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3623002 prefixEnd_3623002 := by exact prefixLift 3623002
  have htrace : WordTrace (prefixWord ++ tailWord_3623002) baseStart_3623002 baseEnd_3623002 := by
    simpa [prefixWord, tailWord_3623002, baseEnd_3623002] using wordTrace_append hprefix tailTrace_3623002
  have hstable : (prefixWord ++ tailWord_3623002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3623002).length < 2 ^ (prefixWord ++ tailWord_3623002).sum := by decide
  have hdescent : baseEnd_3623002 < baseStart_3623002 := by decide
  rcases family_descends (prefixWord ++ tailWord_3623002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3623012 : List Nat := [2, 3, 1, 1, 2, 1, 4, 1, 2, 3, 3]
def baseStart_3623012 : Nat := 118140960795 + 3623012 * 2 ^ 59
def prefixEnd_3623012 : Nat := 4983230072969 + 3 ^ 40 * 3623012 * 2
def baseEnd_3623012 : Nat := 1860346573007284182588077

theorem tailTrace_3623012 : CollatzResearch.WordTrace tailWord_3623012 prefixEnd_3623012 1860346573007284182588077 := by
  unfold tailWord_3623012
  simp only [CollatzResearch.WordTrace]
  refine ⟨66071051775226880016307645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88094735700302506688410193 66071051775226880016307645)
  ·
    refine ⟨24776644415710080006115367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66071051775226880016307645 24776644415710080006115367)
    ·
      refine ⟨37164966623565120009173051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24776644415710080006115367 37164966623565120009173051)
      ·
        refine ⟨55747449935347680013759577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37164966623565120009173051 55747449935347680013759577)
        ·
          refine ⟨41810587451510760010319683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55747449935347680013759577 41810587451510760010319683)
          ·
            refine ⟨62715881177266140015479525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41810587451510760010319683 62715881177266140015479525)
            ·
              refine ⟨11759227720737401252902411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 62715881177266140015479525 11759227720737401252902411)
              ·
                refine ⟨17638841581106101879353617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11759227720737401252902411 17638841581106101879353617)
                ·
                  refine ⟨13229131185829576409515213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17638841581106101879353617 13229131185829576409515213)
                  ·
                    refine ⟨4960924194686091153568205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13229131185829576409515213 4960924194686091153568205)
                    ·
                      refine ⟨1860346573007284182588077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4960924194686091153568205 1860346573007284182588077)
                      ·
                        rfl

theorem cell23_3623012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 4, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 4, 1, 2, 3, 3].length) (baseStart_3623012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3623012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3623012 prefixEnd_3623012 := by exact prefixLift 3623012
  have htrace : WordTrace (prefixWord ++ tailWord_3623012) baseStart_3623012 baseEnd_3623012 := by
    simpa [prefixWord, tailWord_3623012, baseEnd_3623012] using wordTrace_append hprefix tailTrace_3623012
  have hstable : (prefixWord ++ tailWord_3623012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3623012).length < 2 ^ (prefixWord ++ tailWord_3623012).sum := by decide
  have hdescent : baseEnd_3623012 < baseStart_3623012 := by decide
  rcases family_descends (prefixWord ++ tailWord_3623012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3623013 : List Nat := [1, 3, 1, 3, 2, 3, 3, 1, 2, 2, 2]
def baseStart_3623013 : Nat := 118140960795 + 3623013 * 2 ^ 59
def prefixEnd_3623013 : Nat := 4983230072969 + 3 ^ 40 * 3623013 * 2
def baseEnd_3623013 : Nat := 1860347086487938678675573

theorem tailTrace_3623013 : CollatzResearch.WordTrace tailWord_3623013 prefixEnd_3623013 1860347086487938678675573 := by
  unfold tailWord_3623013
  simp only [CollatzResearch.WordTrace]
  refine ⟨132142140023450137203401693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88094760015633424802267795 132142140023450137203401693)
  ·
    refine ⟨49553302508793801451275635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 132142140023450137203401693 49553302508793801451275635)
    ·
      refine ⟨74329953763190702176913453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49553302508793801451275635 74329953763190702176913453)
      ·
        refine ⟨27873732661196513316342545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74329953763190702176913453 27873732661196513316342545)
        ·
          refine ⟨20905299495897384987256909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27873732661196513316342545 20905299495897384987256909)
          ·
            refine ⟨7839487310961519370221341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20905299495897384987256909 7839487310961519370221341)
            ·
              refine ⟨2939807741610569763833003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7839487310961519370221341 2939807741610569763833003)
              ·
                refine ⟨4409711612415854645749505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2939807741610569763833003 4409711612415854645749505)
                ·
                  refine ⟨3307283709311890984312129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4409711612415854645749505 3307283709311890984312129)
                  ·
                    refine ⟨2480462781983918238234097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3307283709311890984312129 2480462781983918238234097)
                    ·
                      refine ⟨1860347086487938678675573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2480462781983918238234097 1860347086487938678675573)
                      ·
                        rfl

theorem cell23_3623013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 3, 1, 2, 2, 2].length) (baseStart_3623013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3623013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3623013 prefixEnd_3623013 := by exact prefixLift 3623013
  have htrace : WordTrace (prefixWord ++ tailWord_3623013) baseStart_3623013 baseEnd_3623013 := by
    simpa [prefixWord, tailWord_3623013, baseEnd_3623013] using wordTrace_append hprefix tailTrace_3623013
  have hstable : (prefixWord ++ tailWord_3623013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3623013).length < 2 ^ (prefixWord ++ tailWord_3623013).sum := by decide
  have hdescent : baseEnd_3623013 < baseStart_3623013 := by decide
  rcases family_descends (prefixWord ++ tailWord_3623013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3623015 : List Nat := [1, 1, 5, 1, 1, 2, 1, 1, 3, 7]
def baseStart_3623015 : Nat := 118140960795 + 3623015 * 2 ^ 59
def prefixEnd_3623015 : Nat := 4983230072969 + 3 ^ 40 * 3623015 * 2
def baseEnd_3623015 : Nat := 620116037816415890283521

theorem tailTrace_3623015 : CollatzResearch.WordTrace tailWord_3623015 prefixEnd_3623015 620116037816415890283521 := by
  unfold tailWord_3623015
  simp only [CollatzResearch.WordTrace]
  refine ⟨132142212969442891544974499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88094808646295261029982999 132142212969442891544974499)
  ·
    refine ⟨198213319454164337317461749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132142212969442891544974499 198213319454164337317461749)
    ·
      refine ⟨18582498698827906623512039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 198213319454164337317461749 18582498698827906623512039)
      ·
        refine ⟨27873748048241859935268059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18582498698827906623512039 27873748048241859935268059)
        ·
          refine ⟨41810622072362789902902089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27873748048241859935268059 41810622072362789902902089)
          ·
            refine ⟨31357966554272092427176567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41810622072362789902902089 31357966554272092427176567)
            ·
              refine ⟨47036949831408138640764851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31357966554272092427176567 47036949831408138640764851)
              ·
                refine ⟨70555424747112207961147277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47036949831408138640764851 70555424747112207961147277)
                ·
                  refine ⟨26458284280167077985430229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 70555424747112207961147277 26458284280167077985430229)
                  ·
                    refine ⟨620116037816415890283521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 26458284280167077985430229 620116037816415890283521)
                    ·
                      rfl

theorem cell23_3623015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 1, 3, 7].length) (baseStart_3623015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3623015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3623015 prefixEnd_3623015 := by exact prefixLift 3623015
  have htrace : WordTrace (prefixWord ++ tailWord_3623015) baseStart_3623015 baseEnd_3623015 := by
    simpa [prefixWord, tailWord_3623015, baseEnd_3623015] using wordTrace_append hprefix tailTrace_3623015
  have hstable : (prefixWord ++ tailWord_3623015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3623015).length < 2 ^ (prefixWord ++ tailWord_3623015).sum := by decide
  have hdescent : baseEnd_3623015 < baseStart_3623015 := by decide
  rcases family_descends (prefixWord ++ tailWord_3623015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3623065 : List Nat := [1, 2, 1, 2, 1, 2, 1, 4, 2, 1, 6]
def baseStart_3623065 : Nat := 118140960795 + 3623065 * 2 ^ 59
def prefixEnd_3623065 : Nat := 4983230072969 + 3 ^ 40 * 3623065 * 2
def baseEnd_3623065 : Nat := 1860373787481972475225333

theorem tailTrace_3623065 : CollatzResearch.WordTrace tailWord_3623065 prefixEnd_3623065 1860373787481972475225333 := by
  unfold tailWord_3623065
  simp only [CollatzResearch.WordTrace]
  refine ⟨132144036619261750084294649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88096024412841166722863099 132144036619261750084294649)
  ·
    refine ⟨99108027464446312563220987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132144036619261750084294649 99108027464446312563220987)
    ·
      refine ⟨148662041196669468844831481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99108027464446312563220987 148662041196669468844831481)
      ·
        refine ⟨111496530897502101633623611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 148662041196669468844831481 111496530897502101633623611)
        ·
          refine ⟨167244796346253152450435417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111496530897502101633623611 167244796346253152450435417)
          ·
            refine ⟨125433597259689864337826563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 167244796346253152450435417 125433597259689864337826563)
            ·
              refine ⟨188150395889534796506739845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 125433597259689864337826563 188150395889534796506739845)
              ·
                refine ⟨35278199229287774345013721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 188150395889534796506739845 35278199229287774345013721)
                ·
                  refine ⟨26458649421965830758760291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35278199229287774345013721 26458649421965830758760291)
                  ·
                    refine ⟨39687974132948746138140437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26458649421965830758760291 39687974132948746138140437)
                    ·
                      refine ⟨1860373787481972475225333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 39687974132948746138140437 1860373787481972475225333)
                      ·
                        rfl

theorem cell23_3623065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 4, 2, 1, 6].length) (baseStart_3623065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3623065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3623065 prefixEnd_3623065 := by exact prefixLift 3623065
  have htrace : WordTrace (prefixWord ++ tailWord_3623065) baseStart_3623065 baseEnd_3623065 := by
    simpa [prefixWord, tailWord_3623065, baseEnd_3623065] using wordTrace_append hprefix tailTrace_3623065
  have hstable : (prefixWord ++ tailWord_3623065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3623065).length < 2 ^ (prefixWord ++ tailWord_3623065).sum := by decide
  have hdescent : baseEnd_3623065 < baseStart_3623065 := by decide
  rcases family_descends (prefixWord ++ tailWord_3623065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3623119 : List Nat := [1, 1, 2, 1, 1, 3, 4, 3, 3, 1, 3]
def baseStart_3623119 : Nat := 118140960795 + 3623119 * 2 ^ 59
def prefixEnd_3623119 : Nat := 4983230072969 + 3 ^ 40 * 3623119 * 2
def baseEnd_3623119 : Nat := 1860401515437315263950085

theorem tailTrace_3623119 : CollatzResearch.WordTrace tailWord_3623119 prefixEnd_3623119 1860401515437315263950085 := by
  unfold tailWord_3623119
  simp only [CollatzResearch.WordTrace]
  refine ⟨132146006161066117306760411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88097337440710744871173607 132146006161066117306760411)
  ·
    refine ⟨198219009241599175960140617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132146006161066117306760411 198219009241599175960140617)
    ·
      refine ⟨148664256931199381970105463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 198219009241599175960140617 148664256931199381970105463)
      ·
        refine ⟨222996385396799072955158195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148664256931199381970105463 222996385396799072955158195)
        ·
          refine ⟨334494578095198609432737293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 222996385396799072955158195 334494578095198609432737293)
          ·
            refine ⟨125435466785699478537276485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 334494578095198609432737293 125435466785699478537276485)
            ·
              refine ⟨23519150022318652225739341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 125435466785699478537276485 23519150022318652225739341)
              ·
                refine ⟨8819681258369494584652253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23519150022318652225739341 8819681258369494584652253)
                ·
                  refine ⟨3307380471888560469244595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8819681258369494584652253 3307380471888560469244595)
                  ·
                    refine ⟨4961070707832840703866893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3307380471888560469244595 4961070707832840703866893)
                    ·
                      refine ⟨1860401515437315263950085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4961070707832840703866893 1860401515437315263950085)
                      ·
                        rfl

theorem cell23_3623119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 4, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 4, 3, 3, 1, 3].length) (baseStart_3623119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3623119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3623119 prefixEnd_3623119 := by exact prefixLift 3623119
  have htrace : WordTrace (prefixWord ++ tailWord_3623119) baseStart_3623119 baseEnd_3623119 := by
    simpa [prefixWord, tailWord_3623119, baseEnd_3623119] using wordTrace_append hprefix tailTrace_3623119
  have hstable : (prefixWord ++ tailWord_3623119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3623119).length < 2 ^ (prefixWord ++ tailWord_3623119).sum := by decide
  have hdescent : baseEnd_3623119 < baseStart_3623119 := by decide
  rcases family_descends (prefixWord ++ tailWord_3623119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3623126 : List Nat := [5, 2, 1, 2, 1, 1, 2, 3, 6]
def baseStart_3623126 : Nat := 118140960795 + 3623126 * 2 ^ 59
def prefixEnd_3623126 : Nat := 4983230072969 + 3 ^ 40 * 3623126 * 2
def baseEnd_3623126 : Nat := 206711678866877415173617

theorem tailTrace_3623126 : CollatzResearch.WordTrace tailWord_3623126 prefixEnd_3623126 206711678866877415173617 := by
  unfold tailWord_3623126
  simp only [CollatzResearch.WordTrace]
  refine ⟨8259141342002547343891577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 88097507648027171668176821 8259141342002547343891577)
  ·
    refine ⟨6194356006501910507918683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8259141342002547343891577 6194356006501910507918683)
    ·
      refine ⟨9291534009752865761878025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6194356006501910507918683 9291534009752865761878025)
      ·
        refine ⟨6968650507314649321408519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9291534009752865761878025 6968650507314649321408519)
        ·
          refine ⟨10452975760971973982112779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6968650507314649321408519 10452975760971973982112779)
          ·
            refine ⟨15679463641457960973169169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10452975760971973982112779 15679463641457960973169169)
            ·
              refine ⟨11759597731093470729876877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15679463641457960973169169 11759597731093470729876877)
              ·
                refine ⟨4409849149160051523703829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11759597731093470729876877 4409849149160051523703829)
                ·
                  refine ⟨206711678866877415173617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4409849149160051523703829 206711678866877415173617)
                  ·
                    rfl

theorem cell23_3623126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 2, 3, 6].length) (baseStart_3623126 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3623126 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3623126 prefixEnd_3623126 := by exact prefixLift 3623126
  have htrace : WordTrace (prefixWord ++ tailWord_3623126) baseStart_3623126 baseEnd_3623126 := by
    simpa [prefixWord, tailWord_3623126, baseEnd_3623126] using wordTrace_append hprefix tailTrace_3623126
  have hstable : (prefixWord ++ tailWord_3623126).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3623126).length < 2 ^ (prefixWord ++ tailWord_3623126).sum := by decide
  have hdescent : baseEnd_3623126 < baseStart_3623126 := by decide
  rcases family_descends (prefixWord ++ tailWord_3623126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3623129 : List Nat := [1, 2, 1, 2, 3, 1, 2, 2, 4, 3, 2]
def baseStart_3623129 : Nat := 118140960795 + 3623129 * 2 ^ 59
def prefixEnd_3623129 : Nat := 4983230072969 + 3 ^ 40 * 3623129 * 2
def baseEnd_3623129 : Nat := 1860406650243860224825039

theorem tailTrace_3623129 : CollatzResearch.WordTrace tailWord_3623129 prefixEnd_3623129 1860406650243860224825039 := by
  unfold tailWord_3623129
  simp only [CollatzResearch.WordTrace]
  refine ⟨132146370891029889014624441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88097580594019926009749627 132146370891029889014624441)
  ·
    refine ⟨99109778168272416760968331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132146370891029889014624441 99109778168272416760968331)
    ·
      refine ⟨148664667252408625141452497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99109778168272416760968331 148664667252408625141452497)
      ·
        refine ⟨111498500439306468856089373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 148664667252408625141452497 111498500439306468856089373)
        ·
          refine ⟨41811937664739925821033515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 111498500439306468856089373 41811937664739925821033515)
          ·
            refine ⟨62717906497109888731550273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41811937664739925821033515 62717906497109888731550273)
            ·
              refine ⟨47038429872832416548662705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62717906497109888731550273 47038429872832416548662705)
              ·
                refine ⟨35278822404624312411497029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47038429872832416548662705 35278822404624312411497029)
                ·
                  refine ⟨6614779200867058577155693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35278822404624312411497029 6614779200867058577155693)
                  ·
                    refine ⟨2480542200325146966433385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6614779200867058577155693 2480542200325146966433385)
                    ·
                      refine ⟨1860406650243860224825039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2480542200325146966433385 1860406650243860224825039)
                      ·
                        rfl

theorem cell23_3623129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 2, 4, 3, 2].length) (baseStart_3623129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3623129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3623129 prefixEnd_3623129 := by exact prefixLift 3623129
  have htrace : WordTrace (prefixWord ++ tailWord_3623129) baseStart_3623129 baseEnd_3623129 := by
    simpa [prefixWord, tailWord_3623129, baseEnd_3623129] using wordTrace_append hprefix tailTrace_3623129
  have hstable : (prefixWord ++ tailWord_3623129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3623129).length < 2 ^ (prefixWord ++ tailWord_3623129).sum := by decide
  have hdescent : baseEnd_3623129 < baseStart_3623129 := by decide
  rcases family_descends (prefixWord ++ tailWord_3623129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3623169 : List Nat := [1, 2, 4, 1, 1, 2, 3, 1, 4, 4]
def baseStart_3623169 : Nat := 118140960795 + 3623169 * 2 ^ 59
def prefixEnd_3623169 : Nat := 4983230072969 + 3 ^ 40 * 3623169 * 2
def baseEnd_3623169 : Nat := 620142396490013356108285

theorem tailTrace_3623169 : CollatzResearch.WordTrace tailWord_3623169 prefixEnd_3623169 620142396490013356108285 := by
  unfold tailWord_3623169
  simp only [CollatzResearch.WordTrace]
  refine ⟨132147829810884975846080561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88098553207256650564053707 132147829810884975846080561)
  ·
    refine ⟨99110872358163731884560421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132147829810884975846080561 99110872358163731884560421)
    ·
      refine ⟨18583288567155699728355079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 99110872358163731884560421 18583288567155699728355079)
      ·
        refine ⟨27874932850733549592532619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18583288567155699728355079 27874932850733549592532619)
        ·
          refine ⟨41812399276100324388798929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27874932850733549592532619 41812399276100324388798929)
          ·
            refine ⟨31359299457075243291599197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41812399276100324388798929 31359299457075243291599197)
            ·
              refine ⟨11759737296403216234349699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31359299457075243291599197 11759737296403216234349699)
              ·
                refine ⟨17639605944604824351524549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11759737296403216234349699 17639605944604824351524549)
                ·
                  refine ⟨3307426114613404565910853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17639605944604824351524549 3307426114613404565910853)
                  ·
                    refine ⟨620142396490013356108285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3307426114613404565910853 620142396490013356108285)
                    ·
                      rfl

theorem cell23_3623169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 3, 1, 4, 4].length) (baseStart_3623169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3623169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3623169 prefixEnd_3623169 := by exact prefixLift 3623169
  have htrace : WordTrace (prefixWord ++ tailWord_3623169) baseStart_3623169 baseEnd_3623169 := by
    simpa [prefixWord, tailWord_3623169, baseEnd_3623169] using wordTrace_append hprefix tailTrace_3623169
  have hstable : (prefixWord ++ tailWord_3623169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3623169).length < 2 ^ (prefixWord ++ tailWord_3623169).sum := by decide
  have hdescent : baseEnd_3623169 < baseStart_3623169 := by decide
  rcases family_descends (prefixWord ++ tailWord_3623169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3623170 : List Nat := [3, 4, 1, 1, 2, 1, 2, 4, 1, 1, 3]
def baseStart_3623170 : Nat := 118140960795 + 3623170 * 2 ^ 59
def prefixEnd_3623170 : Nat := 4983230072969 + 3 ^ 40 * 3623170 * 2
def baseEnd_3623170 : Nat := 1860427702950694564412351

theorem tailTrace_3623170 : CollatzResearch.WordTrace tailWord_3623170 prefixEnd_3623170 1860427702950694564412351 := by
  unfold tailWord_3623170
  simp only [CollatzResearch.WordTrace]
  refine ⟨33036966570970338254216741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88098577522587568677911309 33036966570970338254216741)
  ·
    refine ⟨6194431232056938422665639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33036966570970338254216741 6194431232056938422665639)
    ·
      refine ⟨9291646848085407633998459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6194431232056938422665639 9291646848085407633998459)
      ·
        refine ⟨13937470272128111450997689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9291646848085407633998459 13937470272128111450997689)
        ·
          refine ⟨10453102704096083588248267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13937470272128111450997689 10453102704096083588248267)
          ·
            refine ⟨15679654056144125382372401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10453102704096083588248267 15679654056144125382372401)
            ·
              refine ⟨11759740542108094036779301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15679654056144125382372401 11759740542108094036779301)
              ·
                refine ⟨2204951351645267631896119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11759740542108094036779301 2204951351645267631896119)
                ·
                  refine ⟨3307427027467901447844179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2204951351645267631896119 3307427027467901447844179)
                  ·
                    refine ⟨4961140541201852171766269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3307427027467901447844179 4961140541201852171766269)
                    ·
                      refine ⟨1860427702950694564412351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4961140541201852171766269 1860427702950694564412351)
                      ·
                        rfl

theorem cell23_3623170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 2, 4, 1, 1, 3].length) (baseStart_3623170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3623170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3623170 prefixEnd_3623170 := by exact prefixLift 3623170
  have htrace : WordTrace (prefixWord ++ tailWord_3623170) baseStart_3623170 baseEnd_3623170 := by
    simpa [prefixWord, tailWord_3623170, baseEnd_3623170] using wordTrace_append hprefix tailTrace_3623170
  have hstable : (prefixWord ++ tailWord_3623170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3623170).length < 2 ^ (prefixWord ++ tailWord_3623170).sum := by decide
  have hdescent : baseEnd_3623170 < baseStart_3623170 := by decide
  rcases family_descends (prefixWord ++ tailWord_3623170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3623182 : List Nat := [4, 1, 1, 2, 1, 2, 2, 10]
def baseStart_3623182 : Nat := 118140960795 + 3623182 * 2 ^ 59
def prefixEnd_3623182 : Nat := 4983230072969 + 3 ^ 40 * 3623182 * 2
def baseEnd_3623182 : Nat := 68904957952538833980085

theorem tailTrace_3623182 : CollatzResearch.WordTrace tailWord_3623182 prefixEnd_3623182 68904957952538833980085 := by
  unfold tailWord_3623182
  simp only [CollatzResearch.WordTrace]
  refine ⟨16518537994979734883287975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 88098869306558586044202533 16518537994979734883287975)
  ·
    refine ⟨24777806992469602324931963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16518537994979734883287975 24777806992469602324931963)
    ·
      refine ⟨37166710488704403487397945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24777806992469602324931963 37166710488704403487397945)
      ·
        refine ⟨27875032866528302615548459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37166710488704403487397945 27875032866528302615548459)
        ·
          refine ⟨41812549299792453923322689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27875032866528302615548459 41812549299792453923322689)
          ·
            refine ⟨31359411974844340442492017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41812549299792453923322689 31359411974844340442492017)
            ·
              refine ⟨23519558981133255331869013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31359411974844340442492017 23519558981133255331869013)
              ·
                refine ⟨68904957952538833980085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 23519558981133255331869013 68904957952538833980085)
                ·
                  rfl

theorem cell23_3623182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 2, 10].length) (baseStart_3623182 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3623182 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3623182 prefixEnd_3623182 := by exact prefixLift 3623182
  have htrace : WordTrace (prefixWord ++ tailWord_3623182) baseStart_3623182 baseEnd_3623182 := by
    simpa [prefixWord, tailWord_3623182, baseEnd_3623182] using wordTrace_append hprefix tailTrace_3623182
  have hstable : (prefixWord ++ tailWord_3623182).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3623182).length < 2 ^ (prefixWord ++ tailWord_3623182).sum := by decide
  have hdescent : baseEnd_3623182 < baseStart_3623182 := by decide
  rcases family_descends (prefixWord ++ tailWord_3623182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3623189 : List Nat := [1, 3, 2, 1, 2, 1, 5, 1, 1, 2, 4]
def baseStart_3623189 : Nat := 118140960795 + 3623189 * 2 ^ 59
def prefixEnd_3623189 : Nat := 4983230072969 + 3 ^ 40 * 3623189 * 2
def baseEnd_3623189 : Nat := 1860437459083129990074763

theorem tailTrace_3623189 : CollatzResearch.WordTrace tailWord_3623189 prefixEnd_3623189 1860437459083129990074763 := by
  unfold tailWord_3623189
  simp only [CollatzResearch.WordTrace]
  refine ⟨132148559270812519261808621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88099039513875012841205747 132148559270812519261808621)
  ·
    refine ⟨49555709726554694723178233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 132148559270812519261808621 49555709726554694723178233)
    ·
      refine ⟨37166782294916021042383675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49555709726554694723178233 37166782294916021042383675)
      ·
        refine ⟨55750173442374031563575513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37166782294916021042383675 55750173442374031563575513)
        ·
          refine ⟨41812630081780523672681635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55750173442374031563575513 41812630081780523672681635)
          ·
            refine ⟨62718945122670785509022453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41812630081780523672681635 62718945122670785509022453)
            ·
              refine ⟨5879901105250386141470855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 62718945122670785509022453 5879901105250386141470855)
              ·
                refine ⟨8819851657875579212206283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5879901105250386141470855 8819851657875579212206283)
                ·
                  refine ⟨13229777486813368818309425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8819851657875579212206283 13229777486813368818309425)
                  ·
                    refine ⟨9922333115110026613732069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13229777486813368818309425 9922333115110026613732069)
                    ·
                      refine ⟨1860437459083129990074763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9922333115110026613732069 1860437459083129990074763)
                      ·
                        rfl

theorem cell23_3623189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 5, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 5, 1, 1, 2, 4].length) (baseStart_3623189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3623189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3623189 prefixEnd_3623189 := by exact prefixLift 3623189
  have htrace : WordTrace (prefixWord ++ tailWord_3623189) baseStart_3623189 baseEnd_3623189 := by
    simpa [prefixWord, tailWord_3623189, baseEnd_3623189] using wordTrace_append hprefix tailTrace_3623189
  have hstable : (prefixWord ++ tailWord_3623189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3623189).length < 2 ^ (prefixWord ++ tailWord_3623189).sum := by decide
  have hdescent : baseEnd_3623189 < baseStart_3623189 := by decide
  rcases family_descends (prefixWord ++ tailWord_3623189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3623199 : List Nat := [1, 1, 2, 4, 3, 1, 4, 7]
def baseStart_3623199 : Nat := 118140960795 + 3623199 * 2 ^ 59
def prefixEnd_3623199 : Nat := 4983230072969 + 3 ^ 40 * 3623199 * 2
def baseEnd_3623199 : Nat := 68905281255173146331471

theorem tailTrace_3623199 : CollatzResearch.WordTrace tailWord_3623199 prefixEnd_3623199 68905281255173146331471 := by
  unfold tailWord_3623199
  simp only [CollatzResearch.WordTrace]
  refine ⟨132148924000776290969672651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88099282667184193979781767 132148924000776290969672651)
  ·
    refine ⟨198223386001164436454508977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132148924000776290969672651 198223386001164436454508977)
    ·
      refine ⟨148667539500873327340881733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 198223386001164436454508977 148667539500873327340881733)
      ·
        refine ⟨27875163656413748876415325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 148667539500873327340881733 27875163656413748876415325)
        ·
          refine ⟨10453186371155155828655747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27875163656413748876415325 10453186371155155828655747)
          ·
            refine ⟨15679779556732733742983621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10453186371155155828655747 15679779556732733742983621)
            ·
              refine ⟨2939958666887387576809429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15679779556732733742983621 2939958666887387576809429)
              ·
                refine ⟨68905281255173146331471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2939958666887387576809429 68905281255173146331471)
                ·
                  rfl

theorem cell23_3623199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 4, 7].length) (baseStart_3623199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3623199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3623199 prefixEnd_3623199 := by exact prefixLift 3623199
  have htrace : WordTrace (prefixWord ++ tailWord_3623199) baseStart_3623199 baseEnd_3623199 := by
    simpa [prefixWord, tailWord_3623199, baseEnd_3623199] using wordTrace_append hprefix tailTrace_3623199
  have hstable : (prefixWord ++ tailWord_3623199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3623199).length < 2 ^ (prefixWord ++ tailWord_3623199).sum := by decide
  have hdescent : baseEnd_3623199 < baseStart_3623199 := by decide
  rcases family_descends (prefixWord ++ tailWord_3623199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3623213 : List Nat := [1, 5, 3, 1, 2, 1, 2, 1, 1, 1, 5]
def baseStart_3623213 : Nat := 118140960795 + 3623213 * 2 ^ 59
def prefixEnd_3623213 : Nat := 4983230072969 + 3 ^ 40 * 3623213 * 2
def baseEnd_3623213 : Nat := 1860449782618837896174653

theorem tailTrace_3623213 : CollatzResearch.WordTrace tailWord_3623213 prefixEnd_3623213 1860449782618837896174653 := by
  unfold tailWord_3623213
  simp only [CollatzResearch.WordTrace]
  refine ⟨132149434622725571360682293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88099623081817047573788195 132149434622725571360682293)
  ·
    refine ⟨12389009495880522315063965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 132149434622725571360682293 12389009495880522315063965)
    ·
      refine ⟨4645878560955195868148987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12389009495880522315063965 4645878560955195868148987)
      ·
        refine ⟨6968817841432793802223481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4645878560955195868148987 6968817841432793802223481)
        ·
          refine ⟨5226613381074595351667611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6968817841432793802223481 5226613381074595351667611)
          ·
            refine ⟨7839920071611893027501417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5226613381074595351667611 7839920071611893027501417)
            ·
              refine ⟨5879940053708919770626063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7839920071611893027501417 5879940053708919770626063)
              ·
                refine ⟨8819910080563379655939095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5879940053708919770626063 8819910080563379655939095)
                ·
                  refine ⟨13229865120845069483908643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8819910080563379655939095 13229865120845069483908643)
                  ·
                    refine ⟨19844797681267604225862965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13229865120845069483908643 19844797681267604225862965)
                    ·
                      refine ⟨1860449782618837896174653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19844797681267604225862965 1860449782618837896174653)
                      ·
                        rfl

theorem cell23_3623213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 2, 1, 1, 1, 5].length) (baseStart_3623213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3623213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3623213 prefixEnd_3623213 := by exact prefixLift 3623213
  have htrace : WordTrace (prefixWord ++ tailWord_3623213) baseStart_3623213 baseEnd_3623213 := by
    simpa [prefixWord, tailWord_3623213, baseEnd_3623213] using wordTrace_append hprefix tailTrace_3623213
  have hstable : (prefixWord ++ tailWord_3623213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3623213).length < 2 ^ (prefixWord ++ tailWord_3623213).sum := by decide
  have hdescent : baseEnd_3623213 < baseStart_3623213 := by decide
  rcases family_descends (prefixWord ++ tailWord_3623213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3623226 : List Nat := [3, 1, 1, 1, 4, 2, 2, 1, 4, 1, 3]
def baseStart_3623226 : Nat := 118140960795 + 3623226 * 2 ^ 59
def prefixEnd_3623226 : Nat := 4983230072969 + 3 ^ 40 * 3623226 * 2
def baseEnd_3623226 : Nat := 1860456457867346345312093

theorem tailTrace_3623226 : CollatzResearch.WordTrace tailWord_3623226 prefixEnd_3623226 1860456457867346345312093 := by
  unfold tailWord_3623226
  simp only [CollatzResearch.WordTrace]
  refine ⟨33037477192919618645226383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88099939181118983053937021 33037477192919618645226383)
  ·
    refine ⟨49556215789379427967839575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33037477192919618645226383 49556215789379427967839575)
    ·
      refine ⟨74334323684069141951759363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49556215789379427967839575 74334323684069141951759363)
      ·
        refine ⟨111501485526103712927639045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74334323684069141951759363 111501485526103712927639045)
        ·
          refine ⟨20906528536144446173932321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 111501485526103712927639045 20906528536144446173932321)
          ·
            refine ⟨15679896402108334630449241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20906528536144446173932321 15679896402108334630449241)
            ·
              refine ⟨11759922301581250972836931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15679896402108334630449241 11759922301581250972836931)
              ·
                refine ⟨17639883452371876459255397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11759922301581250972836931 17639883452371876459255397)
                ·
                  refine ⟨3307478147319726836110387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17639883452371876459255397 3307478147319726836110387)
                  ·
                    refine ⟨4961217220979590254165581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3307478147319726836110387 4961217220979590254165581)
                    ·
                      refine ⟨1860456457867346345312093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4961217220979590254165581 1860456457867346345312093)
                      ·
                        rfl

theorem cell23_3623226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 2, 1, 4, 1, 3].length) (baseStart_3623226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3623226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3623226 prefixEnd_3623226 := by exact prefixLift 3623226
  have htrace : WordTrace (prefixWord ++ tailWord_3623226) baseStart_3623226 baseEnd_3623226 := by
    simpa [prefixWord, tailWord_3623226, baseEnd_3623226] using wordTrace_append hprefix tailTrace_3623226
  have hstable : (prefixWord ++ tailWord_3623226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3623226).length < 2 ^ (prefixWord ++ tailWord_3623226).sum := by decide
  have hdescent : baseEnd_3623226 < baseStart_3623226 := by decide
  rcases family_descends (prefixWord ++ tailWord_3623226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3623253 : List Nat := [1, 3, 2, 2, 4, 1, 1, 1, 3, 3, 2]
def baseStart_3623253 : Nat := 118140960795 + 3623253 * 2 ^ 59
def prefixEnd_3623253 : Nat := 4983230072969 + 3 ^ 40 * 3623253 * 2
def baseEnd_3623253 : Nat := 1860470321845017739674469

theorem tailTrace_3623253 : CollatzResearch.WordTrace tailWord_3623253 prefixEnd_3623253 1860470321845017739674469 := by
  unfold tailWord_3623253
  simp only [CollatzResearch.WordTrace]
  refine ⟨132150893542580658192138413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88100595695053772128092275 132150893542580658192138413)
  ·
    refine ⟨49556585078467746822051905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 132150893542580658192138413 49556585078467746822051905)
    ·
      refine ⟨37167438808850810116538929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49556585078467746822051905 37167438808850810116538929)
      ·
        refine ⟨27875579106638107587404197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37167438808850810116538929 27875579106638107587404197)
        ·
          refine ⟨5226671082494645172638287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27875579106638107587404197 5226671082494645172638287)
          ·
            refine ⟨7840006623741967758957431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5226671082494645172638287 7840006623741967758957431)
            ·
              refine ⟨11760009935612951638436147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7840006623741967758957431 11760009935612951638436147)
              ·
                refine ⟨17640014903419427457654221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11760009935612951638436147 17640014903419427457654221)
                ·
                  refine ⟨6615005588782285296620333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17640014903419427457654221 6615005588782285296620333)
                  ·
                    refine ⟨2480627095793356986232625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6615005588782285296620333 2480627095793356986232625)
                    ·
                      refine ⟨1860470321845017739674469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2480627095793356986232625 1860470321845017739674469)
                      ·
                        rfl

theorem cell23_3623253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 1, 1, 3, 3, 2].length) (baseStart_3623253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3623253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3623253 prefixEnd_3623253 := by exact prefixLift 3623253
  have htrace : WordTrace (prefixWord ++ tailWord_3623253) baseStart_3623253 baseEnd_3623253 := by
    simpa [prefixWord, tailWord_3623253, baseEnd_3623253] using wordTrace_append hprefix tailTrace_3623253
  have hstable : (prefixWord ++ tailWord_3623253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3623253).length < 2 ^ (prefixWord ++ tailWord_3623253).sum := by decide
  have hdescent : baseEnd_3623253 < baseStart_3623253 := by decide
  rcases family_descends (prefixWord ++ tailWord_3623253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3623269 : List Nat := [1, 3, 1, 3, 1, 3, 2, 1, 2, 1, 5]
def baseStart_3623269 : Nat := 118140960795 + 3623269 * 2 ^ 59
def prefixEnd_3623269 : Nat := 4983230072969 + 3 ^ 40 * 3623269 * 2
def baseEnd_3623269 : Nat := 1860478537535489677074395

theorem tailTrace_3623269 : CollatzResearch.WordTrace tailWord_3623269 prefixEnd_3623269 1860478537535489677074395 := by
  unfold tailWord_3623269
  simp only [CollatzResearch.WordTrace]
  refine ⟨132151477110522692924720861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88100984740348461949813907 132151477110522692924720861)
  ·
    refine ⟨49556803916446009846770323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 132151477110522692924720861 49556803916446009846770323)
    ·
      refine ⟨74335205874669014770155485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49556803916446009846770323 74335205874669014770155485)
      ·
        refine ⟨27875702203000880538808307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74335205874669014770155485 27875702203000880538808307)
        ·
          refine ⟨41813553304501320808212461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27875702203000880538808307 41813553304501320808212461)
          ·
            refine ⟨15680082489187995303079673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41813553304501320808212461 15680082489187995303079673)
            ·
              refine ⟨11760061866890996477309755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15680082489187995303079673 11760061866890996477309755)
              ·
                refine ⟨17640092800336494715964633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11760061866890996477309755 17640092800336494715964633)
                ·
                  refine ⟨13230069600252371036973475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17640092800336494715964633 13230069600252371036973475)
                  ·
                    refine ⟨19845104400378556555460213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13230069600252371036973475 19845104400378556555460213)
                    ·
                      refine ⟨1860478537535489677074395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19845104400378556555460213 1860478537535489677074395)
                      ·
                        rfl

theorem cell23_3623269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 2, 1, 2, 1, 5].length) (baseStart_3623269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3623269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3623269 prefixEnd_3623269 := by exact prefixLift 3623269
  have htrace : WordTrace (prefixWord ++ tailWord_3623269) baseStart_3623269 baseEnd_3623269 := by
    simpa [prefixWord, tailWord_3623269, baseEnd_3623269] using wordTrace_append hprefix tailTrace_3623269
  have hstable : (prefixWord ++ tailWord_3623269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3623269).length < 2 ^ (prefixWord ++ tailWord_3623269).sum := by decide
  have hdescent : baseEnd_3623269 < baseStart_3623269 := by decide
  rcases family_descends (prefixWord ++ tailWord_3623269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3623356 : List Nat := [2, 2, 2, 4, 1, 1, 1, 2, 1, 3, 4]
def baseStart_3623356 : Nat := 118140960795 + 3623356 * 2 ^ 59
def prefixEnd_3623356 : Nat := 4983230072969 + 3 ^ 40 * 3623356 * 2
def baseEnd_3623356 : Nat := 1860523210352430836686495

theorem tailTrace_3623356 : CollatzResearch.WordTrace tailWord_3623356 prefixEnd_3623356 1860523210352430836686495 := by
  unfold tailWord_3623356
  simp only [CollatzResearch.WordTrace]
  refine ⟨66077325130603753391568961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88103100174138337855425281 66077325130603753391568961)
  ·
    refine ⟨49557993847952815043676721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66077325130603753391568961 49557993847952815043676721)
    ·
      refine ⟨37168495385964611282757541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49557993847952815043676721 37168495385964611282757541)
      ·
        refine ⟨6969092884868364615517039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37168495385964611282757541 6969092884868364615517039)
        ·
          refine ⟨10453639327302546923275559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6969092884868364615517039 10453639327302546923275559)
          ·
            refine ⟨15680458990953820384913339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10453639327302546923275559 15680458990953820384913339)
            ·
              refine ⟨23520688486430730577370009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15680458990953820384913339 23520688486430730577370009)
              ·
                refine ⟨17640516364823047933027507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23520688486430730577370009 17640516364823047933027507)
                ·
                  refine ⟨26460774547234571899541261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17640516364823047933027507 26460774547234571899541261)
                  ·
                    refine ⟨9922790455212964462327973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26460774547234571899541261 9922790455212964462327973)
                    ·
                      refine ⟨1860523210352430836686495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9922790455212964462327973 1860523210352430836686495)
                      ·
                        rfl

theorem cell23_3623356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 1, 2, 1, 3, 4].length) (baseStart_3623356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3623356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3623356 prefixEnd_3623356 := by exact prefixLift 3623356
  have htrace : WordTrace (prefixWord ++ tailWord_3623356) baseStart_3623356 baseEnd_3623356 := by
    simpa [prefixWord, tailWord_3623356, baseEnd_3623356] using wordTrace_append hprefix tailTrace_3623356
  have hstable : (prefixWord ++ tailWord_3623356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3623356).length < 2 ^ (prefixWord ++ tailWord_3623356).sum := by decide
  have hdescent : baseEnd_3623356 < baseStart_3623356 := by decide
  rcases family_descends (prefixWord ++ tailWord_3623356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3623439 : List Nat := [1, 1, 2, 1, 1, 1, 2, 5, 3, 6]
def baseStart_3623439 : Nat := 118140960795 + 3623439 * 2 ^ 59
def prefixEnd_3623439 : Nat := 4983230072969 + 3 ^ 40 * 3623439 * 2
def baseEnd_3623439 : Nat := 620188609748918003982871

theorem tailTrace_3623439 : CollatzResearch.WordTrace tailWord_3623439 prefixEnd_3623439 620188609748918003982871 := by
  unfold tailWord_3623439
  simp only [CollatzResearch.WordTrace]
  refine ⟨132157677519906811958409371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88105118346604541305606247 132157677519906811958409371)
  ·
    refine ⟨198236516279860217937614057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132157677519906811958409371 198236516279860217937614057)
    ·
      refine ⟨148677387209895163453210543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 198236516279860217937614057 148677387209895163453210543)
      ·
        refine ⟨223016080814842745179815815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148677387209895163453210543 223016080814842745179815815)
        ·
          refine ⟨334524121222264117769723723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 223016080814842745179815815 334524121222264117769723723)
          ·
            refine ⟨501786181833396176654585585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 334524121222264117769723723 501786181833396176654585585)
            ·
              refine ⟨376339636375047132490939189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 501786181833396176654585585 376339636375047132490939189)
              ·
                refine ⟨35281840910160668671025549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 376339636375047132490939189 35281840910160668671025549)
                ·
                  refine ⟨13230690341310250751634581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35281840910160668671025549 13230690341310250751634581)
                  ·
                    refine ⟨620188609748918003982871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13230690341310250751634581 620188609748918003982871)
                    ·
                      rfl

theorem cell23_3623439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 5, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 5, 3, 6].length) (baseStart_3623439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3623439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3623439 prefixEnd_3623439 := by exact prefixLift 3623439
  have htrace : WordTrace (prefixWord ++ tailWord_3623439) baseStart_3623439 baseEnd_3623439 := by
    simpa [prefixWord, tailWord_3623439, baseEnd_3623439] using wordTrace_append hprefix tailTrace_3623439
  have hstable : (prefixWord ++ tailWord_3623439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3623439).length < 2 ^ (prefixWord ++ tailWord_3623439).sum := by decide
  have hdescent : baseEnd_3623439 < baseStart_3623439 := by decide
  rcases family_descends (prefixWord ++ tailWord_3623439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3623443 : List Nat := [1, 1, 1, 2, 1, 5, 5, 1, 1, 5]
def baseStart_3623443 : Nat := 118140960795 + 3623443 * 2 ^ 59
def prefixEnd_3623443 : Nat := 4983230072969 + 3 ^ 40 * 3623443 * 2
def baseEnd_3623443 : Nat := 620189294389790665432865

theorem tailTrace_3623443 : CollatzResearch.WordTrace tailWord_3623443 prefixEnd_3623443 620189294389790665432865 := by
  unfold tailWord_3623443
  simp only [CollatzResearch.WordTrace]
  refine ⟨132157823411892320641554983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88105215607928213761036655 132157823411892320641554983)
  ·
    refine ⟨198236735117838480962332475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132157823411892320641554983 198236735117838480962332475)
    ·
      refine ⟨297355102676757721443498713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198236735117838480962332475 297355102676757721443498713)
      ·
        refine ⟨223016327007568291082624035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 297355102676757721443498713 223016327007568291082624035)
        ·
          refine ⟨334524490511352436623936053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 223016327007568291082624035 334524490511352436623936053)
          ·
            refine ⟨31361670985439290933494005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 334524490511352436623936053 31361670985439290933494005)
            ·
              refine ⟨2940156654884933525015063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 31361670985439290933494005 2940156654884933525015063)
              ·
                refine ⟨4410234982327400287522595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2940156654884933525015063 4410234982327400287522595)
                ·
                  refine ⟨6615352473491100431283893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4410234982327400287522595 6615352473491100431283893)
                  ·
                    refine ⟨620189294389790665432865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6615352473491100431283893 620189294389790665432865)
                    ·
                      rfl

theorem cell23_3623443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 5, 1, 1, 5].length) (baseStart_3623443 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3623443 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3623443 prefixEnd_3623443 := by exact prefixLift 3623443
  have htrace : WordTrace (prefixWord ++ tailWord_3623443) baseStart_3623443 baseEnd_3623443 := by
    simpa [prefixWord, tailWord_3623443, baseEnd_3623443] using wordTrace_append hprefix tailTrace_3623443
  have hstable : (prefixWord ++ tailWord_3623443).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3623443).length < 2 ^ (prefixWord ++ tailWord_3623443).sum := by decide
  have hdescent : baseEnd_3623443 < baseStart_3623443 := by decide
  rcases family_descends (prefixWord ++ tailWord_3623443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3623473 : List Nat := [1, 2, 2, 3, 1, 1, 4, 3, 2, 4]
def baseStart_3623473 : Nat := 118140960795 + 3623473 * 2 ^ 59
def prefixEnd_3623473 : Nat := 4983230072969 + 3 ^ 40 * 3623473 * 2
def baseEnd_3623473 : Nat := 620194429196335626307819

theorem tailTrace_3623473 : CollatzResearch.WordTrace tailWord_3623473 prefixEnd_3623473 620194429196335626307819 := by
  unfold tailWord_3623473
  simp only [CollatzResearch.WordTrace]
  refine ⟨132158917601783635765147073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88105945067855757176764715 132158917601783635765147073)
  ·
    refine ⟨99119188201337726823860305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132158917601783635765147073 99119188201337726823860305)
    ·
      refine ⟨74339391151003295117895229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99119188201337726823860305 74339391151003295117895229)
      ·
        refine ⟨27877271681626235669210711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74339391151003295117895229 27877271681626235669210711)
        ·
          refine ⟨41815907522439353503816067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27877271681626235669210711 41815907522439353503816067)
          ·
            refine ⟨62723861283659030255724101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41815907522439353503816067 62723861283659030255724101)
            ·
              refine ⟨11760723990686068172948269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 62723861283659030255724101 11760723990686068172948269)
              ·
                refine ⟨4410271496507275564855601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11760723990686068172948269 4410271496507275564855601)
                ·
                  refine ⟨3307703622380456673641701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4410271496507275564855601 3307703622380456673641701)
                  ·
                    refine ⟨620194429196335626307819, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3307703622380456673641701 620194429196335626307819)
                    ·
                      rfl

theorem cell23_3623473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 4, 3, 2, 4].length) (baseStart_3623473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3623473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3623473 prefixEnd_3623473 := by exact prefixLift 3623473
  have htrace : WordTrace (prefixWord ++ tailWord_3623473) baseStart_3623473 baseEnd_3623473 := by
    simpa [prefixWord, tailWord_3623473, baseEnd_3623473] using wordTrace_append hprefix tailTrace_3623473
  have hstable : (prefixWord ++ tailWord_3623473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3623473).length < 2 ^ (prefixWord ++ tailWord_3623473).sum := by decide
  have hdescent : baseEnd_3623473 < baseStart_3623473 := by decide
  rcases family_descends (prefixWord ++ tailWord_3623473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3623480 : List Nat := [2, 1, 2, 1, 4, 1, 3, 2, 3, 2, 2]
def baseStart_3623480 : Nat := 118140960795 + 3623480 * 2 ^ 59
def prefixEnd_3623480 : Nat := 4983230072969 + 3 ^ 40 * 3623480 * 2
def baseEnd_3623480 : Nat := 1860586881953588351535925

theorem tailTrace_3623480 : CollatzResearch.WordTrace tailWord_3623480 prefixEnd_3623480 1860586881953588351535925 := by
  unfold tailWord_3623480
  simp only [CollatzResearch.WordTrace]
  refine ⟨66079586456379137980325947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88106115275172183973767929 66079586456379137980325947)
  ·
    refine ⟨99119379684568706970488921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66079586456379137980325947 99119379684568706970488921)
    ·
      refine ⟨74339534763426530227866691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99119379684568706970488921 74339534763426530227866691)
      ·
        refine ⟨111509302145139795341800037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74339534763426530227866691 111509302145139795341800037)
        ·
          refine ⟨20907994152213711626587507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 111509302145139795341800037 20907994152213711626587507)
          ·
            refine ⟨31361991228320567439881261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20907994152213711626587507 31361991228320567439881261)
            ·
              refine ⟨11760746710620212789955473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31361991228320567439881261 11760746710620212789955473)
              ·
                refine ⟨8820560032965159592466605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11760746710620212789955473 8820560032965159592466605)
                ·
                  refine ⟨3307710012361934847174977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8820560032965159592466605 3307710012361934847174977)
                  ·
                    refine ⟨2480782509271451135381233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3307710012361934847174977 2480782509271451135381233)
                    ·
                      refine ⟨1860586881953588351535925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2480782509271451135381233 1860586881953588351535925)
                      ·
                        rfl

theorem cell23_3623480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 3, 2, 3, 2, 2].length) (baseStart_3623480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3623480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3623480 prefixEnd_3623480 := by exact prefixLift 3623480
  have htrace : WordTrace (prefixWord ++ tailWord_3623480) baseStart_3623480 baseEnd_3623480 := by
    simpa [prefixWord, tailWord_3623480, baseEnd_3623480] using wordTrace_append hprefix tailTrace_3623480
  have hstable : (prefixWord ++ tailWord_3623480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3623480).length < 2 ^ (prefixWord ++ tailWord_3623480).sum := by decide
  have hdescent : baseEnd_3623480 < baseStart_3623480 := by decide
  rcases family_descends (prefixWord ++ tailWord_3623480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3623494 : List Nat := [6, 1, 1, 1, 2, 3, 2, 1, 1, 5]
def baseStart_3623494 : Nat := 118140960795 + 3623494 * 2 ^ 59
def prefixEnd_3623494 : Nat := 4983230072969 + 3 ^ 40 * 3623494 * 2
def baseEnd_3623494 : Nat := 620198023560917098920287

theorem tailTrace_3623494 : CollatzResearch.WordTrace tailWord_3623494 prefixEnd_3623494 620198023560917098920287 := by
  unfold tailWord_3623494
  simp only [CollatzResearch.WordTrace]
  refine ⟨4129990110459611135989423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 88106455689805037567774357 4129990110459611135989423)
  ·
    refine ⟨6194985165689416703984135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4129990110459611135989423 6194985165689416703984135)
    ·
      refine ⟨9292477748534125055976203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6194985165689416703984135 9292477748534125055976203)
      ·
        refine ⟨13938716622801187583964305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9292477748534125055976203 13938716622801187583964305)
        ·
          refine ⟨10454037467100890687973229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13938716622801187583964305 10454037467100890687973229)
          ·
            refine ⟨3920264050162834007989961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10454037467100890687973229 3920264050162834007989961)
            ·
              refine ⟨2940198037622125505992471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3920264050162834007989961 2940198037622125505992471)
              ·
                refine ⟨4410297056433188258988707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2940198037622125505992471 4410297056433188258988707)
                ·
                  refine ⟨6615445584649782388483061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4410297056433188258988707 6615445584649782388483061)
                  ·
                    refine ⟨620198023560917098920287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6615445584649782388483061 620198023560917098920287)
                    ·
                      rfl

theorem cell23_3623494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 3, 2, 1, 1, 5].length) (baseStart_3623494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3623494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3623494 prefixEnd_3623494 := by exact prefixLift 3623494
  have htrace : WordTrace (prefixWord ++ tailWord_3623494) baseStart_3623494 baseEnd_3623494 := by
    simpa [prefixWord, tailWord_3623494, baseEnd_3623494] using wordTrace_append hprefix tailTrace_3623494
  have hstable : (prefixWord ++ tailWord_3623494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3623494).length < 2 ^ (prefixWord ++ tailWord_3623494).sum := by decide
  have hdescent : baseEnd_3623494 < baseStart_3623494 := by decide
  rcases family_descends (prefixWord ++ tailWord_3623494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3623554 : List Nat := [3, 4, 3, 1, 2, 1, 9]
def baseStart_3623554 : Nat := 118140960795 + 3623554 * 2 ^ 59
def prefixEnd_3623554 : Nat := 4983230072969 + 3 ^ 40 * 3623554 * 2
def baseEnd_3623554 : Nat := 22970677524963222987785

theorem tailTrace_3623554 : CollatzResearch.WordTrace tailWord_3623554 prefixEnd_3623554 22970677524963222987785 := by
  unfold tailWord_3623554
  simp only [CollatzResearch.WordTrace]
  refine ⟨33040467978622546649711429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88107914609660124399230477 33040467978622546649711429)
  ·
    refine ⟨6195087745991727496820893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33040467978622546649711429 6195087745991727496820893)
    ·
      refine ⟨2323157904746897811307835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6195087745991727496820893 2323157904746897811307835)
      ·
        refine ⟨3484736857120346716961753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2323157904746897811307835 3484736857120346716961753)
        ·
          refine ⟨2613552642840260037721315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3484736857120346716961753 2613552642840260037721315)
          ·
            refine ⟨3920328964260390056581973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2613552642840260037721315 3920328964260390056581973)
            ·
              refine ⟨22970677524963222987785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3920328964260390056581973 22970677524963222987785)
              ·
                rfl

theorem cell23_3623554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 2, 1, 9].length) (baseStart_3623554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3623554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3623554 prefixEnd_3623554 := by exact prefixLift 3623554
  have htrace : WordTrace (prefixWord ++ tailWord_3623554) baseStart_3623554 baseEnd_3623554 := by
    simpa [prefixWord, tailWord_3623554, baseEnd_3623554] using wordTrace_append hprefix tailTrace_3623554
  have hstable : (prefixWord ++ tailWord_3623554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3623554).length < 2 ^ (prefixWord ++ tailWord_3623554).sum := by decide
  have hdescent : baseEnd_3623554 < baseStart_3623554 := by decide
  rcases family_descends (prefixWord ++ tailWord_3623554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3623591 : List Nat := [1, 1, 6, 3, 1, 2, 1, 2, 1, 3, 2]
def baseStart_3623591 : Nat := 118140960795 + 3623591 * 2 ^ 59
def prefixEnd_3623591 : Nat := 4983230072969 + 3 ^ 40 * 3623591 * 2
def baseEnd_3623591 : Nat := 1860643878306237417247915

theorem tailTrace_3623591 : CollatzResearch.WordTrace tailWord_3623591 prefixEnd_3623591 1860643878306237417247915 := by
  unfold tailWord_3623591
  simp only [CollatzResearch.WordTrace]
  refine ⟨132163221415356141917942627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88108814276904094611961751 132163221415356141917942627)
  ·
    refine ⟨198244832123034212876913941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132163221415356141917942627 198244832123034212876913941)
    ·
      refine ⟨9292726505767228728605341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 198244832123034212876913941 9292726505767228728605341)
      ·
        refine ⟨3484772439662710773227003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9292726505767228728605341 3484772439662710773227003)
        ·
          refine ⟨5227158659494066159840505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3484772439662710773227003 5227158659494066159840505)
          ·
            refine ⟨3920368994620549619880379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5227158659494066159840505 3920368994620549619880379)
            ·
              refine ⟨5880553491930824429820569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3920368994620549619880379 5880553491930824429820569)
              ·
                refine ⟨4410415118948118322365427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5880553491930824429820569 4410415118948118322365427)
                ·
                  refine ⟨6615622678422177483548141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4410415118948118322365427 6615622678422177483548141)
                  ·
                    refine ⟨2480858504408316556330553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6615622678422177483548141 2480858504408316556330553)
                    ·
                      refine ⟨1860643878306237417247915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2480858504408316556330553 1860643878306237417247915)
                      ·
                        rfl

theorem cell23_3623591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 2, 1, 2, 1, 3, 2].length) (baseStart_3623591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3623591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3623591 prefixEnd_3623591 := by exact prefixLift 3623591
  have htrace : WordTrace (prefixWord ++ tailWord_3623591) baseStart_3623591 baseEnd_3623591 := by
    simpa [prefixWord, tailWord_3623591, baseEnd_3623591] using wordTrace_append hprefix tailTrace_3623591
  have hstable : (prefixWord ++ tailWord_3623591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3623591).length < 2 ^ (prefixWord ++ tailWord_3623591).sum := by decide
  have hdescent : baseEnd_3623591 < baseStart_3623591 := by decide
  rcases family_descends (prefixWord ++ tailWord_3623591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3623630 : List Nat := [4, 1, 1, 1, 3, 2, 1, 1, 2, 5, 2]
def baseStart_3623630 : Nat := 118140960795 + 3623630 * 2 ^ 59
def prefixEnd_3623630 : Nat := 4983230072969 + 3 ^ 40 * 3623630 * 2
def baseEnd_3623630 : Nat := 1860663904051762764660235

theorem tailTrace_3623630 : CollatzResearch.WordTrace tailWord_3623630 prefixEnd_3623630 1860663904051762764660235 := by
  unfold tailWord_3623630
  simp only [CollatzResearch.WordTrace]
  refine ⟨16520580482776856447326543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 88109762574809901052408229 16520580482776856447326543)
  ·
    refine ⟨24780870724165284670989815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16520580482776856447326543 24780870724165284670989815)
    ·
      refine ⟨37171306086247927006484723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24780870724165284670989815 37171306086247927006484723)
      ·
        refine ⟨55756959129371890509727085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37171306086247927006484723 55756959129371890509727085)
        ·
          refine ⟨20908859673514458941147657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55756959129371890509727085 20908859673514458941147657)
          ·
            refine ⟨15681644755135844205860743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20908859673514458941147657 15681644755135844205860743)
            ·
              refine ⟨23522467132703766308791115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15681644755135844205860743 23522467132703766308791115)
              ·
                refine ⟨35283700699055649463186673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23522467132703766308791115 35283700699055649463186673)
                ·
                  refine ⟨26462775524291737097390005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35283700699055649463186673 26462775524291737097390005)
                  ·
                    refine ⟨2480885205402350352880313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 26462775524291737097390005 2480885205402350352880313)
                    ·
                      refine ⟨1860663904051762764660235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2480885205402350352880313 1860663904051762764660235)
                      ·
                        rfl

theorem cell23_3623630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 1, 1, 2, 5, 2].length) (baseStart_3623630 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3623630 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3623630 prefixEnd_3623630 := by exact prefixLift 3623630
  have htrace : WordTrace (prefixWord ++ tailWord_3623630) baseStart_3623630 baseEnd_3623630 := by
    simpa [prefixWord, tailWord_3623630, baseEnd_3623630] using wordTrace_append hprefix tailTrace_3623630
  have hstable : (prefixWord ++ tailWord_3623630).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3623630).length < 2 ^ (prefixWord ++ tailWord_3623630).sum := by decide
  have hdescent : baseEnd_3623630 < baseStart_3623630 := by decide
  rcases family_descends (prefixWord ++ tailWord_3623630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3623637 : List Nat := [1, 3, 2, 5, 1, 1, 1, 1, 2, 3, 3]
def baseStart_3623637 : Nat := 118140960795 + 3623637 * 2 ^ 59
def prefixEnd_3623637 : Nat := 4983230072969 + 3 ^ 40 * 3623637 * 2
def baseEnd_3623637 : Nat := 1860667498416344237272703

theorem tailTrace_3623637 : CollatzResearch.WordTrace tailWord_3623637 prefixEnd_3623637 1860667498416344237272703 := by
  unfold tailWord_3623637
  simp only [CollatzResearch.WordTrace]
  refine ⟨132164899173189491774117165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88109932782126327849411443 132164899173189491774117165)
  ·
    refine ⟨49561837189946059415293937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 132164899173189491774117165 49561837189946059415293937)
    ·
      refine ⟨37171377892459544561470453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49561837189946059415293937 37171377892459544561470453)
      ·
        refine ⟨3484816677418082302637855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 37171377892459544561470453 3484816677418082302637855)
        ·
          refine ⟨5227225016127123453956783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3484816677418082302637855 5227225016127123453956783)
          ·
            refine ⟨7840837524190685180935175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5227225016127123453956783 7840837524190685180935175)
            ·
              refine ⟨11761256286286027771402763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7840837524190685180935175 11761256286286027771402763)
              ·
                refine ⟨17641884429429041657104145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11761256286286027771402763 17641884429429041657104145)
                ·
                  refine ⟨13231413322071781242828109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17641884429429041657104145 13231413322071781242828109)
                  ·
                    refine ⟨4961779995776917966060541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13231413322071781242828109 4961779995776917966060541)
                    ·
                      refine ⟨1860667498416344237272703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4961779995776917966060541 1860667498416344237272703)
                      ·
                        rfl

theorem cell23_3623637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 1, 1, 2, 3, 3].length) (baseStart_3623637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3623637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3623637 prefixEnd_3623637 := by exact prefixLift 3623637
  have htrace : WordTrace (prefixWord ++ tailWord_3623637) baseStart_3623637 baseEnd_3623637 := by
    simpa [prefixWord, tailWord_3623637, baseEnd_3623637] using wordTrace_append hprefix tailTrace_3623637
  have hstable : (prefixWord ++ tailWord_3623637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3623637).length < 2 ^ (prefixWord ++ tailWord_3623637).sum := by decide
  have hdescent : baseEnd_3623637 < baseStart_3623637 := by decide
  rcases family_descends (prefixWord ++ tailWord_3623637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3623670 : List Nat := [5, 1, 1, 1, 1, 2, 1, 2, 5, 4]
def baseStart_3623670 : Nat := 118140960795 + 3623670 * 2 ^ 59
def prefixEnd_3623670 : Nat := 4983230072969 + 3 ^ 40 * 3623670 * 2
def baseEnd_3623670 : Nat := 620228147759314202720017

theorem tailTrace_3623670 : CollatzResearch.WordTrace tailWord_3623670 prefixEnd_3623670 620228147759314202720017 := by
  unfold tailWord_3623670
  simp only [CollatzResearch.WordTrace]
  refine ⟨8260381423879371150629279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 88110735188046625606712309 8260381423879371150629279)
  ·
    refine ⟨12390572135819056725943919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8260381423879371150629279 12390572135819056725943919)
    ·
      refine ⟨18585858203728585088915879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12390572135819056725943919 18585858203728585088915879)
      ·
        refine ⟨27878787305592877633373819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18585858203728585088915879 27878787305592877633373819)
        ·
          refine ⟨41818180958389316450060729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27878787305592877633373819 41818180958389316450060729)
          ·
            refine ⟨31363635718791987337545547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41818180958389316450060729 31363635718791987337545547)
            ·
              refine ⟨47045453578187981006318321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31363635718791987337545547 47045453578187981006318321)
              ·
                refine ⟨35284090183640985754738741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47045453578187981006318321 35284090183640985754738741)
                ·
                  refine ⟨3307883454716342414506757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 35284090183640985754738741 3307883454716342414506757)
                  ·
                    refine ⟨620228147759314202720017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3307883454716342414506757 620228147759314202720017)
                    ·
                      rfl

theorem cell23_3623670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 2, 5, 4].length) (baseStart_3623670 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3623670 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3623670 prefixEnd_3623670 := by exact prefixLift 3623670
  have htrace : WordTrace (prefixWord ++ tailWord_3623670) baseStart_3623670 baseEnd_3623670 := by
    simpa [prefixWord, tailWord_3623670, baseEnd_3623670] using wordTrace_append hprefix tailTrace_3623670
  have hstable : (prefixWord ++ tailWord_3623670).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3623670).length < 2 ^ (prefixWord ++ tailWord_3623670).sum := by decide
  have hdescent : baseEnd_3623670 < baseStart_3623670 := by decide
  rcases family_descends (prefixWord ++ tailWord_3623670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3623687 : List Nat := [1, 1, 4, 4, 1, 2, 2, 1, 3, 4]
def baseStart_3623687 : Nat := 118140960795 + 3623687 * 2 ^ 59
def prefixEnd_3623687 : Nat := 4983230072969 + 3 ^ 40 * 3623687 * 2
def baseEnd_3623687 : Nat := 620231057483023013882491

theorem tailTrace_3623687 : CollatzResearch.WordTrace tailWord_3623687 prefixEnd_3623687 620231057483023013882491 := by
  unfold tailWord_3623687
  simp only [CollatzResearch.WordTrace]
  refine ⟨132166722823008350313437315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88111148548672233542291543 132166722823008350313437315)
  ·
    refine ⟨198250084234512525470155973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132166722823008350313437315 198250084234512525470155973)
    ·
      refine ⟨37171890793971098525654245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 198250084234512525470155973 37171890793971098525654245)
      ·
        refine ⟨6969729523869580973560171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37171890793971098525654245 6969729523869580973560171)
        ·
          refine ⟨10454594285804371460340257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6969729523869580973560171 10454594285804371460340257)
          ·
            refine ⟨7840945714353278595255193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10454594285804371460340257 7840945714353278595255193)
            ·
              refine ⟨5880709285764958946441395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7840945714353278595255193 5880709285764958946441395)
              ·
                refine ⟨8821063928647438419662093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5880709285764958946441395 8821063928647438419662093)
                ·
                  refine ⟨3307898973242789407373285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8821063928647438419662093 3307898973242789407373285)
                  ·
                    refine ⟨620231057483023013882491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3307898973242789407373285 620231057483023013882491)
                    ·
                      rfl

theorem cell23_3623687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 2, 1, 3, 4].length) (baseStart_3623687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3623687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3623687 prefixEnd_3623687 := by exact prefixLift 3623687
  have htrace : WordTrace (prefixWord ++ tailWord_3623687) baseStart_3623687 baseEnd_3623687 := by
    simpa [prefixWord, tailWord_3623687, baseEnd_3623687] using wordTrace_append hprefix tailTrace_3623687
  have hstable : (prefixWord ++ tailWord_3623687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3623687).length < 2 ^ (prefixWord ++ tailWord_3623687).sum := by decide
  have hdescent : baseEnd_3623687 < baseStart_3623687 := by decide
  rcases family_descends (prefixWord ++ tailWord_3623687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3623730 : List Nat := [3, 2, 1, 1, 3, 1, 1, 5, 1, 5]
def baseStart_3623730 : Nat := 118140960795 + 3623730 * 2 ^ 59
def prefixEnd_3623730 : Nat := 4983230072969 + 3 ^ 40 * 3623730 * 2
def baseEnd_3623730 : Nat := 620238417372404124469925

theorem tailTrace_3623730 : CollatzResearch.WordTrace tailWord_3623730 prefixEnd_3623730 620238417372404124469925 := by
  unfold tailWord_3623730
  simp only [CollatzResearch.WordTrace]
  refine ⟨33042072790463142164313161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88112194107901712438168429 33042072790463142164313161)
  ·
    refine ⟨24781554592847356623234871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33042072790463142164313161 24781554592847356623234871)
    ·
      refine ⟨37172331889271034934852307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24781554592847356623234871 37172331889271034934852307)
      ·
        refine ⟨55758497833906552402278461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37172331889271034934852307 55758497833906552402278461)
        ·
          refine ⟨20909436687714957150854423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55758497833906552402278461 20909436687714957150854423)
          ·
            refine ⟨31364155031572435726281635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20909436687714957150854423 31364155031572435726281635)
            ·
              refine ⟨47046232547358653589422453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31364155031572435726281635 47046232547358653589422453)
              ·
                refine ⟨4410584301314873774008355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 47046232547358653589422453 4410584301314873774008355)
                ·
                  refine ⟨6615876451972310661012533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4410584301314873774008355 6615876451972310661012533)
                  ·
                    refine ⟨620238417372404124469925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6615876451972310661012533 620238417372404124469925)
                    ·
                      rfl

theorem cell23_3623730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 5, 1, 5].length) (baseStart_3623730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3623730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3623730 prefixEnd_3623730 := by exact prefixLift 3623730
  have htrace : WordTrace (prefixWord ++ tailWord_3623730) baseStart_3623730 baseEnd_3623730 := by
    simpa [prefixWord, tailWord_3623730, baseEnd_3623730] using wordTrace_append hprefix tailTrace_3623730
  have hstable : (prefixWord ++ tailWord_3623730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3623730).length < 2 ^ (prefixWord ++ tailWord_3623730).sum := by decide
  have hdescent : baseEnd_3623730 < baseStart_3623730 := by decide
  rcases family_descends (prefixWord ++ tailWord_3623730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3623763 : List Nat := [1, 1, 1, 2, 1, 1, 3, 2, 5, 2, 4]
def baseStart_3623763 : Nat := 118140960795 + 3623763 * 2 ^ 59
def prefixEnd_3623763 : Nat := 4983230072969 + 3 ^ 40 * 3623763 * 2
def baseEnd_3623763 : Nat := 1860732196978810744297123

theorem tailTrace_3623763 : CollatzResearch.WordTrace tailWord_3623763 prefixEnd_3623763 1860732196978810744297123 := by
  unfold tailWord_3623763
  simp only [CollatzResearch.WordTrace]
  refine ⟨132169494770733015293203943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88112996513822010195469295 132169494770733015293203943)
  ·
    refine ⟨198254242156099522939805915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132169494770733015293203943 198254242156099522939805915)
    ·
      refine ⟨297381363234149284409708873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198254242156099522939805915 297381363234149284409708873)
      ·
        refine ⟨223036022425611963307281655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 297381363234149284409708873 223036022425611963307281655)
        ·
          refine ⟨334554033638417944960922483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 223036022425611963307281655 334554033638417944960922483)
          ·
            refine ⟨501831050457626917441383725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 334554033638417944960922483 501831050457626917441383725)
            ·
              refine ⟨188186643921610094040518897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 501831050457626917441383725 188186643921610094040518897)
              ·
                refine ⟨141139982941207570530389173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 188186643921610094040518897 141139982941207570530389173)
                ·
                  refine ⟨13231873400738209737223985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 141139982941207570530389173 13231873400738209737223985)
                  ·
                    refine ⟨9923905050553657302917989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13231873400738209737223985 9923905050553657302917989)
                    ·
                      refine ⟨1860732196978810744297123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9923905050553657302917989 1860732196978810744297123)
                      ·
                        rfl

theorem cell23_3623763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 2, 5, 2, 4].length) (baseStart_3623763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3623763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3623763 prefixEnd_3623763 := by exact prefixLift 3623763
  have htrace : WordTrace (prefixWord ++ tailWord_3623763) baseStart_3623763 baseEnd_3623763 := by
    simpa [prefixWord, tailWord_3623763, baseEnd_3623763] using wordTrace_append hprefix tailTrace_3623763
  have hstable : (prefixWord ++ tailWord_3623763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3623763).length < 2 ^ (prefixWord ++ tailWord_3623763).sum := by decide
  have hdescent : baseEnd_3623763 < baseStart_3623763 := by decide
  rcases family_descends (prefixWord ++ tailWord_3623763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3623764 : List Nat := [2, 4, 1, 1, 4, 2, 1, 2, 1, 5]
def baseStart_3623764 : Nat := 118140960795 + 3623764 * 2 ^ 59
def prefixEnd_3623764 : Nat := 4983230072969 + 3 ^ 40 * 3623764 * 2
def baseEnd_3623764 : Nat := 620244236819821746794873

theorem tailTrace_3623764 : CollatzResearch.WordTrace tailWord_3623764 prefixEnd_3623764 620244236819821746794873 := by
  unfold tailWord_3623764
  simp only [CollatzResearch.WordTrace]
  refine ⟨66084765621864696231995173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88113020829152928309326897 66084765621864696231995173)
  ·
    refine ⟨12390893554099630543499095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 66084765621864696231995173 12390893554099630543499095)
    ·
      refine ⟨18586340331149445815248643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12390893554099630543499095 18586340331149445815248643)
      ·
        refine ⟨27879510496724168722872965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18586340331149445815248643 27879510496724168722872965)
        ·
          refine ⟨5227408218135781635538681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27879510496724168722872965 5227408218135781635538681)
          ·
            refine ⟨3920556163601836226654011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5227408218135781635538681 3920556163601836226654011)
            ·
              refine ⟨5880834245402754339981017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3920556163601836226654011 5880834245402754339981017)
              ·
                refine ⟨4410625684052065754985763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5880834245402754339981017 4410625684052065754985763)
                ·
                  refine ⟨6615938526078098632478645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4410625684052065754985763 6615938526078098632478645)
                  ·
                    refine ⟨620244236819821746794873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6615938526078098632478645 620244236819821746794873)
                    ·
                      rfl

theorem cell23_3623764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 2, 1, 2, 1, 5].length) (baseStart_3623764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3623764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3623764 prefixEnd_3623764 := by exact prefixLift 3623764
  have htrace : WordTrace (prefixWord ++ tailWord_3623764) baseStart_3623764 baseEnd_3623764 := by
    simpa [prefixWord, tailWord_3623764, baseEnd_3623764] using wordTrace_append hprefix tailTrace_3623764
  have hstable : (prefixWord ++ tailWord_3623764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3623764).length < 2 ^ (prefixWord ++ tailWord_3623764).sum := by decide
  have hdescent : baseEnd_3623764 < baseStart_3623764 := by decide
  rcases family_descends (prefixWord ++ tailWord_3623764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3623767 : List Nat := [1, 1, 3, 2, 4, 1, 3, 2, 1, 1, 4]
def baseStart_3623767 : Nat := 118140960795 + 3623767 * 2 ^ 59
def prefixEnd_3623767 : Nat := 4983230072969 + 3 ^ 40 * 3623767 * 2
def baseEnd_3623767 : Nat := 1860734250901428728647105

theorem tailTrace_3623767 : CollatzResearch.WordTrace tailWord_3623767 prefixEnd_3623767 1860734250901428728647105 := by
  unfold tailWord_3623767
  simp only [CollatzResearch.WordTrace]
  refine ⟨132169640662718523976349555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88113093775145682650899703 132169640662718523976349555)
  ·
    refine ⟨198254460994077785964524333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132169640662718523976349555 198254460994077785964524333)
    ·
      refine ⟨74345422872779169736696625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 198254460994077785964524333 74345422872779169736696625)
      ·
        refine ⟨55759067154584377302522469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74345422872779169736696625 55759067154584377302522469)
        ·
          refine ⟨10454825091484570744222963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 55759067154584377302522469 10454825091484570744222963)
          ·
            refine ⟨15682237637226856116334445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10454825091484570744222963 15682237637226856116334445)
            ·
              refine ⟨5880839113960071043625417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15682237637226856116334445 5880839113960071043625417)
              ·
                refine ⟨4410629335470053282719063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5880839113960071043625417 4410629335470053282719063)
                ·
                  refine ⟨6615944003205079924078595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4410629335470053282719063 6615944003205079924078595)
                  ·
                    refine ⟨9923916004807619886117893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6615944003205079924078595 9923916004807619886117893)
                    ·
                      refine ⟨1860734250901428728647105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9923916004807619886117893 1860734250901428728647105)
                      ·
                        rfl

theorem cell23_3623767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 3, 2, 1, 1, 4].length) (baseStart_3623767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3623767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3623767 prefixEnd_3623767 := by exact prefixLift 3623767
  have htrace : WordTrace (prefixWord ++ tailWord_3623767) baseStart_3623767 baseEnd_3623767 := by
    simpa [prefixWord, tailWord_3623767, baseEnd_3623767] using wordTrace_append hprefix tailTrace_3623767
  have hstable : (prefixWord ++ tailWord_3623767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3623767).length < 2 ^ (prefixWord ++ tailWord_3623767).sum := by decide
  have hdescent : baseEnd_3623767 < baseStart_3623767 := by decide
  rcases family_descends (prefixWord ++ tailWord_3623767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3623780 : List Nat := [2, 3, 1, 1, 4, 1, 1, 1, 3, 2, 4]
def baseStart_3623780 : Nat := 118140960795 + 3623780 * 2 ^ 59
def prefixEnd_3623780 : Nat := 4983230072969 + 3 ^ 40 * 3623780 * 2
def baseEnd_3623780 : Nat := 1860740926149937177784545

theorem tailTrace_3623780 : CollatzResearch.WordTrace tailWord_3623780 prefixEnd_3623780 1860740926149937177784545 := by
  unfold tailWord_3623780
  simp only [CollatzResearch.WordTrace]
  refine ⟨66085057405835713598286397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88113409874447618131048529 66085057405835713598286397)
  ·
    refine ⟨24781896527188392599357399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66085057405835713598286397 24781896527188392599357399)
    ·
      refine ⟨37172844790782588899036099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24781896527188392599357399 37172844790782588899036099)
      ·
        refine ⟨55759267186173883348554149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37172844790782588899036099 55759267186173883348554149)
        ·
          refine ⟨10454862597407603127853903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 55759267186173883348554149 10454862597407603127853903)
          ·
            refine ⟨15682293896111404691780855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10454862597407603127853903 15682293896111404691780855)
            ·
              refine ⟨23523440844167107037671283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15682293896111404691780855 23523440844167107037671283)
              ·
                refine ⟨35285161266250660556506925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23523440844167107037671283 35285161266250660556506925)
                ·
                  refine ⟨13231935474843997708690097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35285161266250660556506925 13231935474843997708690097)
                  ·
                    refine ⟨9923951606132998281517573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13231935474843997708690097 9923951606132998281517573)
                    ·
                      refine ⟨1860740926149937177784545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9923951606132998281517573 1860740926149937177784545)
                      ·
                        rfl

theorem cell23_3623780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 1, 1, 3, 2, 4].length) (baseStart_3623780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3623780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3623780 prefixEnd_3623780 := by exact prefixLift 3623780
  have htrace : WordTrace (prefixWord ++ tailWord_3623780) baseStart_3623780 baseEnd_3623780 := by
    simpa [prefixWord, tailWord_3623780, baseEnd_3623780] using wordTrace_append hprefix tailTrace_3623780
  have hstable : (prefixWord ++ tailWord_3623780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3623780).length < 2 ^ (prefixWord ++ tailWord_3623780).sum := by decide
  have hdescent : baseEnd_3623780 < baseStart_3623780 := by decide
  rcases family_descends (prefixWord ++ tailWord_3623780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3623784 : List Nat := [2, 1, 4, 2, 1, 3, 3, 1, 1, 1, 4]
def baseStart_3623784 : Nat := 118140960795 + 3623784 * 2 ^ 59
def prefixEnd_3623784 : Nat := 4983230072969 + 3 ^ 40 * 3623784 * 2
def baseEnd_3623784 : Nat := 1860742980072555162134527

theorem tailTrace_3623784 : CollatzResearch.WordTrace tailWord_3623784 prefixEnd_3623784 1860742980072555162134527 := by
  unfold tailWord_3623784
  simp only [CollatzResearch.WordTrace]
  refine ⟨66085130351828467939859203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88113507135771290586478937 66085130351828467939859203)
  ·
    refine ⟨99127695527742701909788805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66085130351828467939859203 99127695527742701909788805)
    ·
      refine ⟨18586442911451756608085401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 99127695527742701909788805 18586442911451756608085401)
      ·
        refine ⟨13939832183588817456064051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18586442911451756608085401 13939832183588817456064051)
        ·
          refine ⟨20909748275383226184096077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13939832183588817456064051 20909748275383226184096077)
          ·
            refine ⟨7841155603268709819036029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20909748275383226184096077 7841155603268709819036029)
            ·
              refine ⟨2940433351225766182138511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7841155603268709819036029 2940433351225766182138511)
              ·
                refine ⟨4410650026838649273207767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2940433351225766182138511 4410650026838649273207767)
                ·
                  refine ⟨6615975040257973909811651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4410650026838649273207767 6615975040257973909811651)
                  ·
                    refine ⟨9923962560386960864717477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6615975040257973909811651 9923962560386960864717477)
                    ·
                      refine ⟨1860742980072555162134527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9923962560386960864717477 1860742980072555162134527)
                      ·
                        rfl

theorem cell23_3623784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 3, 1, 1, 1, 4].length) (baseStart_3623784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3623784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3623784 prefixEnd_3623784 := by exact prefixLift 3623784
  have htrace : WordTrace (prefixWord ++ tailWord_3623784) baseStart_3623784 baseEnd_3623784 := by
    simpa [prefixWord, tailWord_3623784, baseEnd_3623784] using wordTrace_append hprefix tailTrace_3623784
  have hstable : (prefixWord ++ tailWord_3623784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3623784).length < 2 ^ (prefixWord ++ tailWord_3623784).sum := by decide
  have hdescent : baseEnd_3623784 < baseStart_3623784 := by decide
  rcases family_descends (prefixWord ++ tailWord_3623784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3623790 : List Nat := [4, 1, 2, 3, 2, 11]
def baseStart_3623790 : Nat := 118140960795 + 3623790 * 2 ^ 59
def prefixEnd_3623790 : Nat := 4983230072969 + 3 ^ 40 * 3623790 * 2
def baseEnd_3623790 : Nat := 7657391197351778348393

theorem tailTrace_3623790 : CollatzResearch.WordTrace tailWord_3623790 prefixEnd_3623790 7657391197351778348393 := by
  unfold tailWord_3623790
  simp only [CollatzResearch.WordTrace]
  refine ⟨16521309942704399863054603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 88113653027756799269624549 16521309942704399863054603)
  ·
    refine ⟨24781964914056599794581905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16521309942704399863054603 24781964914056599794581905)
    ·
      refine ⟨18586473685542449845936429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24781964914056599794581905 18586473685542449845936429)
      ·
        refine ⟨6969927632078418692226161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18586473685542449845936429 6969927632078418692226161)
        ·
          refine ⟨5227445724058814019169621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6969927632078418692226161 5227445724058814019169621)
          ·
            refine ⟨7657391197351778348393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 5227445724058814019169621 7657391197351778348393)
            ·
              rfl

theorem cell23_3623790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 11].length) (baseStart_3623790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3623790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3623790 prefixEnd_3623790 := by exact prefixLift 3623790
  have htrace : WordTrace (prefixWord ++ tailWord_3623790) baseStart_3623790 baseEnd_3623790 := by
    simpa [prefixWord, tailWord_3623790, baseEnd_3623790] using wordTrace_append hprefix tailTrace_3623790
  have hstable : (prefixWord ++ tailWord_3623790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3623790).length < 2 ^ (prefixWord ++ tailWord_3623790).sum := by decide
  have hdescent : baseEnd_3623790 < baseStart_3623790 := by decide
  rcases family_descends (prefixWord ++ tailWord_3623790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3623801 : List Nat := [1, 2, 1, 3, 2, 4, 1, 4, 1, 2, 2]
def baseStart_3623801 : Nat := 118140960795 + 3623801 * 2 ^ 59
def prefixEnd_3623801 : Nat := 4983230072969 + 3 ^ 40 * 3623801 * 2
def baseEnd_3623801 : Nat := 1860751709243681595621949

theorem tailTrace_3623801 : CollatzResearch.WordTrace tailWord_3623801 prefixEnd_3623801 1860751709243681595621949 := by
  unfold tailWord_3623801
  simp only [CollatzResearch.WordTrace]
  refine ⟨132170880744595347783087257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88113920496396898522058171 132170880744595347783087257)
  ·
    refine ⟨99128160558446510837315443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132170880744595347783087257 99128160558446510837315443)
    ·
      refine ⟨148692240837669766255973165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99128160558446510837315443 148692240837669766255973165)
      ·
        refine ⟨55759590314126162345989937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 148692240837669766255973165 55759590314126162345989937)
        ·
          refine ⟨41819692735594621759492453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55759590314126162345989937 41819692735594621759492453)
          ·
            refine ⟨7841192387923991579904835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41819692735594621759492453 7841192387923991579904835)
            ·
              refine ⟨11761788581885987369857253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7841192387923991579904835 11761788581885987369857253)
              ·
                refine ⟨2205335359103622631848235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11761788581885987369857253 2205335359103622631848235)
                ·
                  refine ⟨3308003038655433947772353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2205335359103622631848235 3308003038655433947772353)
                  ·
                    refine ⟨2481002278991575460829265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3308003038655433947772353 2481002278991575460829265)
                    ·
                      refine ⟨1860751709243681595621949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2481002278991575460829265 1860751709243681595621949)
                      ·
                        rfl

theorem cell23_3623801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 1, 4, 1, 2, 2].length) (baseStart_3623801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3623801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3623801 prefixEnd_3623801 := by exact prefixLift 3623801
  have htrace : WordTrace (prefixWord ++ tailWord_3623801) baseStart_3623801 baseEnd_3623801 := by
    simpa [prefixWord, tailWord_3623801, baseEnd_3623801] using wordTrace_append hprefix tailTrace_3623801
  have hstable : (prefixWord ++ tailWord_3623801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3623801).length < 2 ^ (prefixWord ++ tailWord_3623801).sum := by decide
  have hdescent : baseEnd_3623801 < baseStart_3623801 := by decide
  rcases family_descends (prefixWord ++ tailWord_3623801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3623803 : List Nat := [1, 1, 1, 1, 1, 5, 3, 1, 2, 7]
def baseStart_3623803 : Nat := 118140960795 + 3623803 * 2 ^ 59
def prefixEnd_3623803 : Nat := 4983230072969 + 3 ^ 40 * 3623803 * 2
def baseEnd_3623803 : Nat := 620250912068330195932313

theorem tailTrace_3623803 : CollatzResearch.WordTrace tailWord_3623803 prefixEnd_3623803 620250912068330195932313 := by
  unfold tailWord_3623803
  simp only [CollatzResearch.WordTrace]
  refine ⟨132170953690588102124660063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88113969127058734749773375 132170953690588102124660063)
  ·
    refine ⟨198256430535882153186990095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132170953690588102124660063 198256430535882153186990095)
    ·
      refine ⟨297384645803823229780485143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198256430535882153186990095 297384645803823229780485143)
      ·
        refine ⟨446076968705734844670727715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 297384645803823229780485143 446076968705734844670727715)
        ·
          refine ⟨669115453058602267006091573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 446076968705734844670727715 669115453058602267006091573)
          ·
            refine ⟨62729573724243962531821085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 669115453058602267006091573 62729573724243962531821085)
            ·
              refine ⟨23523590146591485949432907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62729573724243962531821085 23523590146591485949432907)
              ·
                refine ⟨35285385219887228924149361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23523590146591485949432907 35285385219887228924149361)
                ·
                  refine ⟨26464038914915421693112021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35285385219887228924149361 26464038914915421693112021)
                  ·
                    refine ⟨620250912068330195932313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 26464038914915421693112021 620250912068330195932313)
                    ·
                      rfl

theorem cell23_3623803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 3, 1, 2, 7].length) (baseStart_3623803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3623803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3623803 prefixEnd_3623803 := by exact prefixLift 3623803
  have htrace : WordTrace (prefixWord ++ tailWord_3623803) baseStart_3623803 baseEnd_3623803 := by
    simpa [prefixWord, tailWord_3623803, baseEnd_3623803] using wordTrace_append hprefix tailTrace_3623803
  have hstable : (prefixWord ++ tailWord_3623803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3623803).length < 2 ^ (prefixWord ++ tailWord_3623803).sum := by decide
  have hdescent : baseEnd_3623803 < baseStart_3623803 := by decide
  rcases family_descends (prefixWord ++ tailWord_3623803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3623817 : List Nat := [1, 2, 1, 1, 5, 3, 2, 1, 1, 3, 3]
def baseStart_3623817 : Nat := 118140960795 + 3623817 * 2 ^ 59
def prefixEnd_3623817 : Nat := 4983230072969 + 3 ^ 40 * 3623817 * 2
def baseEnd_3623817 : Nat := 1860759924934153533021875

theorem tailTrace_3623817 : CollatzResearch.WordTrace tailWord_3623817 prefixEnd_3623817 1860759924934153533021875 := by
  unfold tailWord_3623817
  simp only [CollatzResearch.WordTrace]
  refine ⟨132171464312537382515669705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88114309541691588343779803 132171464312537382515669705)
  ·
    refine ⟨99128598234403036886752279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132171464312537382515669705 99128598234403036886752279)
    ·
      refine ⟨148692897351604555330128419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99128598234403036886752279 148692897351604555330128419)
      ·
        refine ⟨223039346027406832995192629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148692897351604555330128419 223039346027406832995192629)
        ·
          refine ⟨20909938690069390593299309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 223039346027406832995192629 20909938690069390593299309)
          ·
            refine ⟨7841227008776021472487241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20909938690069390593299309 7841227008776021472487241)
            ·
              refine ⟨5880920256582016104365431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7841227008776021472487241 5880920256582016104365431)
              ·
                refine ⟨8821380384873024156548147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5880920256582016104365431 8821380384873024156548147)
                ·
                  refine ⟨13232070577309536234822221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8821380384873024156548147 13232070577309536234822221)
                  ·
                    refine ⟨4962026466491076088058333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13232070577309536234822221 4962026466491076088058333)
                    ·
                      refine ⟨1860759924934153533021875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4962026466491076088058333 1860759924934153533021875)
                      ·
                        rfl

theorem cell23_3623817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 2, 1, 1, 3, 3].length) (baseStart_3623817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3623817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3623817 prefixEnd_3623817 := by exact prefixLift 3623817
  have htrace : WordTrace (prefixWord ++ tailWord_3623817) baseStart_3623817 baseEnd_3623817 := by
    simpa [prefixWord, tailWord_3623817, baseEnd_3623817] using wordTrace_append hprefix tailTrace_3623817
  have hstable : (prefixWord ++ tailWord_3623817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3623817).length < 2 ^ (prefixWord ++ tailWord_3623817).sum := by decide
  have hdescent : baseEnd_3623817 < baseStart_3623817 := by decide
  rcases family_descends (prefixWord ++ tailWord_3623817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3623833 : List Nat := [1, 2, 1, 2, 1, 3, 1, 1, 3, 8]
def baseStart_3623833 : Nat := 118140960795 + 3623833 * 2 ^ 59
def prefixEnd_3623833 : Nat := 4983230072969 + 3 ^ 40 * 3623833 * 2
def baseEnd_3623833 : Nat := 620256046874875156807267

theorem tailTrace_3623833 : CollatzResearch.WordTrace tailWord_3623833 prefixEnd_3623833 620256046874875156807267 := by
  unfold tailWord_3623833
  simp only [CollatzResearch.WordTrace]
  refine ⟨132172047880479417248252153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88114698586986278165501435 132172047880479417248252153)
  ·
    refine ⟨99129035910359562936189115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132172047880479417248252153 99129035910359562936189115)
    ·
      refine ⟨148693553865539344404283673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99129035910359562936189115 148693553865539344404283673)
      ·
        refine ⟨111520165399154508303212755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 148693553865539344404283673 111520165399154508303212755)
        ·
          refine ⟨167280248098731762454819133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111520165399154508303212755 167280248098731762454819133)
          ·
            refine ⟨62730093037024410920557175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 167280248098731762454819133 62730093037024410920557175)
            ·
              refine ⟨94095139555536616380835763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62730093037024410920557175 94095139555536616380835763)
              ·
                refine ⟨141142709333304924571253645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 94095139555536616380835763 141142709333304924571253645)
                ·
                  refine ⟨52928515999989346714220117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 141142709333304924571253645 52928515999989346714220117)
                  ·
                    refine ⟨620256046874875156807267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 52928515999989346714220117 620256046874875156807267)
                    ·
                      rfl

theorem cell23_3623833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 1, 3, 8].length) (baseStart_3623833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3623833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3623833 prefixEnd_3623833 := by exact prefixLift 3623833
  have htrace : WordTrace (prefixWord ++ tailWord_3623833) baseStart_3623833 baseEnd_3623833 := by
    simpa [prefixWord, tailWord_3623833, baseEnd_3623833] using wordTrace_append hprefix tailTrace_3623833
  have hstable : (prefixWord ++ tailWord_3623833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3623833).length < 2 ^ (prefixWord ++ tailWord_3623833).sum := by decide
  have hdescent : baseEnd_3623833 < baseStart_3623833 := by decide
  rcases family_descends (prefixWord ++ tailWord_3623833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3623844 : List Nat := [2, 3, 1, 2, 1, 2, 3, 3, 1, 3, 2]
def baseStart_3623844 : Nat := 118140960795 + 3623844 * 2 ^ 59
def prefixEnd_3623844 : Nat := 4983230072969 + 3 ^ 40 * 3623844 * 2
def baseEnd_3623844 : Nat := 1860773788911824927384251

theorem tailTrace_3623844 : CollatzResearch.WordTrace tailWord_3623844 prefixEnd_3623844 1860773788911824927384251 := by
  unfold tailWord_3623844
  simp only [CollatzResearch.WordTrace]
  refine ⟨66086224541719783063451293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88114966055626377417935057 66086224541719783063451293)
  ·
    refine ⟨24782334203144918648794235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66086224541719783063451293 24782334203144918648794235)
    ·
      refine ⟨37173501304717377973191353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24782334203144918648794235 37173501304717377973191353)
      ·
        refine ⟨27880125978538033479893515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37173501304717377973191353 27880125978538033479893515)
        ·
          refine ⟨41820188967807050219840273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27880125978538033479893515 41820188967807050219840273)
          ·
            refine ⟨31365141725855287664880205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41820188967807050219840273 31365141725855287664880205)
            ·
              refine ⟨11761928147195732874330077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31365141725855287664880205 11761928147195732874330077)
              ·
                refine ⟨4410723055198399827873779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11761928147195732874330077 4410723055198399827873779)
                ·
                  refine ⟨6616084582797599741810669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4410723055198399827873779 6616084582797599741810669)
                  ·
                    refine ⟨2481031718549099903179001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6616084582797599741810669 2481031718549099903179001)
                    ·
                      refine ⟨1860773788911824927384251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2481031718549099903179001 1860773788911824927384251)
                      ·
                        rfl

theorem cell23_3623844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 3, 3, 1, 3, 2].length) (baseStart_3623844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3623844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3623844 prefixEnd_3623844 := by exact prefixLift 3623844
  have htrace : WordTrace (prefixWord ++ tailWord_3623844) baseStart_3623844 baseEnd_3623844 := by
    simpa [prefixWord, tailWord_3623844, baseEnd_3623844] using wordTrace_append hprefix tailTrace_3623844
  have hstable : (prefixWord ++ tailWord_3623844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3623844).length < 2 ^ (prefixWord ++ tailWord_3623844).sum := by decide
  have hdescent : baseEnd_3623844 < baseStart_3623844 := by decide
  rcases family_descends (prefixWord ++ tailWord_3623844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3623894 : List Nat := [5, 2, 1, 1, 2, 2, 1, 1, 2, 1, 5]
def baseStart_3623894 : Nat := 118140960795 + 3623894 * 2 ^ 59
def prefixEnd_3623894 : Nat := 4983230072969 + 3 ^ 40 * 3623894 * 2
def baseEnd_3623894 : Nat := 1860799462944549731759021

theorem tailTrace_3623894 : CollatzResearch.WordTrace tailWord_3623894 prefixEnd_3623894 1860799462944549731759021 := by
  unfold tailWord_3623894
  simp only [CollatzResearch.WordTrace]
  refine ⟨8260892045828651541638921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 88116181822172283110815157 8260892045828651541638921)
  ·
    refine ⟨6195669034371488656229191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8260892045828651541638921 6195669034371488656229191)
    ·
      refine ⟨9293503551557232984343787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6195669034371488656229191 9293503551557232984343787)
      ·
        refine ⟨13940255327335849476515681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9293503551557232984343787 13940255327335849476515681)
        ·
          refine ⟨10455191495501887107386761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13940255327335849476515681 10455191495501887107386761)
          ·
            refine ⟨7841393621626415330540071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10455191495501887107386761 7841393621626415330540071)
            ·
              refine ⟨11762090432439622995810107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7841393621626415330540071 11762090432439622995810107)
              ·
                refine ⟨17643135648659434493715161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11762090432439622995810107 17643135648659434493715161)
                ·
                  refine ⟨13232351736494575870286371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17643135648659434493715161 13232351736494575870286371)
                  ·
                    refine ⟨19848527604741863805429557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13232351736494575870286371 19848527604741863805429557)
                    ·
                      refine ⟨1860799462944549731759021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19848527604741863805429557 1860799462944549731759021)
                      ·
                        rfl

theorem cell23_3623894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 1, 1, 2, 1, 5].length) (baseStart_3623894 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3623894 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3623894 prefixEnd_3623894 := by exact prefixLift 3623894
  have htrace : WordTrace (prefixWord ++ tailWord_3623894) baseStart_3623894 baseEnd_3623894 := by
    simpa [prefixWord, tailWord_3623894, baseEnd_3623894] using wordTrace_append hprefix tailTrace_3623894
  have hstable : (prefixWord ++ tailWord_3623894).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3623894).length < 2 ^ (prefixWord ++ tailWord_3623894).sum := by decide
  have hdescent : baseEnd_3623894 < baseStart_3623894 := by decide
  rcases family_descends (prefixWord ++ tailWord_3623894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3623925 : List Nat := [1, 3, 5, 2, 1, 1, 1, 3, 2, 2, 2]
def baseStart_3623925 : Nat := 118140960795 + 3623925 * 2 ^ 59
def prefixEnd_3623925 : Nat := 4983230072969 + 3 ^ 40 * 3623925 * 2
def baseEnd_3623925 : Nat := 1860815380844839110471379

theorem tailTrace_3623925 : CollatzResearch.WordTrace tailWord_3623925 prefixEnd_3623925 1860815380844839110471379 := by
  unfold tailWord_3623925
  simp only [CollatzResearch.WordTrace]
  refine ⟨132175403396146116960601229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88116935597430744640400819 132175403396146116960601229)
  ·
    refine ⟨49565776273554793860225461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 132175403396146116960601229 49565776273554793860225461)
    ·
      refine ⟨4646791525645761924396137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 49565776273554793860225461 4646791525645761924396137)
      ·
        refine ⟨3485093644234321443297103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4646791525645761924396137 3485093644234321443297103)
        ·
          refine ⟨5227640466351482164945655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3485093644234321443297103 5227640466351482164945655)
          ·
            refine ⟨7841460699527223247418483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5227640466351482164945655 7841460699527223247418483)
            ·
              refine ⟨11762191049290834871127725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7841460699527223247418483 11762191049290834871127725)
              ·
                refine ⟨4410821643484063076672897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11762191049290834871127725 4410821643484063076672897)
                ·
                  refine ⟨3308116232613047307504673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4410821643484063076672897 3308116232613047307504673)
                  ·
                    refine ⟨2481087174459785480628505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3308116232613047307504673 2481087174459785480628505)
                    ·
                      refine ⟨1860815380844839110471379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2481087174459785480628505 1860815380844839110471379)
                      ·
                        rfl

theorem cell23_3623925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 1, 3, 2, 2, 2].length) (baseStart_3623925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3623925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3623925 prefixEnd_3623925 := by exact prefixLift 3623925
  have htrace : WordTrace (prefixWord ++ tailWord_3623925) baseStart_3623925 baseEnd_3623925 := by
    simpa [prefixWord, tailWord_3623925, baseEnd_3623925] using wordTrace_append hprefix tailTrace_3623925
  have hstable : (prefixWord ++ tailWord_3623925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3623925).length < 2 ^ (prefixWord ++ tailWord_3623925).sum := by decide
  have hdescent : baseEnd_3623925 < baseStart_3623925 := by decide
  rcases family_descends (prefixWord ++ tailWord_3623925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3623930 : List Nat := [3, 1, 1, 1, 1, 2, 1, 3, 3, 3, 4]
def baseStart_3623930 : Nat := 118140960795 + 3623930 * 2 ^ 59
def prefixEnd_3623930 : Nat := 4983230072969 + 3 ^ 40 * 3623930 * 2
def baseEnd_3623930 : Nat := 1860817948248111590908855

theorem tailTrace_3623930 : CollatzResearch.WordTrace tailWord_3623930 prefixEnd_3623930 1860817948248111590908855 := by
  unfold tailWord_3623930
  simp only [CollatzResearch.WordTrace]
  refine ⟨33043896440282000703633311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88117057174085335209688829 33043896440282000703633311)
  ·
    refine ⟨49565844660423001055449967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33043896440282000703633311 49565844660423001055449967)
    ·
      refine ⟨74348766990634501583174951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49565844660423001055449967 74348766990634501583174951)
      ·
        refine ⟨111523150485951752374762427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74348766990634501583174951 111523150485951752374762427)
        ·
          refine ⟨167284725728927628562143641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111523150485951752374762427 167284725728927628562143641)
          ·
            refine ⟨125463544296695721421607731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 167284725728927628562143641 125463544296695721421607731)
            ·
              refine ⟨188195316445043582132411597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 125463544296695721421607731 188195316445043582132411597)
              ·
                refine ⟨70573243666891343299654349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 188195316445043582132411597 70573243666891343299654349)
                ·
                  refine ⟨26464966375084253737370381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 70573243666891343299654349 26464966375084253737370381)
                  ·
                    refine ⟨9924362390656595151513893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26464966375084253737370381 9924362390656595151513893)
                    ·
                      refine ⟨1860817948248111590908855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9924362390656595151513893 1860817948248111590908855)
                      ·
                        rfl

theorem cell23_3623930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 3, 3, 3, 4].length) (baseStart_3623930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3623930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3623930 prefixEnd_3623930 := by exact prefixLift 3623930
  have htrace : WordTrace (prefixWord ++ tailWord_3623930) baseStart_3623930 baseEnd_3623930 := by
    simpa [prefixWord, tailWord_3623930, baseEnd_3623930] using wordTrace_append hprefix tailTrace_3623930
  have hstable : (prefixWord ++ tailWord_3623930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3623930).length < 2 ^ (prefixWord ++ tailWord_3623930).sum := by decide
  have hdescent : baseEnd_3623930 < baseStart_3623930 := by decide
  rcases family_descends (prefixWord ++ tailWord_3623930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3623947 : List Nat := [1, 1, 1, 1, 6, 2, 1, 3, 2, 1, 4]
def baseStart_3623947 : Nat := 118140960795 + 3623947 * 2 ^ 59
def prefixEnd_3623947 : Nat := 4983230072969 + 3 ^ 40 * 3623947 * 2
def baseEnd_3623947 : Nat := 1860826677419238024396277

theorem tailTrace_3623947 : CollatzResearch.WordTrace tailWord_3623947 prefixEnd_3623947 1860826677419238024396277 := by
  unfold tailWord_3623947
  simp only [CollatzResearch.WordTrace]
  refine ⟨132176205802066414717902095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88117470534710943145268063 132176205802066414717902095)
  ·
    refine ⟨198264308703099622076853143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132176205802066414717902095 198264308703099622076853143)
    ·
      refine ⟨297396463054649433115279715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198264308703099622076853143 297396463054649433115279715)
      ·
        refine ⟨446094694581974149672919573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 297396463054649433115279715 446094694581974149672919573)
        ·
          refine ⟨20910688808530038265918105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 446094694581974149672919573 20910688808530038265918105)
          ·
            refine ⟨15683016606397528699438579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20910688808530038265918105 15683016606397528699438579)
            ·
              refine ⟨23524524909596293049157869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15683016606397528699438579 23524524909596293049157869)
              ·
                refine ⟨8821696841098609893434201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23524524909596293049157869 8821696841098609893434201)
                ·
                  refine ⟨6616272630823957420075651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8821696841098609893434201 6616272630823957420075651)
                  ·
                    refine ⟨9924408946235936130113477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6616272630823957420075651 9924408946235936130113477)
                    ·
                      refine ⟨1860826677419238024396277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9924408946235936130113477 1860826677419238024396277)
                      ·
                        rfl

theorem cell23_3623947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 1, 3, 2, 1, 4].length) (baseStart_3623947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3623947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3623947 prefixEnd_3623947 := by exact prefixLift 3623947
  have htrace : WordTrace (prefixWord ++ tailWord_3623947) baseStart_3623947 baseEnd_3623947 := by
    simpa [prefixWord, tailWord_3623947, baseEnd_3623947] using wordTrace_append hprefix tailTrace_3623947
  have hstable : (prefixWord ++ tailWord_3623947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3623947).length < 2 ^ (prefixWord ++ tailWord_3623947).sum := by decide
  have hdescent : baseEnd_3623947 < baseStart_3623947 := by decide
  rcases family_descends (prefixWord ++ tailWord_3623947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3624014 : List Nat := [4, 1, 1, 1, 1, 3, 1, 2, 5, 1, 3]
def baseStart_3624014 : Nat := 118140960795 + 3624014 * 2 ^ 59
def prefixEnd_3624014 : Nat := 4983230072969 + 3 ^ 40 * 3624014 * 2
def baseEnd_3624014 : Nat := 1860861080623089262258469

theorem tailTrace_3624014 : CollatzResearch.WordTrace tailWord_3624014 prefixEnd_3624014 1860861080623089262258469 := by
  unfold tailWord_3624014
  simp only [CollatzResearch.WordTrace]
  refine ⟨16522331186602960645073887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 88119099661882456773727397 16522331186602960645073887)
  ·
    refine ⟨24783496779904440967610831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16522331186602960645073887 24783496779904440967610831)
    ·
      refine ⟨37175245169856661451416247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24783496779904440967610831 37175245169856661451416247)
      ·
        refine ⟨55762867754784992177124371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37175245169856661451416247 55762867754784992177124371)
        ·
          refine ⟨83644301632177488265686557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55762867754784992177124371 83644301632177488265686557)
          ·
            refine ⟨31366613112066558099632459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 83644301632177488265686557 31366613112066558099632459)
            ·
              refine ⟨47049919668099837149448689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31366613112066558099632459 47049919668099837149448689)
              ·
                refine ⟨35287439751074877862086517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47049919668099837149448689 35287439751074877862086517)
                ·
                  refine ⟨3308197476663269799570611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 35287439751074877862086517 3308197476663269799570611)
                  ·
                    refine ⟨4962296214994904699355917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3308197476663269799570611 4962296214994904699355917)
                    ·
                      refine ⟨1860861080623089262258469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4962296214994904699355917 1860861080623089262258469)
                      ·
                        rfl

theorem cell23_3624014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 2, 5, 1, 3].length) (baseStart_3624014 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3624014 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3624014 prefixEnd_3624014 := by exact prefixLift 3624014
  have htrace : WordTrace (prefixWord ++ tailWord_3624014) baseStart_3624014 baseEnd_3624014 := by
    simpa [prefixWord, tailWord_3624014, baseEnd_3624014] using wordTrace_append hprefix tailTrace_3624014
  have hstable : (prefixWord ++ tailWord_3624014).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3624014).length < 2 ^ (prefixWord ++ tailWord_3624014).sum := by decide
  have hdescent : baseEnd_3624014 < baseStart_3624014 := by decide
  rcases family_descends (prefixWord ++ tailWord_3624014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3624024 : List Nat := [2, 1, 2, 2, 1, 3, 2, 1, 4, 3, 2]
def baseStart_3624024 : Nat := 118140960795 + 3624024 * 2 ^ 59
def prefixEnd_3624024 : Nat := 4983230072969 + 3 ^ 40 * 3624024 * 2
def baseEnd_3624024 : Nat := 1860866215429634223133423

theorem tailTrace_3624024 : CollatzResearch.WordTrace tailWord_3624024 prefixEnd_3624024 1860866215429634223133423 := by
  unfold tailWord_3624024
  simp only [CollatzResearch.WordTrace]
  refine ⟨66089507111393728434227563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88119342815191637912303417 66089507111393728434227563)
  ·
    refine ⟨99134260667090592651341345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66089507111393728434227563 99134260667090592651341345)
    ·
      refine ⟨74350695500317944488506009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99134260667090592651341345 74350695500317944488506009)
      ·
        refine ⟨55763021625238458366379507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74350695500317944488506009 55763021625238458366379507)
        ·
          refine ⟨83644532437857687549569261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55763021625238458366379507 83644532437857687549569261)
          ·
            refine ⟨31366699664196632831088473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 83644532437857687549569261 31366699664196632831088473)
            ·
              refine ⟨23525024748147474623316355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31366699664196632831088473 23525024748147474623316355)
              ·
                refine ⟨35287537122221211934974533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23525024748147474623316355 35287537122221211934974533)
                ·
                  refine ⟨6616413210416477237807725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35287537122221211934974533 6616413210416477237807725)
                  ·
                    refine ⟨2481154953906178964177897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6616413210416477237807725 2481154953906178964177897)
                    ·
                      refine ⟨1860866215429634223133423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2481154953906178964177897 1860866215429634223133423)
                      ·
                        rfl

theorem cell23_3624024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 2, 1, 4, 3, 2].length) (baseStart_3624024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3624024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3624024 prefixEnd_3624024 := by exact prefixLift 3624024
  have htrace : WordTrace (prefixWord ++ tailWord_3624024) baseStart_3624024 baseEnd_3624024 := by
    simpa [prefixWord, tailWord_3624024, baseEnd_3624024] using wordTrace_append hprefix tailTrace_3624024
  have hstable : (prefixWord ++ tailWord_3624024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3624024).length < 2 ^ (prefixWord ++ tailWord_3624024).sum := by decide
  have hdescent : baseEnd_3624024 < baseStart_3624024 := by decide
  rcases family_descends (prefixWord ++ tailWord_3624024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3624031 : List Nat := [1, 1, 2, 3, 1, 1, 3, 6, 1, 1, 3]
def baseStart_3624031 : Nat := 118140960795 + 3624031 * 2 ^ 59
def prefixEnd_3624031 : Nat := 4983230072969 + 3 ^ 40 * 3624031 * 2
def baseEnd_3624031 : Nat := 1860869809794215695745891

theorem tailTrace_3624031 : CollatzResearch.WordTrace tailWord_3624031 prefixEnd_3624031 1860869809794215695745891 := by
  unfold tailWord_3624031
  simp only [CollatzResearch.WordTrace]
  refine ⟨132179269533762097063959947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88119513022508064709306631 132179269533762097063959947)
  ·
    refine ⟨198268904300643145595939921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132179269533762097063959947 198268904300643145595939921)
    ·
      refine ⟨148701678225482359196954941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 198268904300643145595939921 148701678225482359196954941)
      ·
        refine ⟨55763129334555884698858103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 148701678225482359196954941 55763129334555884698858103)
        ·
          refine ⟨83644694001833827048287155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55763129334555884698858103 83644694001833827048287155)
          ·
            refine ⟨125467041002750740572430733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83644694001833827048287155 125467041002750740572430733)
            ·
              refine ⟨47050140376031527714661525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 125467041002750740572430733 47050140376031527714661525)
              ·
                refine ⟨2205475330126477861624759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 47050140376031527714661525 2205475330126477861624759)
                ·
                  refine ⟨3308212995189716792437139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2205475330126477861624759 3308212995189716792437139)
                  ·
                    refine ⟨4962319492784575188655709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3308212995189716792437139 4962319492784575188655709)
                    ·
                      refine ⟨1860869809794215695745891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4962319492784575188655709 1860869809794215695745891)
                      ·
                        rfl

theorem cell23_3624031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 6, 1, 1, 3].length) (baseStart_3624031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3624031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3624031 prefixEnd_3624031 := by exact prefixLift 3624031
  have htrace : WordTrace (prefixWord ++ tailWord_3624031) baseStart_3624031 baseEnd_3624031 := by
    simpa [prefixWord, tailWord_3624031, baseEnd_3624031] using wordTrace_append hprefix tailTrace_3624031
  have hstable : (prefixWord ++ tailWord_3624031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3624031).length < 2 ^ (prefixWord ++ tailWord_3624031).sum := by decide
  have hdescent : baseEnd_3624031 < baseStart_3624031 := by decide
  rcases family_descends (prefixWord ++ tailWord_3624031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3624065 : List Nat := [1, 2, 4, 2, 2, 3, 1, 3, 1, 1, 3]
def baseStart_3624065 : Nat := 118140960795 + 3624065 * 2 ^ 59
def prefixEnd_3624065 : Nat := 4983230072969 + 3 ^ 40 * 3624065 * 2
def baseEnd_3624065 : Nat := 1860887268136468562720735

theorem tailTrace_3624065 : CollatzResearch.WordTrace tailWord_3624065 prefixEnd_3624065 1860887268136468562720735 := by
  unfold tailWord_3624065
  simp only [CollatzResearch.WordTrace]
  refine ⟨132180509615638920870697649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88120339743759280580465099 132180509615638920870697649)
  ·
    refine ⟨99135382211729190653023237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132180509615638920870697649 99135382211729190653023237)
    ·
      refine ⟨18587884164699223247441857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 99135382211729190653023237 18587884164699223247441857)
      ·
        refine ⟨13940913123524417435581393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18587884164699223247441857 13940913123524417435581393)
        ·
          refine ⟨10455684842643313076686045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13940913123524417435581393 10455684842643313076686045)
          ·
            refine ⟨3920881815991242403757267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10455684842643313076686045 3920881815991242403757267)
            ·
              refine ⟨5881322723986863605635901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3920881815991242403757267 5881322723986863605635901)
              ·
                refine ⟨2205496021495073852113463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5881322723986863605635901 2205496021495073852113463)
                ·
                  refine ⟨3308244032242610778170195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2205496021495073852113463 3308244032242610778170195)
                  ·
                    refine ⟨4962366048363916167255293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3308244032242610778170195 4962366048363916167255293)
                    ·
                      refine ⟨1860887268136468562720735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4962366048363916167255293 1860887268136468562720735)
                      ·
                        rfl

theorem cell23_3624065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 3, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 3, 1, 3, 1, 1, 3].length) (baseStart_3624065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3624065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3624065 prefixEnd_3624065 := by exact prefixLift 3624065
  have htrace : WordTrace (prefixWord ++ tailWord_3624065) baseStart_3624065 baseEnd_3624065 := by
    simpa [prefixWord, tailWord_3624065, baseEnd_3624065] using wordTrace_append hprefix tailTrace_3624065
  have hstable : (prefixWord ++ tailWord_3624065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3624065).length < 2 ^ (prefixWord ++ tailWord_3624065).sum := by decide
  have hdescent : baseEnd_3624065 < baseStart_3624065 := by decide
  rcases family_descends (prefixWord ++ tailWord_3624065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3624067 : List Nat := [1, 1, 1, 3, 3, 2, 2, 1, 3, 2, 4]
def baseStart_3624067 : Nat := 118140960795 + 3624067 * 2 ^ 59
def prefixEnd_3624067 : Nat := 4983230072969 + 3 ^ 40 * 3624067 * 2
def baseEnd_3624067 : Nat := 1860888295097777554895725

theorem tailTrace_3624067 : CollatzResearch.WordTrace tailWord_3624067 prefixEnd_3624067 1860888295097777554895725 := by
  unfold tailWord_3624067
  simp only [CollatzResearch.WordTrace]
  refine ⟨132180582561631675212270455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88120388374421116808180303 132180582561631675212270455)
  ·
    refine ⟨198270873842447512818405683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132180582561631675212270455 198270873842447512818405683)
    ·
      refine ⟨297406310763671269227608525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198270873842447512818405683 297406310763671269227608525)
      ·
        refine ⟨111527366536376725960353197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 297406310763671269227608525 111527366536376725960353197)
        ·
          refine ⟨41822762451141272235132449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 111527366536376725960353197 41822762451141272235132449)
          ·
            refine ⟨31367071838355954176349337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41822762451141272235132449 31367071838355954176349337)
            ·
              refine ⟨23525303878766965632262003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31367071838355954176349337 23525303878766965632262003)
              ·
                refine ⟨35287955818150448448393005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23525303878766965632262003 35287955818150448448393005)
                ·
                  refine ⟨13232983431806418168147377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35287955818150448448393005 13232983431806418168147377)
                  ·
                    refine ⟨9924737573854813626110533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13232983431806418168147377 9924737573854813626110533)
                    ·
                      refine ⟨1860888295097777554895725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9924737573854813626110533 1860888295097777554895725)
                      ·
                        rfl

theorem cell23_3624067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 2, 1, 3, 2, 4].length) (baseStart_3624067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3624067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3624067 prefixEnd_3624067 := by exact prefixLift 3624067
  have htrace : WordTrace (prefixWord ++ tailWord_3624067) baseStart_3624067 baseEnd_3624067 := by
    simpa [prefixWord, tailWord_3624067, baseEnd_3624067] using wordTrace_append hprefix tailTrace_3624067
  have hstable : (prefixWord ++ tailWord_3624067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3624067).length < 2 ^ (prefixWord ++ tailWord_3624067).sum := by decide
  have hdescent : baseEnd_3624067 < baseStart_3624067 := by decide
  rcases family_descends (prefixWord ++ tailWord_3624067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3624074 : List Nat := [3, 1, 2, 3, 1, 1, 4, 1, 1, 1, 5]
def baseStart_3624074 : Nat := 118140960795 + 3624074 * 2 ^ 59
def prefixEnd_3624074 : Nat := 4983230072969 + 3 ^ 40 * 3624074 * 2
def baseEnd_3624074 : Nat := 1860891889462359027508193

theorem tailTrace_3624074 : CollatzResearch.WordTrace tailWord_3624074 prefixEnd_3624074 1860891889462359027508193 := by
  unfold tailWord_3624074
  simp only [CollatzResearch.WordTrace]
  refine ⟨33045209468151578851943819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88120558581737543605183517 33045209468151578851943819)
  ·
    refine ⟨49567814202227368277915729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33045209468151578851943819 49567814202227368277915729)
    ·
      refine ⟨37175860651670526208436797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49567814202227368277915729 37175860651670526208436797)
      ·
        refine ⟨13940947744376447328163799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37175860651670526208436797 13940947744376447328163799)
        ·
          refine ⟨20911421616564670992245699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13940947744376447328163799 20911421616564670992245699)
          ·
            refine ⟨31367132424847006488368549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20911421616564670992245699 31367132424847006488368549)
            ·
              refine ⟨5881337329658813716569103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31367132424847006488368549 5881337329658813716569103)
              ·
                refine ⟨8822005994488220574853655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5881337329658813716569103 8822005994488220574853655)
                ·
                  refine ⟨13233008991732330862280483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8822005994488220574853655 13233008991732330862280483)
                  ·
                    refine ⟨19849513487598496293420725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13233008991732330862280483 19849513487598496293420725)
                    ·
                      refine ⟨1860891889462359027508193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19849513487598496293420725 1860891889462359027508193)
                      ·
                        rfl

theorem cell23_3624074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 4, 1, 1, 1, 5].length) (baseStart_3624074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3624074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3624074 prefixEnd_3624074 := by exact prefixLift 3624074
  have htrace : WordTrace (prefixWord ++ tailWord_3624074) baseStart_3624074 baseEnd_3624074 := by
    simpa [prefixWord, tailWord_3624074, baseEnd_3624074] using wordTrace_append hprefix tailTrace_3624074
  have hstable : (prefixWord ++ tailWord_3624074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3624074).length < 2 ^ (prefixWord ++ tailWord_3624074).sum := by decide
  have hdescent : baseEnd_3624074 < baseStart_3624074 := by decide
  rcases family_descends (prefixWord ++ tailWord_3624074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3624088 : List Nat := [2, 1, 2, 4, 2, 1, 3, 1, 3, 2, 2]
def baseStart_3624088 : Nat := 118140960795 + 3624088 * 2 ^ 59
def prefixEnd_3624088 : Nat := 4983230072969 + 3 ^ 40 * 3624088 * 2
def baseEnd_3624088 : Nat := 1860899078191521972733129

theorem tailTrace_3624088 : CollatzResearch.WordTrace tailWord_3624088 prefixEnd_3624088 1860899078191521972733129 := by
  unfold tailWord_3624088
  simp only [CollatzResearch.WordTrace]
  refine ⟨66090674247277797899392459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88120898996370397199189945 66090674247277797899392459)
  ·
    refine ⟨99136011370916696849088689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66090674247277797899392459 99136011370916696849088689)
    ·
      refine ⟨74352008528187522636816517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99136011370916696849088689 74352008528187522636816517)
      ·
        refine ⟨13941001599035160494403097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 74352008528187522636816517 13941001599035160494403097)
        ·
          refine ⟨10455751199276370370802323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13941001599035160494403097 10455751199276370370802323)
          ·
            refine ⟨15683626798914555556203485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10455751199276370370802323 15683626798914555556203485)
            ·
              refine ⟨5881360049592958333576307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15683626798914555556203485 5881360049592958333576307)
              ·
                refine ⟨8822040074389437500364461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5881360049592958333576307 8822040074389437500364461)
                ·
                  refine ⟨3308265027896039062636673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8822040074389437500364461 3308265027896039062636673)
                  ·
                    refine ⟨2481198770922029296977505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3308265027896039062636673 2481198770922029296977505)
                    ·
                      refine ⟨1860899078191521972733129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2481198770922029296977505 1860899078191521972733129)
                      ·
                        rfl

theorem cell23_3624088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 3, 1, 3, 2, 2].length) (baseStart_3624088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3624088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3624088 prefixEnd_3624088 := by exact prefixLift 3624088
  have htrace : WordTrace (prefixWord ++ tailWord_3624088) baseStart_3624088 baseEnd_3624088 := by
    simpa [prefixWord, tailWord_3624088, baseEnd_3624088] using wordTrace_append hprefix tailTrace_3624088
  have hstable : (prefixWord ++ tailWord_3624088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3624088).length < 2 ^ (prefixWord ++ tailWord_3624088).sum := by decide
  have hdescent : baseEnd_3624088 < baseStart_3624088 := by decide
  rcases family_descends (prefixWord ++ tailWord_3624088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3624094 : List Nat := [4, 3, 1, 1, 2, 1, 1, 10]
def baseStart_3624094 : Nat := 118140960795 + 3624094 * 2 ^ 59
def prefixEnd_3624094 : Nat := 4983230072969 + 3 ^ 40 * 3624094 * 2
def baseEnd_3624094 : Nat := 68922302187979590713263

theorem tailTrace_3624094 : CollatzResearch.WordTrace tailWord_3624094 prefixEnd_3624094 68922302187979590713263 := by
  unfold tailWord_3624094
  simp only [CollatzResearch.WordTrace]
  refine ⟨16522695916566732352937917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 88121044888355905882335557 16522695916566732352937917)
  ·
    refine ⟨6196010968712524632351719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16522695916566732352937917 6196010968712524632351719)
    ·
      refine ⟨9294016453068786948527579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6196010968712524632351719 9294016453068786948527579)
      ·
        refine ⟨13941024679603180422791369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9294016453068786948527579 13941024679603180422791369)
        ·
          refine ⟨10455768509702385317093527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13941024679603180422791369 10455768509702385317093527)
          ·
            refine ⟨15683652764553577975640291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10455768509702385317093527 15683652764553577975640291)
            ·
              refine ⟨23525479146830366963460437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15683652764553577975640291 23525479146830366963460437)
              ·
                refine ⟨68922302187979590713263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 23525479146830366963460437 68922302187979590713263)
                ·
                  rfl

theorem cell23_3624094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 1, 10].length) (baseStart_3624094 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3624094 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3624094 prefixEnd_3624094 := by exact prefixLift 3624094
  have htrace : WordTrace (prefixWord ++ tailWord_3624094) baseStart_3624094 baseEnd_3624094 := by
    simpa [prefixWord, tailWord_3624094, baseEnd_3624094] using wordTrace_append hprefix tailTrace_3624094
  have hstable : (prefixWord ++ tailWord_3624094).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3624094).length < 2 ^ (prefixWord ++ tailWord_3624094).sum := by decide
  have hdescent : baseEnd_3624094 < baseStart_3624094 := by decide
  rcases family_descends (prefixWord ++ tailWord_3624094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3624097 : List Nat := [1, 2, 3, 3, 1, 1, 1, 1, 2, 2, 6]
def baseStart_3624097 : Nat := 118140960795 + 3624097 * 2 ^ 59
def prefixEnd_3624097 : Nat := 4983230072969 + 3 ^ 40 * 3624097 * 2
def baseEnd_3624097 : Nat := 1860903699517412437520587

theorem tailTrace_3624097 : CollatzResearch.WordTrace tailWord_3624097 prefixEnd_3624097 1860903699517412437520587 := by
  unfold tailWord_3624097
  simp only [CollatzResearch.WordTrace]
  refine ⟨132181676751522990335862545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88121117834348660223908363 132181676751522990335862545)
  ·
    refine ⟨99136257563642242751896909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132181676751522990335862545 99136257563642242751896909)
    ·
      refine ⟨37176096586365841031961341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 99136257563642242751896909 37176096586365841031961341)
      ·
        refine ⟨13941036219887190386985503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37176096586365841031961341 13941036219887190386985503)
        ·
          refine ⟨20911554329830785580478255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13941036219887190386985503 20911554329830785580478255)
          ·
            refine ⟨31367331494746178370717383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20911554329830785580478255 31367331494746178370717383)
            ·
              refine ⟨47050997242119267556076075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31367331494746178370717383 47050997242119267556076075)
              ·
                refine ⟨70576495863178901334114113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47050997242119267556076075 70576495863178901334114113)
                ·
                  refine ⟨52932371897384176000585585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 70576495863178901334114113 52932371897384176000585585)
                  ·
                    refine ⟨39699278923038132000439189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 52932371897384176000585585 39699278923038132000439189)
                    ·
                      refine ⟨1860903699517412437520587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 39699278923038132000439189 1860903699517412437520587)
                      ·
                        rfl

theorem cell23_3624097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 1, 2, 2, 6].length) (baseStart_3624097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3624097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3624097 prefixEnd_3624097 := by exact prefixLift 3624097
  have htrace : WordTrace (prefixWord ++ tailWord_3624097) baseStart_3624097 baseEnd_3624097 := by
    simpa [prefixWord, tailWord_3624097, baseEnd_3624097] using wordTrace_append hprefix tailTrace_3624097
  have hstable : (prefixWord ++ tailWord_3624097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3624097).length < 2 ^ (prefixWord ++ tailWord_3624097).sum := by decide
  have hdescent : baseEnd_3624097 < baseStart_3624097 := by decide
  rcases family_descends (prefixWord ++ tailWord_3624097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3624098 : List Nat := [3, 3, 1, 3, 2, 1, 1, 3, 2, 4]
def baseStart_3624098 : Nat := 118140960795 + 3624098 * 2 ^ 59
def prefixEnd_3624098 : Nat := 4983230072969 + 3 ^ 40 * 3624098 * 2
def baseEnd_3624098 : Nat := 620301404332688977869361

theorem tailTrace_3624098 : CollatzResearch.WordTrace tailWord_3624098 prefixEnd_3624098 620301404332688977869361 := by
  unfold tailWord_3624098
  simp only [CollatzResearch.WordTrace]
  refine ⟨33045428306129841876662237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88121142149679578337765965 33045428306129841876662237)
  ·
    refine ⟨12392035614798690703748339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33045428306129841876662237 12392035614798690703748339)
    ·
      refine ⟨18588053422198036055622509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12392035614798690703748339 18588053422198036055622509)
      ·
        refine ⟨6970520033324263520858441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18588053422198036055622509 6970520033324263520858441)
        ·
          refine ⟨5227890024993197640643831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6970520033324263520858441 5227890024993197640643831)
          ·
            refine ⟨7841835037489796460965747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5227890024993197640643831 7841835037489796460965747)
            ·
              refine ⟨11762752556234694691448621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7841835037489796460965747 11762752556234694691448621)
              ·
                refine ⟨4411032208588010509293233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11762752556234694691448621 4411032208588010509293233)
                ·
                  refine ⟨3308274156441007881969925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4411032208588010509293233 3308274156441007881969925)
                  ·
                    refine ⟨620301404332688977869361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3308274156441007881969925 620301404332688977869361)
                    ·
                      rfl

theorem cell23_3624098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 1, 3, 2, 4].length) (baseStart_3624098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3624098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3624098 prefixEnd_3624098 := by exact prefixLift 3624098
  have htrace : WordTrace (prefixWord ++ tailWord_3624098) baseStart_3624098 baseEnd_3624098 := by
    simpa [prefixWord, tailWord_3624098, baseEnd_3624098] using wordTrace_append hprefix tailTrace_3624098
  have hstable : (prefixWord ++ tailWord_3624098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3624098).length < 2 ^ (prefixWord ++ tailWord_3624098).sum := by decide
  have hdescent : baseEnd_3624098 < baseStart_3624098 := by decide
  rcases family_descends (prefixWord ++ tailWord_3624098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3624138 : List Nat := [3, 1, 2, 1, 3, 3, 2, 2, 2, 1, 3]
def baseStart_3624138 : Nat := 118140960795 + 3624138 * 2 ^ 59
def prefixEnd_3624138 : Nat := 4983230072969 + 3 ^ 40 * 3624138 * 2
def baseEnd_3624138 : Nat := 1860924752224246777107899

theorem tailTrace_3624138 : CollatzResearch.WordTrace tailWord_3624138 prefixEnd_3624138 1860924752224246777107899 := by
  unfold tailWord_3624138
  simp only [CollatzResearch.WordTrace]
  refine ⟨33045793036093613584526267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88122114762916302892070045 33045793036093613584526267)
  ·
    refine ⟨49568689554140420376789401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33045793036093613584526267 49568689554140420376789401)
    ·
      refine ⟨37176517165605315282592051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49568689554140420376789401 37176517165605315282592051)
      ·
        refine ⟨55764775748407972923888077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37176517165605315282592051 55764775748407972923888077)
        ·
          refine ⟨20911790905652989846458029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55764775748407972923888077 20911790905652989846458029)
          ·
            refine ⟨7841921589619871192421761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20911790905652989846458029 7841921589619871192421761)
            ·
              refine ⟨5881441192214903394316321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7841921589619871192421761 5881441192214903394316321)
              ·
                refine ⟨4411080894161177545737241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5881441192214903394316321 4411080894161177545737241)
                ·
                  refine ⟨3308310670620883159302931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4411080894161177545737241 3308310670620883159302931)
                  ·
                    refine ⟨4962466005931324738954397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3308310670620883159302931 4962466005931324738954397)
                    ·
                      refine ⟨1860924752224246777107899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4962466005931324738954397 1860924752224246777107899)
                      ·
                        rfl

theorem cell23_3624138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 2, 2, 2, 1, 3].length) (baseStart_3624138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3624138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3624138 prefixEnd_3624138 := by exact prefixLift 3624138
  have htrace : WordTrace (prefixWord ++ tailWord_3624138) baseStart_3624138 baseEnd_3624138 := by
    simpa [prefixWord, tailWord_3624138, baseEnd_3624138] using wordTrace_append hprefix tailTrace_3624138
  have hstable : (prefixWord ++ tailWord_3624138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3624138).length < 2 ^ (prefixWord ++ tailWord_3624138).sum := by decide
  have hdescent : baseEnd_3624138 < baseStart_3624138 := by decide
  rcases family_descends (prefixWord ++ tailWord_3624138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3624161 : List Nat := [1, 2, 3, 1, 3, 2, 1, 3, 1, 4, 2]
def baseStart_3624161 : Nat := 118140960795 + 3624161 * 2 ^ 59
def prefixEnd_3624161 : Nat := 4983230072969 + 3 ^ 40 * 3624161 * 2
def baseEnd_3624161 : Nat := 1860936562279300187120293

theorem tailTrace_3624161 : CollatzResearch.WordTrace tailWord_3624161 prefixEnd_3624161 1860936562279300187120293 := by
  unfold tailWord_3624161
  simp only [CollatzResearch.WordTrace]
  refine ⟨132184011023291129266192337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88122674015527419510794891 132184011023291129266192337)
  ·
    refine ⟨99138008267468346949644253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132184011023291129266192337 99138008267468346949644253)
    ·
      refine ⟨37176753100300630106116595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 99138008267468346949644253 37176753100300630106116595)
      ·
        refine ⟨55765129650450945159174893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37176753100300630106116595 55765129650450945159174893)
        ·
          refine ⟨20911923618919104434690585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55765129650450945159174893 20911923618919104434690585)
          ·
            refine ⟨15683942714189328326017939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20911923618919104434690585 15683942714189328326017939)
            ·
              refine ⟨23525914071283992489026909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15683942714189328326017939 23525914071283992489026909)
              ·
                refine ⟨8822217776731497183385091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23525914071283992489026909 8822217776731497183385091)
                ·
                  refine ⟨13233326665097245775077637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8822217776731497183385091 13233326665097245775077637)
                  ·
                    refine ⟨2481248749705733582827057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13233326665097245775077637 2481248749705733582827057)
                    ·
                      refine ⟨1860936562279300187120293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2481248749705733582827057 1860936562279300187120293)
                      ·
                        rfl

theorem cell23_3624161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 1, 3, 1, 4, 2].length) (baseStart_3624161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3624161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3624161 prefixEnd_3624161 := by exact prefixLift 3624161
  have htrace : WordTrace (prefixWord ++ tailWord_3624161) baseStart_3624161 baseEnd_3624161 := by
    simpa [prefixWord, tailWord_3624161, baseEnd_3624161] using wordTrace_append hprefix tailTrace_3624161
  have hstable : (prefixWord ++ tailWord_3624161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3624161).length < 2 ^ (prefixWord ++ tailWord_3624161).sum := by decide
  have hdescent : baseEnd_3624161 < baseStart_3624161 := by decide
  rcases family_descends (prefixWord ++ tailWord_3624161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3624177 : List Nat := [1, 2, 2, 2, 2, 1, 1, 2, 1, 2, 7]
def baseStart_3624177 : Nat := 118140960795 + 3624177 * 2 ^ 59
def prefixEnd_3624177 : Nat := 4983230072969 + 3 ^ 40 * 3624177 * 2
def baseEnd_3624177 : Nat := 1860944777969772124520219

theorem tailTrace_3624177 : CollatzResearch.WordTrace tailWord_3624177 prefixEnd_3624177 1860944777969772124520219 := by
  unfold tailWord_3624177
  simp only [CollatzResearch.WordTrace]
  refine ⟨132184594591233163998774785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88123063060822109332516523 132184594591233163998774785)
  ·
    refine ⟨99138445943424872999081089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132184594591233163998774785 99138445943424872999081089)
    ·
      refine ⟨74353834457568654749310817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99138445943424872999081089 74353834457568654749310817)
      ·
        refine ⟨55765375843176491061983113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74353834457568654749310817 55765375843176491061983113)
        ·
          refine ⟨41824031882382368296487335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55765375843176491061983113 41824031882382368296487335)
          ·
            refine ⟨62736047823573552444731003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41824031882382368296487335 62736047823573552444731003)
            ·
              refine ⟨94104071735360328667096505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62736047823573552444731003 94104071735360328667096505)
              ·
                refine ⟨70578053801520246500322379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 94104071735360328667096505 70578053801520246500322379)
                ·
                  refine ⟨105867080702280369750483569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 70578053801520246500322379 105867080702280369750483569)
                  ·
                    refine ⟨79400310526710277312862677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 105867080702280369750483569 79400310526710277312862677)
                    ·
                      refine ⟨1860944777969772124520219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 79400310526710277312862677 1860944777969772124520219)
                      ·
                        rfl

theorem cell23_3624177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 2, 1, 2, 7].length) (baseStart_3624177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3624177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3624177 prefixEnd_3624177 := by exact prefixLift 3624177
  have htrace : WordTrace (prefixWord ++ tailWord_3624177) baseStart_3624177 baseEnd_3624177 := by
    simpa [prefixWord, tailWord_3624177, baseEnd_3624177] using wordTrace_append hprefix tailTrace_3624177
  have hstable : (prefixWord ++ tailWord_3624177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3624177).length < 2 ^ (prefixWord ++ tailWord_3624177).sum := by decide
  have hdescent : baseEnd_3624177 < baseStart_3624177 := by decide
  rcases family_descends (prefixWord ++ tailWord_3624177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3624195 : List Nat := [1, 1, 1, 3, 2, 6, 1, 2, 2, 2, 2]
def baseStart_3624195 : Nat := 118140960795 + 3624195 * 2 ^ 59
def prefixEnd_3624195 : Nat := 4983230072969 + 3 ^ 40 * 3624195 * 2
def baseEnd_3624195 : Nat := 1860954020621553054095137

theorem tailTrace_3624195 : CollatzResearch.WordTrace tailWord_3624195 prefixEnd_3624195 1860954020621553054095137 := by
  unfold tailWord_3624195
  simp only [CollatzResearch.WordTrace]
  refine ⟨132185251105167953072930039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88123500736778635381953359 132185251105167953072930039)
  ·
    refine ⟨198277876657751929609395059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132185251105167953072930039 198277876657751929609395059)
    ·
      refine ⟨297416814986627894414092589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198277876657751929609395059 297416814986627894414092589)
      ·
        refine ⟨111531305619985460405284721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 297416814986627894414092589 111531305619985460405284721)
        ·
          refine ⟨83648479214989095303963541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 111531305619985460405284721 83648479214989095303963541)
          ·
            refine ⟨3921022463202613842373291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 83648479214989095303963541 3921022463202613842373291)
            ·
              refine ⟨5881533694803920763559937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3921022463202613842373291 5881533694803920763559937)
              ·
                refine ⟨4411150271102940572669953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5881533694803920763559937 4411150271102940572669953)
                ·
                  refine ⟨3308362703327205429502465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4411150271102940572669953 3308362703327205429502465)
                  ·
                    refine ⟨2481272027495404072126849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3308362703327205429502465 2481272027495404072126849)
                    ·
                      refine ⟨1860954020621553054095137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2481272027495404072126849 1860954020621553054095137)
                      ·
                        rfl

theorem cell23_3624195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 6, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 6, 1, 2, 2, 2, 2].length) (baseStart_3624195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3624195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3624195 prefixEnd_3624195 := by exact prefixLift 3624195
  have htrace : WordTrace (prefixWord ++ tailWord_3624195) baseStart_3624195 baseEnd_3624195 := by
    simpa [prefixWord, tailWord_3624195, baseEnd_3624195] using wordTrace_append hprefix tailTrace_3624195
  have hstable : (prefixWord ++ tailWord_3624195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3624195).length < 2 ^ (prefixWord ++ tailWord_3624195).sum := by decide
  have hdescent : baseEnd_3624195 < baseStart_3624195 := by decide
  rcases family_descends (prefixWord ++ tailWord_3624195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3624288 : List Nat := [2, 1, 1, 3, 4, 2, 2, 1, 2, 2, 3]
def baseStart_3624288 : Nat := 118140960795 + 3624288 * 2 ^ 59
def prefixEnd_3624288 : Nat := 4983230072969 + 3 ^ 40 * 3624288 * 2
def baseEnd_3624288 : Nat := 1861001774322421190232209

theorem tailTrace_3624288 : CollatzResearch.WordTrace tailWord_3624288 prefixEnd_3624288 1861001774322421190232209 := by
  unfold tailWord_3624288
  simp only [CollatzResearch.WordTrace]
  refine ⟨66094321546915514978032759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88125762062554019970710345 66094321546915514978032759)
  ·
    refine ⟨99141482320373272467049139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66094321546915514978032759 99141482320373272467049139)
    ·
      refine ⟨148712223480559908700573709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99141482320373272467049139 148712223480559908700573709)
      ·
        refine ⟨55767083805209965762715141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 148712223480559908700573709 55767083805209965762715141)
        ·
          refine ⟨10456328213476868580509089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 55767083805209965762715141 10456328213476868580509089)
          ·
            refine ⟨7842246160107651435381817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10456328213476868580509089 7842246160107651435381817)
            ·
              refine ⟨5881684620080738576536363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7842246160107651435381817 5881684620080738576536363)
              ·
                refine ⟨8822526930121107864804545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5881684620080738576536363 8822526930121107864804545)
                ·
                  refine ⟨6616895197590830898603409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8822526930121107864804545 6616895197590830898603409)
                  ·
                    refine ⟨4962671398193123173952557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6616895197590830898603409 4962671398193123173952557)
                    ·
                      refine ⟨1861001774322421190232209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4962671398193123173952557 1861001774322421190232209)
                      ·
                        rfl

theorem cell23_3624288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 2, 1, 2, 2, 3].length) (baseStart_3624288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3624288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3624288 prefixEnd_3624288 := by exact prefixLift 3624288
  have htrace : WordTrace (prefixWord ++ tailWord_3624288) baseStart_3624288 baseEnd_3624288 := by
    simpa [prefixWord, tailWord_3624288, baseEnd_3624288] using wordTrace_append hprefix tailTrace_3624288
  have hstable : (prefixWord ++ tailWord_3624288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3624288).length < 2 ^ (prefixWord ++ tailWord_3624288).sum := by decide
  have hdescent : baseEnd_3624288 < baseStart_3624288 := by decide
  rcases family_descends (prefixWord ++ tailWord_3624288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3624341 : List Nat := [1, 3, 2, 1, 1, 2, 4, 1, 3, 1, 4]
def baseStart_3624341 : Nat := 118140960795 + 3624341 * 2 ^ 59
def prefixEnd_3624341 : Nat := 4983230072969 + 3 ^ 40 * 3624341 * 2
def baseEnd_3624341 : Nat := 1861028988797109482869465

theorem tailTrace_3624341 : CollatzResearch.WordTrace tailWord_3624341 prefixEnd_3624341 1861028988797109482869465 := by
  unfold tailWord_3624341
  simp only [CollatzResearch.WordTrace]
  refine ⟨132190576162639020007744877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88127050775092680005163251 132190576162639020007744877)
  ·
    refine ⟨49571466060989632502904329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 132190576162639020007744877 49571466060989632502904329)
    ·
      refine ⟨37178599545742224377178247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49571466060989632502904329 37178599545742224377178247)
      ·
        refine ⟨55767899318613336565767371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37178599545742224377178247 55767899318613336565767371)
        ·
          refine ⟨83651848977920004848651057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55767899318613336565767371 83651848977920004848651057)
          ·
            refine ⟨62738886733440003636488293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83651848977920004848651057 62738886733440003636488293)
            ·
              refine ⟨11763541262520000681841555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 62738886733440003636488293 11763541262520000681841555)
              ·
                refine ⟨17645311893780001022762333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11763541262520000681841555 17645311893780001022762333)
                ·
                  refine ⟨6616991960167500383535875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17645311893780001022762333 6616991960167500383535875)
                  ·
                    refine ⟨9925487940251250575303813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6616991960167500383535875 9925487940251250575303813)
                    ·
                      refine ⟨1861028988797109482869465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9925487940251250575303813 1861028988797109482869465)
                      ·
                        rfl

theorem cell23_3624341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 4, 1, 3, 1, 4].length) (baseStart_3624341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3624341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3624341 prefixEnd_3624341 := by exact prefixLift 3624341
  have htrace : WordTrace (prefixWord ++ tailWord_3624341) baseStart_3624341 baseEnd_3624341 := by
    simpa [prefixWord, tailWord_3624341, baseEnd_3624341] using wordTrace_append hprefix tailTrace_3624341
  have hstable : (prefixWord ++ tailWord_3624341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3624341).length < 2 ^ (prefixWord ++ tailWord_3624341).sum := by decide
  have hdescent : baseEnd_3624341 < baseStart_3624341 := by decide
  rcases family_descends (prefixWord ++ tailWord_3624341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3624345 : List Nat := [1, 2, 1, 2, 1, 7, 1, 1, 2, 3, 2]
def baseStart_3624345 : Nat := 118140960795 + 3624345 * 2 ^ 59
def prefixEnd_3624345 : Nat := 4983230072969 + 3 ^ 40 * 3624345 * 2
def baseEnd_3624345 : Nat := 1861031042719727467219447

theorem tailTrace_3624345 : CollatzResearch.WordTrace tailWord_3624345 prefixEnd_3624345 1861031042719727467219447 := by
  unfold tailWord_3624345
  simp only [CollatzResearch.WordTrace]
  refine ⟨132190722054624528690890489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88127148036416352460593659 132190722054624528690890489)
  ·
    refine ⟨99143041540968396518167867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132190722054624528690890489 99143041540968396518167867)
    ·
      refine ⟨148714562311452594777251801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99143041540968396518167867 148714562311452594777251801)
      ·
        refine ⟨111535921733589446082938851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 148714562311452594777251801 111535921733589446082938851)
        ·
          refine ⟨167303882600384169124408277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111535921733589446082938851 167303882600384169124408277)
          ·
            refine ⟨3921184748446503963853319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 167303882600384169124408277 3921184748446503963853319)
            ·
              refine ⟨5881777122669755945779979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3921184748446503963853319 5881777122669755945779979)
              ·
                refine ⟨8822665684004633918669969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5881777122669755945779979 8822665684004633918669969)
                ·
                  refine ⟨6616999263003475439002477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8822665684004633918669969 6616999263003475439002477)
                  ·
                    refine ⟨2481374723626303289625929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6616999263003475439002477 2481374723626303289625929)
                    ·
                      refine ⟨1861031042719727467219447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2481374723626303289625929 1861031042719727467219447)
                      ·
                        rfl

theorem cell23_3624345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 7, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 7, 1, 1, 2, 3, 2].length) (baseStart_3624345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3624345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3624345 prefixEnd_3624345 := by exact prefixLift 3624345
  have htrace : WordTrace (prefixWord ++ tailWord_3624345) baseStart_3624345 baseEnd_3624345 := by
    simpa [prefixWord, tailWord_3624345, baseEnd_3624345] using wordTrace_append hprefix tailTrace_3624345
  have hstable : (prefixWord ++ tailWord_3624345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3624345).length < 2 ^ (prefixWord ++ tailWord_3624345).sum := by decide
  have hdescent : baseEnd_3624345 < baseStart_3624345 := by decide
  rcases family_descends (prefixWord ++ tailWord_3624345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3624351 : List Nat := [1, 1, 2, 5, 1, 2, 2, 2, 1, 6]
def baseStart_3624351 : Nat := 118140960795 + 3624351 * 2 ^ 59
def prefixEnd_3624351 : Nat := 4983230072969 + 3 ^ 40 * 3624351 * 2
def baseEnd_3624351 : Nat := 620344707867884814581473

theorem tailTrace_3624351 : CollatzResearch.WordTrace tailWord_3624351 prefixEnd_3624351 620344707867884814581473 := by
  unfold tailWord_3624351
  simp only [CollatzResearch.WordTrace]
  refine ⟨132190940892602791715608907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88127293928401861143739271 132190940892602791715608907)
  ·
    refine ⟨198286411338904187573413361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132190940892602791715608907 198286411338904187573413361)
    ·
      refine ⟨148714808504178140680060021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 198286411338904187573413361 148714808504178140680060021)
      ·
        refine ⟨13942013297266700688755627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 148714808504178140680060021 13942013297266700688755627)
        ·
          refine ⟨20913019945900051033133441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13942013297266700688755627 20913019945900051033133441)
          ·
            refine ⟨15684764959425038274850081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20913019945900051033133441 15684764959425038274850081)
            ·
              refine ⟨11763573719568778706137561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15684764959425038274850081 11763573719568778706137561)
              ·
                refine ⟨8822680289676584029603171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11763573719568778706137561 8822680289676584029603171)
                ·
                  refine ⟨13234020434514876044404757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8822680289676584029603171 13234020434514876044404757)
                  ·
                    refine ⟨620344707867884814581473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13234020434514876044404757 620344707867884814581473)
                    ·
                      rfl

theorem cell23_3624351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 2, 2, 1, 6].length) (baseStart_3624351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3624351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3624351 prefixEnd_3624351 := by exact prefixLift 3624351
  have htrace : WordTrace (prefixWord ++ tailWord_3624351) baseStart_3624351 baseEnd_3624351 := by
    simpa [prefixWord, tailWord_3624351, baseEnd_3624351] using wordTrace_append hprefix tailTrace_3624351
  have hstable : (prefixWord ++ tailWord_3624351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3624351).length < 2 ^ (prefixWord ++ tailWord_3624351).sum := by decide
  have hdescent : baseEnd_3624351 < baseStart_3624351 := by decide
  rcases family_descends (prefixWord ++ tailWord_3624351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3624375 : List Nat := [1, 1, 3, 1, 3, 2, 4, 1, 3, 2, 2]
def baseStart_3624375 : Nat := 118140960795 + 3624375 * 2 ^ 59
def prefixEnd_3624375 : Nat := 4983230072969 + 3 ^ 40 * 3624375 * 2
def baseEnd_3624375 : Nat := 1861046447139362349844309

theorem tailTrace_3624375 : CollatzResearch.WordTrace tailWord_3624375 prefixEnd_3624375 1861046447139362349844309 := by
  unfold tailWord_3624375
  simp only [CollatzResearch.WordTrace]
  refine ⟨132191816244515843814482579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88127877496343895876321719 132191816244515843814482579)
  ·
    refine ⟨198287724366773765721723869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132191816244515843814482579 198287724366773765721723869)
    ·
      refine ⟨74357896637540162145646451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 198287724366773765721723869 74357896637540162145646451)
      ·
        refine ⟨111536844956310243218469677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74357896637540162145646451 111536844956310243218469677)
        ·
          refine ⟨41826316858616341206926129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 111536844956310243218469677 41826316858616341206926129)
          ·
            refine ⟨31369737643962255905194597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41826316858616341206926129 31369737643962255905194597)
            ·
              refine ⟨5881825808242922982223987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31369737643962255905194597 5881825808242922982223987)
              ·
                refine ⟨8822738712364384473335981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5881825808242922982223987 8822738712364384473335981)
                ·
                  refine ⟨3308527017136644177500993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8822738712364384473335981 3308527017136644177500993)
                  ·
                    refine ⟨2481395262852483133125745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3308527017136644177500993 2481395262852483133125745)
                    ·
                      refine ⟨1861046447139362349844309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2481395262852483133125745 1861046447139362349844309)
                      ·
                        rfl

theorem cell23_3624375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 4, 1, 3, 2, 2].length) (baseStart_3624375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3624375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3624375 prefixEnd_3624375 := by exact prefixLift 3624375
  have htrace : WordTrace (prefixWord ++ tailWord_3624375) baseStart_3624375 baseEnd_3624375 := by
    simpa [prefixWord, tailWord_3624375, baseEnd_3624375] using wordTrace_append hprefix tailTrace_3624375
  have hstable : (prefixWord ++ tailWord_3624375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3624375).length < 2 ^ (prefixWord ++ tailWord_3624375).sum := by decide
  have hdescent : baseEnd_3624375 < baseStart_3624375 := by decide
  rcases family_descends (prefixWord ++ tailWord_3624375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3624388 : List Nat := [2, 3, 3, 2, 1, 2, 1, 1, 1, 1, 6]
def baseStart_3624388 : Nat := 118140960795 + 3624388 * 2 ^ 59
def prefixEnd_3624388 : Nat := 4983230072969 + 3 ^ 40 * 3624388 * 2
def baseEnd_3624388 : Nat := 1861053122387870798981749

theorem tailTrace_3624388 : CollatzResearch.WordTrace tailWord_3624388 prefixEnd_3624388 1861053122387870798981749 := by
  unfold tailWord_3624388
  simp only [CollatzResearch.WordTrace]
  refine ⟨66096145196734373517352909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88128193595645831356470545 66096145196734373517352909)
  ·
    refine ⟨24786054448775390069007341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66096145196734373517352909 24786054448775390069007341)
    ·
      refine ⟨9294770418290771275877753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24786054448775390069007341 9294770418290771275877753)
      ·
        refine ⟨6971077813718078456908315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9294770418290771275877753 6971077813718078456908315)
        ·
          refine ⟨10456616720577117685362473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6971077813718078456908315 10456616720577117685362473)
          ·
            refine ⟨7842462540432838264021855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10456616720577117685362473 7842462540432838264021855)
            ·
              refine ⟨11763693810649257396032783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7842462540432838264021855 11763693810649257396032783)
              ·
                refine ⟨17645540715973886094049175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11763693810649257396032783 17645540715973886094049175)
                ·
                  refine ⟨26468311073960829141073763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17645540715973886094049175 26468311073960829141073763)
                  ·
                    refine ⟨39702466610941243711610645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26468311073960829141073763 39702466610941243711610645)
                    ·
                      refine ⟨1861053122387870798981749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 39702466610941243711610645 1861053122387870798981749)
                      ·
                        rfl

theorem cell23_3624388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 1, 1, 1, 1, 6].length) (baseStart_3624388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3624388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3624388 prefixEnd_3624388 := by exact prefixLift 3624388
  have htrace : WordTrace (prefixWord ++ tailWord_3624388) baseStart_3624388 baseEnd_3624388 := by
    simpa [prefixWord, tailWord_3624388, baseEnd_3624388] using wordTrace_append hprefix tailTrace_3624388
  have hstable : (prefixWord ++ tailWord_3624388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3624388).length < 2 ^ (prefixWord ++ tailWord_3624388).sum := by decide
  have hdescent : baseEnd_3624388 < baseStart_3624388 := by decide
  rcases family_descends (prefixWord ++ tailWord_3624388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3624408 : List Nat := [2, 1, 2, 2, 2, 1, 3, 2, 4, 1, 3]
def baseStart_3624408 : Nat := 118140960795 + 3624408 * 2 ^ 59
def prefixEnd_3624408 : Nat := 4983230072969 + 3 ^ 40 * 3624408 * 2
def baseEnd_3624408 : Nat := 1861063392000960720731657

theorem tailTrace_3624408 : CollatzResearch.WordTrace tailWord_3624408 prefixEnd_3624408 1861063392000960720731657 := by
  unfold tailWord_3624408
  simp only [CollatzResearch.WordTrace]
  refine ⟨66096509926698145225216939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88128679902264193633622585 66096509926698145225216939)
  ·
    refine ⟨99144764890047217837825409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66096509926698145225216939 99144764890047217837825409)
    ·
      refine ⟨74358573667535413378369057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99144764890047217837825409 74358573667535413378369057)
      ·
        refine ⟨55768930250651560033776793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74358573667535413378369057 55768930250651560033776793)
        ·
          refine ⟨41826697687988670025332595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55768930250651560033776793 41826697687988670025332595)
          ·
            refine ⟨62740046531983005037998893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41826697687988670025332595 62740046531983005037998893)
            ·
              refine ⟨23527517449493626889249585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62740046531983005037998893 23527517449493626889249585)
              ·
                refine ⟨17645638087120220166937189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23527517449493626889249585 17645638087120220166937189)
                ·
                  refine ⟨3308557141335041281300723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17645638087120220166937189 3308557141335041281300723)
                  ·
                    refine ⟨4962835712002561921951085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3308557141335041281300723 4962835712002561921951085)
                    ·
                      refine ⟨1861063392000960720731657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4962835712002561921951085 1861063392000960720731657)
                      ·
                        rfl

theorem cell23_3624408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 3, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 3, 2, 4, 1, 3].length) (baseStart_3624408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3624408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3624408 prefixEnd_3624408 := by exact prefixLift 3624408
  have htrace : WordTrace (prefixWord ++ tailWord_3624408) baseStart_3624408 baseEnd_3624408 := by
    simpa [prefixWord, tailWord_3624408, baseEnd_3624408] using wordTrace_append hprefix tailTrace_3624408
  have hstable : (prefixWord ++ tailWord_3624408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3624408).length < 2 ^ (prefixWord ++ tailWord_3624408).sum := by decide
  have hdescent : baseEnd_3624408 < baseStart_3624408 := by decide
  rcases family_descends (prefixWord ++ tailWord_3624408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3624409 : List Nat := [1, 2, 1, 2, 4, 4, 1, 3, 1, 2, 2]
def baseStart_3624409 : Nat := 118140960795 + 3624409 * 2 ^ 59
def prefixEnd_3624409 : Nat := 4983230072969 + 3 ^ 40 * 3624409 * 2
def baseEnd_3624409 : Nat := 1861063905481615216819153

theorem tailTrace_3624409 : CollatzResearch.WordTrace tailWord_3624409 prefixEnd_3624409 1861063905481615216819153 := by
  unfold tailWord_3624409
  simp only [CollatzResearch.WordTrace]
  refine ⟨132193056326392667621220281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88128704217595111747480187 132193056326392667621220281)
  ·
    refine ⟨99144792244794500715915211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132193056326392667621220281 99144792244794500715915211)
    ·
      refine ⟨148717188367191751073872817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99144792244794500715915211 148717188367191751073872817)
      ·
        refine ⟨111537891275393813305404613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 148717188367191751073872817 111537891275393813305404613)
        ·
          refine ⟨20913354614136339994763365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 111537891275393813305404613 20913354614136339994763365)
          ·
            refine ⟨3921253990150563749018131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20913354614136339994763365 3921253990150563749018131)
            ·
              refine ⟨5881880985225845623527197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3921253990150563749018131 5881880985225845623527197)
              ·
                refine ⟨2205705369459692108822699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5881880985225845623527197 2205705369459692108822699)
                ·
                  refine ⟨3308558054189538163234049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2205705369459692108822699 3308558054189538163234049)
                  ·
                    refine ⟨2481418540642153622425537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3308558054189538163234049 2481418540642153622425537)
                    ·
                      refine ⟨1861063905481615216819153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2481418540642153622425537 1861063905481615216819153)
                      ·
                        rfl

theorem cell23_3624409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 4, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 4, 1, 3, 1, 2, 2].length) (baseStart_3624409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3624409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3624409 prefixEnd_3624409 := by exact prefixLift 3624409
  have htrace : WordTrace (prefixWord ++ tailWord_3624409) baseStart_3624409 baseEnd_3624409 := by
    simpa [prefixWord, tailWord_3624409, baseEnd_3624409] using wordTrace_append hprefix tailTrace_3624409
  have hstable : (prefixWord ++ tailWord_3624409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3624409).length < 2 ^ (prefixWord ++ tailWord_3624409).sum := by decide
  have hdescent : baseEnd_3624409 < baseStart_3624409 := by decide
  rcases family_descends (prefixWord ++ tailWord_3624409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3624426 : List Nat := [3, 1, 3, 1, 4, 1, 3, 2, 1, 2, 2]
def baseStart_3624426 : Nat := 118140960795 + 3624426 * 2 ^ 59
def prefixEnd_3624426 : Nat := 4983230072969 + 3 ^ 40 * 3624426 * 2
def baseEnd_3624426 : Nat := 1861072634652741650306575

theorem tailTrace_3624426 : CollatzResearch.WordTrace tailWord_3624426 prefixEnd_3624426 1861072634652741650306575 := by
  unfold tailWord_3624426
  simp only [CollatzResearch.WordTrace]
  refine ⟨33048419091832769881147283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88129117578220719683059421 33048419091832769881147283)
  ·
    refine ⟨49572628637749154821720925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33048419091832769881147283 49572628637749154821720925)
    ·
      refine ⟨18589735739155933058145347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49572628637749154821720925 18589735739155933058145347)
      ·
        refine ⟨27884603608733899587218021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18589735739155933058145347 27884603608733899587218021)
        ·
          refine ⟨5228363176637606172603379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27884603608733899587218021 5228363176637606172603379)
          ·
            refine ⟨7842544764956409258905069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5228363176637606172603379 7842544764956409258905069)
            ·
              refine ⟨2940954286858653472089401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7842544764956409258905069 2940954286858653472089401)
              ·
                refine ⟨2205715715143990104067051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2940954286858653472089401 2205715715143990104067051)
                ·
                  refine ⟨3308573572715985156100577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2205715715143990104067051 3308573572715985156100577)
                  ·
                    refine ⟨2481430179536988867075433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3308573572715985156100577 2481430179536988867075433)
                    ·
                      refine ⟨1861072634652741650306575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2481430179536988867075433 1861072634652741650306575)
                      ·
                        rfl

theorem cell23_3624426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 3, 2, 1, 2, 2].length) (baseStart_3624426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3624426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3624426 prefixEnd_3624426 := by exact prefixLift 3624426
  have htrace : WordTrace (prefixWord ++ tailWord_3624426) baseStart_3624426 baseEnd_3624426 := by
    simpa [prefixWord, tailWord_3624426, baseEnd_3624426] using wordTrace_append hprefix tailTrace_3624426
  have hstable : (prefixWord ++ tailWord_3624426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3624426).length < 2 ^ (prefixWord ++ tailWord_3624426).sum := by decide
  have hdescent : baseEnd_3624426 < baseStart_3624426 := by decide
  rcases family_descends (prefixWord ++ tailWord_3624426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3624446 : List Nat := [4, 2, 2, 3, 2, 1, 1, 2, 1, 2, 3]
def baseStart_3624446 : Nat := 118140960795 + 3624446 * 2 ^ 59
def prefixEnd_3624446 : Nat := 4983230072969 + 3 ^ 40 * 3624446 * 2
def baseEnd_3624446 : Nat := 1861082904265831572056483

theorem tailTrace_3624446 : CollatzResearch.WordTrace tailWord_3624446 prefixEnd_3624446 1861082904265831572056483 := by
  unfold tailWord_3624446
  simp only [CollatzResearch.WordTrace]
  refine ⟨16524300728407327867539649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 88129603884839081960211461 16524300728407327867539649)
  ·
    refine ⟨12393225546305495900654737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16524300728407327867539649 12393225546305495900654737)
    ·
      refine ⟨9294919159729121925491053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12393225546305495900654737 9294919159729121925491053)
      ·
        refine ⟨3485594684898420722059145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9294919159729121925491053 3485594684898420722059145)
        ·
          refine ⟨2614196013673815541544359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3485594684898420722059145 2614196013673815541544359)
          ·
            refine ⟨3921294020510723312316539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2614196013673815541544359 3921294020510723312316539)
            ·
              refine ⟨5881941030766084968474809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3921294020510723312316539 5881941030766084968474809)
              ·
                refine ⟨4411455773074563726356107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5881941030766084968474809 4411455773074563726356107)
                ·
                  refine ⟨6617183659611845589534161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4411455773074563726356107 6617183659611845589534161)
                  ·
                    refine ⟨4962887744708884192150621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6617183659611845589534161 4962887744708884192150621)
                    ·
                      refine ⟨1861082904265831572056483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4962887744708884192150621 1861082904265831572056483)
                      ·
                        rfl

theorem cell23_3624446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 2, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 2, 1, 1, 2, 1, 2, 3].length) (baseStart_3624446 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3624446 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3624446 prefixEnd_3624446 := by exact prefixLift 3624446
  have htrace : WordTrace (prefixWord ++ tailWord_3624446) baseStart_3624446 baseEnd_3624446 := by
    simpa [prefixWord, tailWord_3624446, baseEnd_3624446] using wordTrace_append hprefix tailTrace_3624446
  have hstable : (prefixWord ++ tailWord_3624446).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3624446).length < 2 ^ (prefixWord ++ tailWord_3624446).sum := by decide
  have hdescent : baseEnd_3624446 < baseStart_3624446 := by decide
  rcases family_descends (prefixWord ++ tailWord_3624446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3624451 : List Nat := [1, 1, 1, 3, 2, 1, 2, 1, 4, 4, 3]
def baseStart_3624451 : Nat := 118140960795 + 3624451 * 2 ^ 59
def prefixEnd_3624451 : Nat := 4983230072969 + 3 ^ 40 * 3624451 * 2
def baseEnd_3624451 : Nat := 1861085471669104052493959

theorem tailTrace_3624451 : CollatzResearch.WordTrace tailWord_3624451 prefixEnd_3624451 1861085471669104052493959 := by
  unfold tailWord_3624451
  simp only [CollatzResearch.WordTrace]
  refine ⟨132194588192240508794249207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88129725461493672529499471 132194588192240508794249207)
  ·
    refine ⟨198291882288360763191373811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132194588192240508794249207 198291882288360763191373811)
    ·
      refine ⟨297437823432541144787060717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198291882288360763191373811 297437823432541144787060717)
      ·
        refine ⟨111539183787202929295147769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 297437823432541144787060717 111539183787202929295147769)
        ·
          refine ⟨83654387840402196971360827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 111539183787202929295147769 83654387840402196971360827)
          ·
            refine ⟨125481581760603295457041241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83654387840402196971360827 125481581760603295457041241)
            ·
              refine ⟨94111186320452471592780931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 125481581760603295457041241 94111186320452471592780931)
              ·
                refine ⟨141166779480678707389171397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 94111186320452471592780931 141166779480678707389171397)
                ·
                  refine ⟨26468771152627257635469637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 141166779480678707389171397 26468771152627257635469637)
                  ·
                    refine ⟨4962894591117610806650557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26468771152627257635469637 4962894591117610806650557)
                    ·
                      refine ⟨1861085471669104052493959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4962894591117610806650557 1861085471669104052493959)
                      ·
                        rfl

theorem cell23_3624451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 1, 4, 4, 3].length) (baseStart_3624451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3624451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3624451 prefixEnd_3624451 := by exact prefixLift 3624451
  have htrace : WordTrace (prefixWord ++ tailWord_3624451) baseStart_3624451 baseEnd_3624451 := by
    simpa [prefixWord, tailWord_3624451, baseEnd_3624451] using wordTrace_append hprefix tailTrace_3624451
  have hstable : (prefixWord ++ tailWord_3624451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3624451).length < 2 ^ (prefixWord ++ tailWord_3624451).sum := by decide
  have hdescent : baseEnd_3624451 < baseStart_3624451 := by decide
  rcases family_descends (prefixWord ++ tailWord_3624451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3624452 : List Nat := [2, 3, 2, 3, 2, 1, 1, 1, 3, 3, 2]
def baseStart_3624452 : Nat := 118140960795 + 3624452 * 2 ^ 59
def prefixEnd_3624452 : Nat := 4983230072969 + 3 ^ 40 * 3624452 * 2
def baseEnd_3624452 : Nat := 1861085985149758548581455

theorem tailTrace_3624452 : CollatzResearch.WordTrace tailWord_3624452 prefixEnd_3624452 1861085985149758548581455 := by
  unfold tailWord_3624452
  simp only [CollatzResearch.WordTrace]
  refine ⟨66097312332618442982517805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88129749776824590643357073 66097312332618442982517805)
  ·
    refine ⟨24786492124731916118444177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66097312332618442982517805 24786492124731916118444177)
    ·
      refine ⟨18589869093548937088833133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24786492124731916118444177 18589869093548937088833133)
      ·
        refine ⟨6971200910080851408312425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18589869093548937088833133 6971200910080851408312425)
        ·
          refine ⟨5228400682560638556234319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6971200910080851408312425 5228400682560638556234319)
          ·
            refine ⟨7842601023840957834351479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5228400682560638556234319 7842601023840957834351479)
            ·
              refine ⟨11763901535761436751527219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7842601023840957834351479 11763901535761436751527219)
              ·
                refine ⟨17645852303642155127290829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11763901535761436751527219 17645852303642155127290829)
                ·
                  refine ⟨6617194613865808172734061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17645852303642155127290829 6617194613865808172734061)
                  ·
                    refine ⟨2481447980199678064775273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6617194613865808172734061 2481447980199678064775273)
                    ·
                      refine ⟨1861085985149758548581455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2481447980199678064775273 1861085985149758548581455)
                      ·
                        rfl

theorem cell23_3624452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 1, 1, 3, 3, 2].length) (baseStart_3624452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3624452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3624452 prefixEnd_3624452 := by exact prefixLift 3624452
  have htrace : WordTrace (prefixWord ++ tailWord_3624452) baseStart_3624452 baseEnd_3624452 := by
    simpa [prefixWord, tailWord_3624452, baseEnd_3624452] using wordTrace_append hprefix tailTrace_3624452
  have hstable : (prefixWord ++ tailWord_3624452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3624452).length < 2 ^ (prefixWord ++ tailWord_3624452).sum := by decide
  have hdescent : baseEnd_3624452 < baseStart_3624452 := by decide
  rcases family_descends (prefixWord ++ tailWord_3624452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3624482 : List Nat := [3, 3, 1, 1, 1, 1, 3, 4, 2, 2, 2]
def baseStart_3624482 : Nat := 118140960795 + 3624482 * 2 ^ 59
def prefixEnd_3624482 : Nat := 4983230072969 + 3 ^ 40 * 3624482 * 2
def baseEnd_3624482 : Nat := 1861101389569393431206317

theorem tailTrace_3624482 : CollatzResearch.WordTrace tailWord_3624482 prefixEnd_3624482 1861101389569393431206317 := by
  unfold tailWord_3624482
  simp only [CollatzResearch.WordTrace]
  refine ⟨33048929713782050272156925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88130479236752134059085133 33048929713782050272156925)
  ·
    refine ⟨12393348642668268852058847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33048929713782050272156925 12393348642668268852058847)
    ·
      refine ⟨18590022964002403278088271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12393348642668268852058847 18590022964002403278088271)
      ·
        refine ⟨27885034446003604917132407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18590022964002403278088271 27885034446003604917132407)
        ·
          refine ⟨41827551669005407375698611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27885034446003604917132407 41827551669005407375698611)
          ·
            refine ⟨62741327503508111063547917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41827551669005407375698611 62741327503508111063547917)
            ·
              refine ⟨23527997813815541648830469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62741327503508111063547917 23527997813815541648830469)
              ·
                refine ⟨4411499590090414059155713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23527997813815541648830469 4411499590090414059155713)
                ·
                  refine ⟨3308624692567810544366785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4411499590090414059155713 3308624692567810544366785)
                  ·
                    refine ⟨2481468519425857908275089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3308624692567810544366785 2481468519425857908275089)
                    ·
                      refine ⟨1861101389569393431206317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2481468519425857908275089 1861101389569393431206317)
                      ·
                        rfl

theorem cell23_3624482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 3, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 3, 4, 2, 2, 2].length) (baseStart_3624482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3624482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3624482 prefixEnd_3624482 := by exact prefixLift 3624482
  have htrace : WordTrace (prefixWord ++ tailWord_3624482) baseStart_3624482 baseEnd_3624482 := by
    simpa [prefixWord, tailWord_3624482, baseEnd_3624482] using wordTrace_append hprefix tailTrace_3624482
  have hstable : (prefixWord ++ tailWord_3624482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3624482).length < 2 ^ (prefixWord ++ tailWord_3624482).sum := by decide
  have hdescent : baseEnd_3624482 < baseStart_3624482 := by decide
  rcases family_descends (prefixWord ++ tailWord_3624482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3624538 : List Nat := [3, 1, 1, 2, 1, 1, 1, 6, 2, 1, 4]
def baseStart_3624538 : Nat := 118140960795 + 3624538 * 2 ^ 59
def prefixEnd_3624538 : Nat := 4983230072969 + 3 ^ 40 * 3624538 * 2
def baseEnd_3624538 : Nat := 1861130144486045212106059

theorem tailTrace_3624538 : CollatzResearch.WordTrace tailWord_3624538 prefixEnd_3624538 1861130144486045212106059 := by
  unfold tailWord_3624538
  simp only [CollatzResearch.WordTrace]
  refine ⟨33049440335731330663166567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88131840895283548435110845 33049440335731330663166567)
  ·
    refine ⟨49574160503596995994749851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33049440335731330663166567 49574160503596995994749851)
    ·
      refine ⟨74361240755395493992124777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49574160503596995994749851 74361240755395493992124777)
      ·
        refine ⟨55770930566546620494093583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74361240755395493992124777 55770930566546620494093583)
        ·
          refine ⟨83656395849819930741140375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55770930566546620494093583 83656395849819930741140375)
          ·
            refine ⟨125484593774729896111710563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83656395849819930741140375 125484593774729896111710563)
            ·
              refine ⟨188226890662094844167565845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 125484593774729896111710563 188226890662094844167565845)
              ·
                refine ⟨8823135499785695820354649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 188226890662094844167565845 8823135499785695820354649)
                ·
                  refine ⟨6617351624839271865265987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8823135499785695820354649 6617351624839271865265987)
                  ·
                    refine ⟨9926027437258907797898981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6617351624839271865265987 9926027437258907797898981)
                    ·
                      refine ⟨1861130144486045212106059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9926027437258907797898981 1861130144486045212106059)
                      ·
                        rfl

theorem cell23_3624538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 6, 2, 1, 4].length) (baseStart_3624538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3624538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3624538 prefixEnd_3624538 := by exact prefixLift 3624538
  have htrace : WordTrace (prefixWord ++ tailWord_3624538) baseStart_3624538 baseEnd_3624538 := by
    simpa [prefixWord, tailWord_3624538, baseEnd_3624538] using wordTrace_append hprefix tailTrace_3624538
  have hstable : (prefixWord ++ tailWord_3624538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3624538).length < 2 ^ (prefixWord ++ tailWord_3624538).sum := by decide
  have hdescent : baseEnd_3624538 < baseStart_3624538 := by decide
  rcases family_descends (prefixWord ++ tailWord_3624538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3624599 : List Nat := [1, 1, 3, 3, 2, 3, 3, 2, 1, 4]
def baseStart_3624599 : Nat := 118140960795 + 3624599 * 2 ^ 59
def prefixEnd_3624599 : Nat := 4983230072969 + 3 ^ 40 * 3624599 * 2
def baseEnd_3624599 : Nat := 620387155601989824481093

theorem tailTrace_3624599 : CollatzResearch.WordTrace tailWord_3624599 prefixEnd_3624599 620387155601989824481093 := by
  unfold tailWord_3624599
  simp only [CollatzResearch.WordTrace]
  refine ⟨132199986195704330070636851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88133324130469553380424567 132199986195704330070636851)
  ·
    refine ⟨198299979293556495105955277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132199986195704330070636851 198299979293556495105955277)
    ·
      refine ⟨74362492235083685664733229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 198299979293556495105955277 74362492235083685664733229)
      ·
        refine ⟨27885934588156382124274961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74362492235083685664733229 27885934588156382124274961)
        ·
          refine ⟨20914450941117286593206221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27885934588156382124274961 20914450941117286593206221)
          ·
            refine ⟨7842919102918982472452333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20914450941117286593206221 7842919102918982472452333)
            ·
              refine ⟨2941094663594618427169625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7842919102918982472452333 2941094663594618427169625)
              ·
                refine ⟨2205820997695963820377219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2941094663594618427169625 2205820997695963820377219)
                ·
                  refine ⟨3308731496543945730565829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2205820997695963820377219 3308731496543945730565829)
                  ·
                    refine ⟨620387155601989824481093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3308731496543945730565829 620387155601989824481093)
                    ·
                      rfl

theorem cell23_3624599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 3, 2, 1, 4].length) (baseStart_3624599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3624599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3624599 prefixEnd_3624599 := by exact prefixLift 3624599
  have htrace : WordTrace (prefixWord ++ tailWord_3624599) baseStart_3624599 baseEnd_3624599 := by
    simpa [prefixWord, tailWord_3624599, baseEnd_3624599] using wordTrace_append hprefix tailTrace_3624599
  have hstable : (prefixWord ++ tailWord_3624599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3624599).length < 2 ^ (prefixWord ++ tailWord_3624599).sum := by decide
  have hdescent : baseEnd_3624599 < baseStart_3624599 := by decide
  rcases family_descends (prefixWord ++ tailWord_3624599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3624612 : List Nat := [2, 3, 1, 2, 2, 4, 2, 1, 6]
def baseStart_3624612 : Nat := 118140960795 + 3624612 * 2 ^ 59
def prefixEnd_3624612 : Nat := 4983230072969 + 3 ^ 40 * 3624612 * 2
def baseEnd_3624612 : Nat := 206796460228275324731191

theorem tailTrace_3624612 : CollatzResearch.WordTrace tailWord_3624612 prefixEnd_3624612 206796460228275324731191 := by
  unfold tailWord_3624612
  simp only [CollatzResearch.WordTrace]
  refine ⟨66100230172328616645430045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88133640229771488860573393 66100230172328616645430045)
  ·
    refine ⟨24787586314623231242036267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66100230172328616645430045 24787586314623231242036267)
    ·
      refine ⟨37181379471934846863054401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24787586314623231242036267 37181379471934846863054401)
      ·
        refine ⟨27886034603951135147290801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37181379471934846863054401 27886034603951135147290801)
        ·
          refine ⟨20914525952963351360468101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27886034603951135147290801 20914525952963351360468101)
          ·
            refine ⟨3921473616180628380087769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20914525952963351360468101 3921473616180628380087769)
            ·
              refine ⟨2941105212135471285065827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3921473616180628380087769 2941105212135471285065827)
              ·
                refine ⟨4411657818203206927598741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2941105212135471285065827 4411657818203206927598741)
                ·
                  refine ⟨206796460228275324731191, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4411657818203206927598741 206796460228275324731191)
                  ·
                    rfl

theorem cell23_3624612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 4, 2, 1, 6].length) (baseStart_3624612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3624612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3624612 prefixEnd_3624612 := by exact prefixLift 3624612
  have htrace : WordTrace (prefixWord ++ tailWord_3624612) baseStart_3624612 baseEnd_3624612 := by
    simpa [prefixWord, tailWord_3624612, baseEnd_3624612] using wordTrace_append hprefix tailTrace_3624612
  have hstable : (prefixWord ++ tailWord_3624612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3624612).length < 2 ^ (prefixWord ++ tailWord_3624612).sum := by decide
  have hdescent : baseEnd_3624612 < baseStart_3624612 := by decide
  rcases family_descends (prefixWord ++ tailWord_3624612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3624665 : List Nat := [1, 2, 1, 2, 3, 3, 1, 2, 3, 2, 3]
def baseStart_3624665 : Nat := 118140960795 + 3624665 * 2 ^ 59
def prefixEnd_3624665 : Nat := 4983230072969 + 3 ^ 40 * 3624665 * 2
def baseEnd_3624665 : Nat := 1861195356529166215217975

theorem tailTrace_3624665 : CollatzResearch.WordTrace tailWord_3624665 prefixEnd_3624665 1861195356529166215217975 := by
  unfold tailWord_3624665
  simp only [CollatzResearch.WordTrace]
  refine ⟨132202393413465223342539449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88134928942310148895026299 132202393413465223342539449)
  ·
    refine ⟨99151795060098917506904587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132202393413465223342539449 99151795060098917506904587)
    ·
      refine ⟨148727692590148376260356881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99151795060098917506904587 148727692590148376260356881)
      ·
        refine ⟨111545769442611282195267661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 148727692590148376260356881 111545769442611282195267661)
        ·
          refine ⟨41829663540979230823225373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 111545769442611282195267661 41829663540979230823225373)
          ·
            refine ⟨15686123827867211558709515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41829663540979230823225373 15686123827867211558709515)
            ·
              refine ⟨23529185741800817338064273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15686123827867211558709515 23529185741800817338064273)
              ·
                refine ⟨17646889306350613003548205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23529185741800817338064273 17646889306350613003548205)
                ·
                  refine ⟨6617583489881479876330577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17646889306350613003548205 6617583489881479876330577)
                  ·
                    refine ⟨4963187617411109907247933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6617583489881479876330577 4963187617411109907247933)
                    ·
                      refine ⟨1861195356529166215217975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4963187617411109907247933 1861195356529166215217975)
                      ·
                        rfl

theorem cell23_3624665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 1, 2, 3, 2, 3].length) (baseStart_3624665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3624665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3624665 prefixEnd_3624665 := by exact prefixLift 3624665
  have htrace : WordTrace (prefixWord ++ tailWord_3624665) baseStart_3624665 baseEnd_3624665 := by
    simpa [prefixWord, tailWord_3624665, baseEnd_3624665] using wordTrace_append hprefix tailTrace_3624665
  have hstable : (prefixWord ++ tailWord_3624665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3624665).length < 2 ^ (prefixWord ++ tailWord_3624665).sum := by decide
  have hdescent : baseEnd_3624665 < baseStart_3624665 := by decide
  rcases family_descends (prefixWord ++ tailWord_3624665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3624695 : List Nat := [1, 1, 3, 1, 1, 1, 6, 2, 1, 3, 3]
def baseStart_3624695 : Nat := 118140960795 + 3624695 * 2 ^ 59
def prefixEnd_3624695 : Nat := 4983230072969 + 3 ^ 40 * 3624695 * 2
def baseEnd_3624695 : Nat := 1861210760948801097842837

theorem tailTrace_3624695 : CollatzResearch.WordTrace tailWord_3624695 prefixEnd_3624695 1861210760948801097842837 := by
  unfold tailWord_3624695
  simp only [CollatzResearch.WordTrace]
  refine ⟨132203487603356538466131539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88135658402237692310754359 132203487603356538466131539)
  ·
    refine ⟨198305231405034807699197309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132203487603356538466131539 198305231405034807699197309)
    ·
      refine ⟨74364461776888052887198991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 198305231405034807699197309 74364461776888052887198991)
      ·
        refine ⟨111546692665332079330798487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74364461776888052887198991 111546692665332079330798487)
        ·
          refine ⟨167320038997998118996197731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111546692665332079330798487 167320038997998118996197731)
          ·
            refine ⟨250980058496997178494296597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 167320038997998118996197731 250980058496997178494296597)
            ·
              refine ⟨11764690242046742741920153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 250980058496997178494296597 11764690242046742741920153)
              ·
                refine ⟨8823517681535057056440115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11764690242046742741920153 8823517681535057056440115)
                ·
                  refine ⟨13235276522302585584660173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8823517681535057056440115 13235276522302585584660173)
                  ·
                    refine ⟨4963228695863469594247565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13235276522302585584660173 4963228695863469594247565)
                    ·
                      refine ⟨1861210760948801097842837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4963228695863469594247565 1861210760948801097842837)
                      ·
                        rfl

theorem cell23_3624695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 6, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 6, 2, 1, 3, 3].length) (baseStart_3624695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3624695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3624695 prefixEnd_3624695 := by exact prefixLift 3624695
  have htrace : WordTrace (prefixWord ++ tailWord_3624695) baseStart_3624695 baseEnd_3624695 := by
    simpa [prefixWord, tailWord_3624695, baseEnd_3624695] using wordTrace_append hprefix tailTrace_3624695
  have hstable : (prefixWord ++ tailWord_3624695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3624695).length < 2 ^ (prefixWord ++ tailWord_3624695).sum := by decide
  have hdescent : baseEnd_3624695 < baseStart_3624695 := by decide
  rcases family_descends (prefixWord ++ tailWord_3624695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3624712 : List Nat := [2, 1, 3, 2, 2, 1, 3, 1, 4, 1, 3]
def baseStart_3624712 : Nat := 118140960795 + 3624712 * 2 ^ 59
def prefixEnd_3624712 : Nat := 4983230072969 + 3 ^ 40 * 3624712 * 2
def baseEnd_3624712 : Nat := 1861219490119927531330259

theorem tailTrace_3624712 : CollatzResearch.WordTrace tailWord_3624712 prefixEnd_3624712 1861219490119927531330259 := by
  unfold tailWord_3624712
  simp only [CollatzResearch.WordTrace]
  refine ⟨66102053822147475184750195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88136071762863300246333593 66102053822147475184750195)
  ·
    refine ⟨99153080733221212777125293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66102053822147475184750195 99153080733221212777125293)
    ·
      refine ⟨37182405274957954791421985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 99153080733221212777125293 37182405274957954791421985)
      ·
        refine ⟨27886803956218466093566489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37182405274957954791421985 27886803956218466093566489)
        ·
          refine ⟨20915102967163849570174867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27886803956218466093566489 20915102967163849570174867)
          ·
            refine ⟨31372654450745774355262301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20915102967163849570174867 31372654450745774355262301)
            ·
              refine ⟨11764745419029665383223363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31372654450745774355262301 11764745419029665383223363)
              ·
                refine ⟨17647118128544498074835045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11764745419029665383223363 17647118128544498074835045)
                ·
                  refine ⟨3308834649102093389031571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17647118128544498074835045 3308834649102093389031571)
                  ·
                    refine ⟨4963251973653140083547357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3308834649102093389031571 4963251973653140083547357)
                    ·
                      refine ⟨1861219490119927531330259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4963251973653140083547357 1861219490119927531330259)
                      ·
                        rfl

theorem cell23_3624712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 3, 1, 4, 1, 3].length) (baseStart_3624712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3624712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3624712 prefixEnd_3624712 := by exact prefixLift 3624712
  have htrace : WordTrace (prefixWord ++ tailWord_3624712) baseStart_3624712 baseEnd_3624712 := by
    simpa [prefixWord, tailWord_3624712, baseEnd_3624712] using wordTrace_append hprefix tailTrace_3624712
  have hstable : (prefixWord ++ tailWord_3624712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3624712).length < 2 ^ (prefixWord ++ tailWord_3624712).sum := by decide
  have hdescent : baseEnd_3624712 < baseStart_3624712 := by decide
  rcases family_descends (prefixWord ++ tailWord_3624712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3624756 : List Nat := [2, 5, 1, 1, 2, 1, 2, 3, 1, 3, 2]
def baseStart_3624756 : Nat := 118140960795 + 3624756 * 2 ^ 59
def prefixEnd_3624756 : Nat := 4983230072969 + 3 ^ 40 * 3624756 * 2
def baseEnd_3624756 : Nat := 1861242083268725359180057

theorem tailTrace_3624756 : CollatzResearch.WordTrace tailWord_3624756 prefixEnd_3624756 1861242083268725359180057 := by
  unfold tailWord_3624756
  simp only [CollatzResearch.WordTrace]
  refine ⟨66102856228067772942051061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88137141637423697256068081 66102856228067772942051061)
  ·
    refine ⟨6197142771381353713317287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 66102856228067772942051061 6197142771381353713317287)
    ·
      refine ⟨9295714157072030569975931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6197142771381353713317287 9295714157072030569975931)
      ·
        refine ⟨13943571235608045854963897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9295714157072030569975931 13943571235608045854963897)
        ·
          refine ⟨10457678426706034391222923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13943571235608045854963897 10457678426706034391222923)
          ·
            refine ⟨15686517640059051586834385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10457678426706034391222923 15686517640059051586834385)
            ·
              refine ⟨11764888230044288690125789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15686517640059051586834385 11764888230044288690125789)
              ·
                refine ⟨4411833086266608258797171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11764888230044288690125789 4411833086266608258797171)
                ·
                  refine ⟨6617749629399912388195757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4411833086266608258797171 6617749629399912388195757)
                  ·
                    refine ⟨2481656111024967145573409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6617749629399912388195757 2481656111024967145573409)
                    ·
                      refine ⟨1861242083268725359180057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2481656111024967145573409 1861242083268725359180057)
                      ·
                        rfl

theorem cell23_3624756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 2, 3, 1, 3, 2].length) (baseStart_3624756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3624756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3624756 prefixEnd_3624756 := by exact prefixLift 3624756
  have htrace : WordTrace (prefixWord ++ tailWord_3624756) baseStart_3624756 baseEnd_3624756 := by
    simpa [prefixWord, tailWord_3624756, baseEnd_3624756] using wordTrace_append hprefix tailTrace_3624756
  have hstable : (prefixWord ++ tailWord_3624756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3624756).length < 2 ^ (prefixWord ++ tailWord_3624756).sum := by decide
  have hdescent : baseEnd_3624756 < baseStart_3624756 := by decide
  rcases family_descends (prefixWord ++ tailWord_3624756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3624775 : List Nat := [1, 1, 4, 1, 2, 1, 5, 1, 7]
def baseStart_3624775 : Nat := 118140960795 + 3624775 * 2 ^ 59
def prefixEnd_3624775 : Nat := 4983230072969 + 3 ^ 40 * 3624775 * 2
def baseEnd_3624775 : Nat := 206805759933462309426941

theorem tailTrace_3624775 : CollatzResearch.WordTrace tailWord_3624775 prefixEnd_3624775 206805759933462309426941 := by
  unfold tailWord_3624775
  simp only [CollatzResearch.WordTrace]
  refine ⟨132206405443066712129043779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88137603628711141419362519 132206405443066712129043779)
  ·
    refine ⟨198309608164600068193565669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132206405443066712129043779 198309608164600068193565669)
    ·
      refine ⟨37183051530862512786293563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 198309608164600068193565669 37183051530862512786293563)
      ·
        refine ⟨55774577296293769179440345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37183051530862512786293563 55774577296293769179440345)
        ·
          refine ⟨41830932972220326884580259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55774577296293769179440345 41830932972220326884580259)
          ·
            refine ⟨62746399458330490326870389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41830932972220326884580259 62746399458330490326870389)
            ·
              refine ⟨5882474949218483468144099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 62746399458330490326870389 5882474949218483468144099)
              ·
                refine ⟨8823712423827725202216149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5882474949218483468144099 8823712423827725202216149)
                ·
                  refine ⟨206805759933462309426941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8823712423827725202216149 206805759933462309426941)
                  ·
                    rfl

theorem cell23_3624775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 5, 1, 7].length) (baseStart_3624775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3624775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3624775 prefixEnd_3624775 := by exact prefixLift 3624775
  have htrace : WordTrace (prefixWord ++ tailWord_3624775) baseStart_3624775 baseEnd_3624775 := by
    simpa [prefixWord, tailWord_3624775, baseEnd_3624775] using wordTrace_append hprefix tailTrace_3624775
  have hstable : (prefixWord ++ tailWord_3624775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3624775).length < 2 ^ (prefixWord ++ tailWord_3624775).sum := by decide
  have hdescent : baseEnd_3624775 < baseStart_3624775 := by decide
  rcases family_descends (prefixWord ++ tailWord_3624775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3624786 : List Nat := [3, 2, 2, 1, 1, 4, 1, 3, 2, 2, 2]
def baseStart_3624786 : Nat := 118140960795 + 3624786 * 2 ^ 59
def prefixEnd_3624786 : Nat := 4983230072969 + 3 ^ 40 * 3624786 * 2
def baseEnd_3624786 : Nat := 1861257487688360241804919

theorem tailTrace_3624786 : CollatzResearch.WordTrace tailWord_3624786 prefixEnd_3624786 1861257487688360241804919 := by
  unfold tailWord_3624786
  simp only [CollatzResearch.WordTrace]
  refine ⟨33051701661506715251923553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88137871097351240671796141 33051701661506715251923553)
  ·
    refine ⟨24788776246130036438942665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33051701661506715251923553 24788776246130036438942665)
    ·
      refine ⟨18591582184597527329206999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24788776246130036438942665 18591582184597527329206999)
      ·
        refine ⟨27887373276896290993810499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18591582184597527329206999 27887373276896290993810499)
        ·
          refine ⟨41831059915344436490715749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27887373276896290993810499 41831059915344436490715749)
          ·
            refine ⟨7843323734127081842009203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41831059915344436490715749 7843323734127081842009203)
            ·
              refine ⟨11764985601190622763013805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7843323734127081842009203 11764985601190622763013805)
              ·
                refine ⟨4411869600446483536130177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11764985601190622763013805 4411869600446483536130177)
                ·
                  refine ⟨3308902200334862652097633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4411869600446483536130177 3308902200334862652097633)
                  ·
                    refine ⟨2481676650251146989073225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3308902200334862652097633 2481676650251146989073225)
                    ·
                      refine ⟨1861257487688360241804919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2481676650251146989073225 1861257487688360241804919)
                      ·
                        rfl

theorem cell23_3624786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 1, 3, 2, 2, 2].length) (baseStart_3624786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3624786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3624786 prefixEnd_3624786 := by exact prefixLift 3624786
  have htrace : WordTrace (prefixWord ++ tailWord_3624786) baseStart_3624786 baseEnd_3624786 := by
    simpa [prefixWord, tailWord_3624786, baseEnd_3624786] using wordTrace_append hprefix tailTrace_3624786
  have hstable : (prefixWord ++ tailWord_3624786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3624786).length < 2 ^ (prefixWord ++ tailWord_3624786).sum := by decide
  have hdescent : baseEnd_3624786 < baseStart_3624786 := by decide
  rcases family_descends (prefixWord ++ tailWord_3624786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3624856 : List Nat := [2, 1, 2, 6, 1, 2, 1, 1, 2, 5]
def baseStart_3624856 : Nat := 118140960795 + 3624856 * 2 ^ 59
def prefixEnd_3624856 : Nat := 4983230072969 + 3 ^ 40 * 3624856 * 2
def baseEnd_3624856 : Nat := 620431143778058322643199

theorem tailTrace_3624856 : CollatzResearch.WordTrace tailWord_3624856 prefixEnd_3624856 620431143778058322643199 := by
  unfold tailWord_3624856
  simp only [CollatzResearch.WordTrace]
  refine ⟨66104679877886631481371211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88139573170515508641828281 66104679877886631481371211)
  ·
    refine ⟨99157019816829947222056817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66104679877886631481371211 99157019816829947222056817)
    ·
      refine ⟨74367764862622460416542613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99157019816829947222056817 74367764862622460416542613)
      ·
        refine ⟨3485988977935427832025435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 74367764862622460416542613 3485988977935427832025435)
        ·
          refine ⟨5228983466903141748038153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3485988977935427832025435 5228983466903141748038153)
          ·
            refine ⟨3921737600177356311028615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5228983466903141748038153 3921737600177356311028615)
            ·
              refine ⟨5882606400266034466542923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3921737600177356311028615 5882606400266034466542923)
              ·
                refine ⟨8823909600399051699814385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5882606400266034466542923 8823909600399051699814385)
                ·
                  refine ⟨6617932200299288774860789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8823909600399051699814385 6617932200299288774860789)
                  ·
                    refine ⟨620431143778058322643199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6617932200299288774860789 620431143778058322643199)
                    ·
                      rfl

theorem cell23_3624856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 2, 1, 1, 2, 5].length) (baseStart_3624856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3624856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3624856 prefixEnd_3624856 := by exact prefixLift 3624856
  have htrace : WordTrace (prefixWord ++ tailWord_3624856) baseStart_3624856 baseEnd_3624856 := by
    simpa [prefixWord, tailWord_3624856, baseEnd_3624856] using wordTrace_append hprefix tailTrace_3624856
  have hstable : (prefixWord ++ tailWord_3624856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3624856).length < 2 ^ (prefixWord ++ tailWord_3624856).sum := by decide
  have hdescent : baseEnd_3624856 < baseStart_3624856 := by decide
  rcases family_descends (prefixWord ++ tailWord_3624856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3624912 : List Nat := [2, 1, 1, 1, 1, 2, 5, 4, 1, 5]
def baseStart_3624912 : Nat := 118140960795 + 3624912 * 2 ^ 59
def prefixEnd_3624912 : Nat := 4983230072969 + 3 ^ 40 * 3624912 * 2
def baseEnd_3624912 : Nat := 620440728750275582943113

theorem tailTrace_3624912 : CollatzResearch.WordTrace tailWord_3624912 prefixEnd_3624912 620440728750275582943113 := by
  unfold tailWord_3624912
  simp only [CollatzResearch.WordTrace]
  refine ⟨66105701121785192263390495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88140934829046923017853993 66105701121785192263390495)
  ·
    refine ⟨99158551682677788395085743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66105701121785192263390495 99158551682677788395085743)
    ·
      refine ⟨148737827524016682592628615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99158551682677788395085743 148737827524016682592628615)
      ·
        refine ⟨223106741286025023888942923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148737827524016682592628615 223106741286025023888942923)
        ·
          refine ⟨334660111929037535833414385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 223106741286025023888942923 334660111929037535833414385)
          ·
            refine ⟨250995083946778151875060789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 334660111929037535833414385 250995083946778151875060789)
            ·
              refine ⟨23530789120010451738286949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 250995083946778151875060789 23530789120010451738286949)
              ·
                refine ⟨4412022960001959700928803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23530789120010451738286949 4412022960001959700928803)
                ·
                  refine ⟨6618034440002939551393205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4412022960001959700928803 6618034440002939551393205)
                  ·
                    refine ⟨620440728750275582943113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6618034440002939551393205 620440728750275582943113)
                    ·
                      rfl

theorem cell23_3624912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 5, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 5, 4, 1, 5].length) (baseStart_3624912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3624912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3624912 prefixEnd_3624912 := by exact prefixLift 3624912
  have htrace : WordTrace (prefixWord ++ tailWord_3624912) baseStart_3624912 baseEnd_3624912 := by
    simpa [prefixWord, tailWord_3624912, baseEnd_3624912] using wordTrace_append hprefix tailTrace_3624912
  have hstable : (prefixWord ++ tailWord_3624912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3624912).length < 2 ^ (prefixWord ++ tailWord_3624912).sum := by decide
  have hdescent : baseEnd_3624912 < baseStart_3624912 := by decide
  rcases family_descends (prefixWord ++ tailWord_3624912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3624919 : List Nat := [1, 1, 3, 2, 1, 1, 4, 3, 2, 3, 2]
def baseStart_3624919 : Nat := 118140960795 + 3624919 * 2 ^ 59
def prefixEnd_3624919 : Nat := 4983230072969 + 3 ^ 40 * 3624919 * 2
def baseEnd_3624919 : Nat := 1861325780615408221441807

theorem tailTrace_3624919 : CollatzResearch.WordTrace tailWord_3624919 prefixEnd_3624919 1861325780615408221441807 := by
  unfold tailWord_3624919
  simp only [CollatzResearch.WordTrace]
  refine ⟨132211657554545024722285811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88141105036363349814857207 132211657554545024722285811)
  ·
    refine ⟨198317486331817537083428717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132211657554545024722285811 198317486331817537083428717)
    ·
      refine ⟨74369057374431576406285769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 198317486331817537083428717 74369057374431576406285769)
      ·
        refine ⟨55776793030823682304714327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74369057374431576406285769 55776793030823682304714327)
        ·
          refine ⟨83665189546235523457071491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55776793030823682304714327 83665189546235523457071491)
          ·
            refine ⟨125497784319353285185607237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83665189546235523457071491 125497784319353285185607237)
            ·
              refine ⟨23530834559878740972301357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 125497784319353285185607237 23530834559878740972301357)
              ·
                refine ⟨8824062959954527864613009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23530834559878740972301357 8824062959954527864613009)
                ·
                  refine ⟨6618047219965895898459757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8824062959954527864613009 6618047219965895898459757)
                  ·
                    refine ⟨2481767707487210961922409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6618047219965895898459757 2481767707487210961922409)
                    ·
                      refine ⟨1861325780615408221441807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2481767707487210961922409 1861325780615408221441807)
                      ·
                        rfl

theorem cell23_3624919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 4, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 4, 3, 2, 3, 2].length) (baseStart_3624919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3624919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3624919 prefixEnd_3624919 := by exact prefixLift 3624919
  have htrace : WordTrace (prefixWord ++ tailWord_3624919) baseStart_3624919 baseEnd_3624919 := by
    simpa [prefixWord, tailWord_3624919, baseEnd_3624919] using wordTrace_append hprefix tailTrace_3624919
  have hstable : (prefixWord ++ tailWord_3624919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3624919).length < 2 ^ (prefixWord ++ tailWord_3624919).sum := by decide
  have hdescent : baseEnd_3624919 < baseStart_3624919 := by decide
  rcases family_descends (prefixWord ++ tailWord_3624919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3624943 : List Nat := [1, 1, 2, 1, 4, 2, 5, 2, 1, 1, 3]
def baseStart_3624943 : Nat := 118140960795 + 3624943 * 2 ^ 59
def prefixEnd_3624943 : Nat := 4983230072969 + 3 ^ 40 * 3624943 * 2
def baseEnd_3624943 : Nat := 1861338104151116127541697

theorem tailTrace_3624943 : CollatzResearch.WordTrace tailWord_3624943 prefixEnd_3624943 1861338104151116127541697 := by
  unfold tailWord_3624943
  simp only [CollatzResearch.WordTrace]
  refine ⟨132212532906458076821159483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88141688604305384547439655 132212532906458076821159483)
  ·
    refine ⟨198318799359687115231739225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132212532906458076821159483 198318799359687115231739225)
    ·
      refine ⟨148739099519765336423804419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 198318799359687115231739225 148739099519765336423804419)
      ·
        refine ⟨223108649279648004635706629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148739099519765336423804419 223108649279648004635706629)
        ·
          refine ⟨41832871739934000869194993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 223108649279648004635706629 41832871739934000869194993)
          ·
            refine ⟨31374653804950500651896245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41832871739934000869194993 31374653804950500651896245)
            ·
              refine ⟨2941373794214109436115273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 31374653804950500651896245 2941373794214109436115273)
              ·
                refine ⟨2206030345660582077086455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2941373794214109436115273 2206030345660582077086455)
                ·
                  refine ⟨3309045518490873115629683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2206030345660582077086455 3309045518490873115629683)
                  ·
                    refine ⟨4963568277736309673444525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3309045518490873115629683 4963568277736309673444525)
                    ·
                      refine ⟨1861338104151116127541697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4963568277736309673444525 1861338104151116127541697)
                      ·
                        rfl

theorem cell23_3624943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 5, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 5, 2, 1, 1, 3].length) (baseStart_3624943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3624943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3624943 prefixEnd_3624943 := by exact prefixLift 3624943
  have htrace : WordTrace (prefixWord ++ tailWord_3624943) baseStart_3624943 baseEnd_3624943 := by
    simpa [prefixWord, tailWord_3624943, baseEnd_3624943] using wordTrace_append hprefix tailTrace_3624943
  have hstable : (prefixWord ++ tailWord_3624943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3624943).length < 2 ^ (prefixWord ++ tailWord_3624943).sum := by decide
  have hdescent : baseEnd_3624943 < baseStart_3624943 := by decide
  rcases family_descends (prefixWord ++ tailWord_3624943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3624952 : List Nat := [2, 1, 2, 1, 1, 3, 4, 2, 1, 1, 5]
def baseStart_3624952 : Nat := 118140960795 + 3624952 * 2 ^ 59
def prefixEnd_3624952 : Nat := 4983230072969 + 3 ^ 40 * 3624952 * 2
def baseEnd_3624952 : Nat := 1861342725477006592329155

theorem tailTrace_3624952 : CollatzResearch.WordTrace tailWord_3624952 prefixEnd_3624952 1861342725477006592329155 := by
  unfold tailWord_3624952
  simp only [CollatzResearch.WordTrace]
  refine ⟨66106430581712735679118555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88141907442283647572158073 66106430581712735679118555)
  ·
    refine ⟨99159645872569103518677833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66106430581712735679118555 99159645872569103518677833)
    ·
      refine ⟨74369734404426827639008375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99159645872569103518677833 74369734404426827639008375)
      ·
        refine ⟨111554601606640241458512563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74369734404426827639008375 111554601606640241458512563)
        ·
          refine ⟨167331902409960362187768845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111554601606640241458512563 167331902409960362187768845)
          ·
            refine ⟨62749463403735135820413317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 167331902409960362187768845 62749463403735135820413317)
            ·
              refine ⟨11765524388200337966327497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 62749463403735135820413317 11765524388200337966327497)
              ·
                refine ⟨8824143291150253474745623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11765524388200337966327497 8824143291150253474745623)
                ·
                  refine ⟨13236214936725380212118435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8824143291150253474745623 13236214936725380212118435)
                  ·
                    refine ⟨19854322405088070318177653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13236214936725380212118435 19854322405088070318177653)
                    ·
                      refine ⟨1861342725477006592329155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19854322405088070318177653 1861342725477006592329155)
                      ·
                        rfl

theorem cell23_3624952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 4, 2, 1, 1, 5].length) (baseStart_3624952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3624952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3624952 prefixEnd_3624952 := by exact prefixLift 3624952
  have htrace : WordTrace (prefixWord ++ tailWord_3624952) baseStart_3624952 baseEnd_3624952 := by
    simpa [prefixWord, tailWord_3624952, baseEnd_3624952] using wordTrace_append hprefix tailTrace_3624952
  have hstable : (prefixWord ++ tailWord_3624952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3624952).length < 2 ^ (prefixWord ++ tailWord_3624952).sum := by decide
  have hdescent : baseEnd_3624952 < baseStart_3624952 := by decide
  rcases family_descends (prefixWord ++ tailWord_3624952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3624955 : List Nat := [1, 1, 1, 1, 1, 3, 5, 10]
def baseStart_3624955 : Nat := 118140960795 + 3624955 * 2 ^ 59
def prefixEnd_3624955 : Nat := 4983230072969 + 3 ^ 40 * 3624955 * 2
def baseEnd_3624955 : Nat := 68938676515517410392283

theorem tailTrace_3624955 : CollatzResearch.WordTrace tailWord_3624955 prefixEnd_3624955 68938676515517410392283 := by
  unfold tailWord_3624955
  simp only [CollatzResearch.WordTrace]
  refine ⟨132212970582414602870596319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88141980388276401913730879 132212970582414602870596319)
  ·
    refine ⟨198319455873621904305894479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132212970582414602870596319 198319455873621904305894479)
    ·
      refine ⟨297479183810432856458841719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198319455873621904305894479 297479183810432856458841719)
      ·
        refine ⟨446218775715649284688262579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 297479183810432856458841719 446218775715649284688262579)
        ·
          refine ⟨669328163573473927032393869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 446218775715649284688262579 669328163573473927032393869)
          ·
            refine ⟨250998061340052722637147701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 669328163573473927032393869 250998061340052722637147701)
            ·
              refine ⟨23531068250629942747232597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 250998061340052722637147701 23531068250629942747232597)
              ·
                refine ⟨68938676515517410392283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 23531068250629942747232597 68938676515517410392283)
                ·
                  rfl

theorem cell23_3624955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 5, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 5, 10].length) (baseStart_3624955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3624955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3624955 prefixEnd_3624955 := by exact prefixLift 3624955
  have htrace : WordTrace (prefixWord ++ tailWord_3624955) baseStart_3624955 baseEnd_3624955 := by
    simpa [prefixWord, tailWord_3624955, baseEnd_3624955] using wordTrace_append hprefix tailTrace_3624955
  have hstable : (prefixWord ++ tailWord_3624955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3624955).length < 2 ^ (prefixWord ++ tailWord_3624955).sum := by decide
  have hdescent : baseEnd_3624955 < baseStart_3624955 := by decide
  rcases family_descends (prefixWord ++ tailWord_3624955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3624980 : List Nat := [2, 4, 3, 2, 1, 1, 3, 1, 1, 5]
def baseStart_3624980 : Nat := 118140960795 + 3624980 * 2 ^ 59
def prefixEnd_3624980 : Nat := 4983230072969 + 3 ^ 40 * 3624980 * 2
def baseEnd_3624980 : Nat := 620452367645110827593009

theorem tailTrace_3624980 : CollatzResearch.WordTrace tailWord_3624980 prefixEnd_3624980 620452367645110827593009 := by
  unfold tailWord_3624980
  simp only [CollatzResearch.WordTrace]
  refine ⟨66106941203662016070128197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88142588271549354760170929 66106941203662016070128197)
  ·
    refine ⟨12395051475686628013149037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 66106941203662016070128197 12395051475686628013149037)
    ·
      refine ⟨4648144303382485504930889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12395051475686628013149037 4648144303382485504930889)
      ·
        refine ⟨3486108227536864128698167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4648144303382485504930889 3486108227536864128698167)
        ·
          refine ⟨5229162341305296193047251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3486108227536864128698167 5229162341305296193047251)
          ·
            refine ⟨7843743511957944289570877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5229162341305296193047251 7843743511957944289570877)
            ·
              refine ⟨2941403816984229108589079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7843743511957944289570877 2941403816984229108589079)
              ·
                refine ⟨4412105725476343662883619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2941403816984229108589079 4412105725476343662883619)
                ·
                  refine ⟨6618158588214515494325429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4412105725476343662883619 6618158588214515494325429)
                  ·
                    refine ⟨620452367645110827593009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6618158588214515494325429 620452367645110827593009)
                    ·
                      rfl

theorem cell23_3624980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 3, 1, 1, 5].length) (baseStart_3624980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3624980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3624980 prefixEnd_3624980 := by exact prefixLift 3624980
  have htrace : WordTrace (prefixWord ++ tailWord_3624980) baseStart_3624980 baseEnd_3624980 := by
    simpa [prefixWord, tailWord_3624980, baseEnd_3624980] using wordTrace_append hprefix tailTrace_3624980
  have hstable : (prefixWord ++ tailWord_3624980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3624980).length < 2 ^ (prefixWord ++ tailWord_3624980).sum := by decide
  have hdescent : baseEnd_3624980 < baseStart_3624980 := by decide
  rcases family_descends (prefixWord ++ tailWord_3624980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3624983 : List Nat := [1, 1, 3, 5, 2, 1, 3, 1, 1, 1, 4]
def baseStart_3624983 : Nat := 118140960795 + 3624983 * 2 ^ 59
def prefixEnd_3624983 : Nat := 4983230072969 + 3 ^ 40 * 3624983 * 2
def baseEnd_3624983 : Nat := 1861358643377295971041513

theorem tailTrace_3624983 : CollatzResearch.WordTrace tailWord_3624983 prefixEnd_3624983 1861358643377295971041513 := by
  unfold tailWord_3624983
  simp only [CollatzResearch.WordTrace]
  refine ⟨132213991826313163652615603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88142661217542109101743735 132213991826313163652615603)
  ·
    refine ⟨198320987739469745478923405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132213991826313163652615603 198320987739469745478923405)
    ·
      refine ⟨74370370402301154554596277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 198320987739469745478923405 74370370402301154554596277)
      ·
        refine ⟨6972222225215733239493401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 74370370402301154554596277 6972222225215733239493401)
        ·
          refine ⟨5229166668911799929620051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6972222225215733239493401 5229166668911799929620051)
          ·
            refine ⟨7843750003367699894430077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5229166668911799929620051 7843750003367699894430077)
            ·
              refine ⟨2941406251262887460411279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7843750003367699894430077 2941406251262887460411279)
              ·
                refine ⟨4412109376894331190616919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2941406251262887460411279 4412109376894331190616919)
                ·
                  refine ⟨6618164065341496785925379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4412109376894331190616919 6618164065341496785925379)
                  ·
                    refine ⟨9927246098012245178888069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6618164065341496785925379 9927246098012245178888069)
                    ·
                      refine ⟨1861358643377295971041513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9927246098012245178888069 1861358643377295971041513)
                      ·
                        rfl

theorem cell23_3624983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 3, 1, 1, 1, 4].length) (baseStart_3624983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3624983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3624983 prefixEnd_3624983 := by exact prefixLift 3624983
  have htrace : WordTrace (prefixWord ++ tailWord_3624983) baseStart_3624983 baseEnd_3624983 := by
    simpa [prefixWord, tailWord_3624983, baseEnd_3624983] using wordTrace_append hprefix tailTrace_3624983
  have hstable : (prefixWord ++ tailWord_3624983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3624983).length < 2 ^ (prefixWord ++ tailWord_3624983).sum := by decide
  have hdescent : baseEnd_3624983 < baseStart_3624983 := by decide
  rcases family_descends (prefixWord ++ tailWord_3624983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3625016 : List Nat := [2, 1, 2, 1, 6, 1, 2, 1, 1, 3, 3]
def baseStart_3625016 : Nat := 118140960795 + 3625016 * 2 ^ 59
def prefixEnd_3625016 : Nat := 4983230072969 + 3 ^ 40 * 3625016 * 2
def baseEnd_3625016 : Nat := 1861375588238894341928861

theorem tailTrace_3625016 : CollatzResearch.WordTrace tailWord_3625016 prefixEnd_3625016 1861375588238894341928861 := by
  unfold tailWord_3625016
  simp only [CollatzResearch.WordTrace]
  refine ⟨66107597717596805144283451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88143463623462406859044601 66107597717596805144283451)
  ·
    refine ⟨99161396576395207716425177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66107597717596805144283451 99161396576395207716425177)
    ·
      refine ⟨74371047432296405787318883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99161396576395207716425177 74371047432296405787318883)
      ·
        refine ⟨111556571148444608680978325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74371047432296405787318883 111556571148444608680978325)
        ·
          refine ⟨5229214272583341031920859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 111556571148444608680978325 5229214272583341031920859)
          ·
            refine ⟨7843821408875011547881289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5229214272583341031920859 7843821408875011547881289)
            ·
              refine ⟨5882866056656258660910967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7843821408875011547881289 5882866056656258660910967)
              ·
                refine ⟨8824299084984387991366451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5882866056656258660910967 8824299084984387991366451)
                ·
                  refine ⟨13236448627476581987049677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8824299084984387991366451 13236448627476581987049677)
                  ·
                    refine ⟨4963668235303718245143629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13236448627476581987049677 4963668235303718245143629)
                    ·
                      refine ⟨1861375588238894341928861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4963668235303718245143629 1861375588238894341928861)
                      ·
                        rfl

theorem cell23_3625016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 2, 1, 1, 3, 3].length) (baseStart_3625016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3625016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3625016 prefixEnd_3625016 := by exact prefixLift 3625016
  have htrace : WordTrace (prefixWord ++ tailWord_3625016) baseStart_3625016 baseEnd_3625016 := by
    simpa [prefixWord, tailWord_3625016, baseEnd_3625016] using wordTrace_append hprefix tailTrace_3625016
  have hstable : (prefixWord ++ tailWord_3625016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3625016).length < 2 ^ (prefixWord ++ tailWord_3625016).sum := by decide
  have hdescent : baseEnd_3625016 < baseStart_3625016 := by decide
  rcases family_descends (prefixWord ++ tailWord_3625016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3625069 : List Nat := [1, 5, 1, 1, 2, 1, 1, 3, 2, 2, 4]
def baseStart_3625069 : Nat := 118140960795 + 3625069 * 2 ^ 59
def prefixEnd_3625069 : Nat := 4983230072969 + 3 ^ 40 * 3625069 * 2
def baseEnd_3625069 : Nat := 1861402802713582634566117

theorem tailTrace_3625069 : CollatzResearch.WordTrace tailWord_3625069 prefixEnd_3625069 1861402802713582634566117 := by
  unfold tailWord_3625069
  simp only [CollatzResearch.WordTrace]
  refine ⟨132217128504001600340246261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88144752336001066893497507 132217128504001600340246261)
  ·
    refine ⟨12395355797250150031898087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 132217128504001600340246261 12395355797250150031898087)
    ·
      refine ⟨18593033695875225047847131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12395355797250150031898087 18593033695875225047847131)
      ·
        refine ⟨27889550543812837571770697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18593033695875225047847131 27889550543812837571770697)
        ·
          refine ⟨20917162907859628178828023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27889550543812837571770697 20917162907859628178828023)
          ·
            refine ⟨31375744361789442268242035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20917162907859628178828023 31375744361789442268242035)
            ·
              refine ⟨47063616542684163402363053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31375744361789442268242035 47063616542684163402363053)
              ·
                refine ⟨17648856203506561275886145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47063616542684163402363053 17648856203506561275886145)
                ·
                  refine ⟨13236642152629920956914609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17648856203506561275886145 13236642152629920956914609)
                  ·
                    refine ⟨9927481614472440717685957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13236642152629920956914609 9927481614472440717685957)
                    ·
                      refine ⟨1861402802713582634566117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9927481614472440717685957 1861402802713582634566117)
                      ·
                        rfl

theorem cell23_3625069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 3, 2, 2, 4].length) (baseStart_3625069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3625069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3625069 prefixEnd_3625069 := by exact prefixLift 3625069
  have htrace : WordTrace (prefixWord ++ tailWord_3625069) baseStart_3625069 baseEnd_3625069 := by
    simpa [prefixWord, tailWord_3625069, baseEnd_3625069] using wordTrace_append hprefix tailTrace_3625069
  have hstable : (prefixWord ++ tailWord_3625069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3625069).length < 2 ^ (prefixWord ++ tailWord_3625069).sum := by decide
  have hdescent : baseEnd_3625069 < baseStart_3625069 := by decide
  rcases family_descends (prefixWord ++ tailWord_3625069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3625099 : List Nat := [1, 1, 1, 1, 4, 1, 1, 1, 3, 7, 2]
def baseStart_3625099 : Nat := 118140960795 + 3625099 * 2 ^ 59
def prefixEnd_3625099 : Nat := 4983230072969 + 3 ^ 40 * 3625099 * 2
def baseEnd_3625099 : Nat := 1861418207133217517190979

theorem tailTrace_3625099 : CollatzResearch.WordTrace tailWord_3625099 prefixEnd_3625099 1861418207133217517190979 := by
  unfold tailWord_3625099
  simp only [CollatzResearch.WordTrace]
  refine ⟨132218222693892915463838351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88145481795928610309225567 132218222693892915463838351)
  ·
    refine ⟨198327334040839373195757527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132218222693892915463838351 198327334040839373195757527)
    ·
      refine ⟨297491001061259059793636291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198327334040839373195757527 297491001061259059793636291)
      ·
        refine ⟨446236501591888589690454437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 297491001061259059793636291 446236501591888589690454437)
        ·
          refine ⟨83669344048479110566960207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 446236501591888589690454437 83669344048479110566960207)
          ·
            refine ⟨125504016072718665850440311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83669344048479110566960207 125504016072718665850440311)
            ·
              refine ⟨188256024109077998775660467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 125504016072718665850440311 188256024109077998775660467)
              ·
                refine ⟨282384036163616998163490701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 188256024109077998775660467 282384036163616998163490701)
                ·
                  refine ⟨105894013561356374311309013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 282384036163616998163490701 105894013561356374311309013)
                  ·
                    refine ⟨2481890942844290022921305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 105894013561356374311309013 2481890942844290022921305)
                    ·
                      refine ⟨1861418207133217517190979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2481890942844290022921305 1861418207133217517190979)
                      ·
                        rfl

theorem cell23_3625099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 1, 3, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 1, 3, 7, 2].length) (baseStart_3625099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3625099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3625099 prefixEnd_3625099 := by exact prefixLift 3625099
  have htrace : WordTrace (prefixWord ++ tailWord_3625099) baseStart_3625099 baseEnd_3625099 := by
    simpa [prefixWord, tailWord_3625099, baseEnd_3625099] using wordTrace_append hprefix tailTrace_3625099
  have hstable : (prefixWord ++ tailWord_3625099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3625099).length < 2 ^ (prefixWord ++ tailWord_3625099).sum := by decide
  have hdescent : baseEnd_3625099 < baseStart_3625099 := by decide
  rcases family_descends (prefixWord ++ tailWord_3625099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3625109 : List Nat := [1, 3, 2, 1, 1, 1, 5, 2, 2, 5]
def baseStart_3625109 : Nat := 118140960795 + 3625109 * 2 ^ 59
def prefixEnd_3625109 : Nat := 4983230072969 + 3 ^ 40 * 3625109 * 2
def baseEnd_3625109 : Nat := 620474447313254159355311

theorem tailTrace_3625109 : CollatzResearch.WordTrace tailWord_3625109 prefixEnd_3625109 620474447313254159355311 := by
  unfold tailWord_3625109
  simp only [CollatzResearch.WordTrace]
  refine ⟨132218587423856687171702381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88145724949237791447801587 132218587423856687171702381)
  ·
    refine ⟨49581970283946257689388393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 132218587423856687171702381 49581970283946257689388393)
    ·
      refine ⟨37186477712959693267041295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49581970283946257689388393 37186477712959693267041295)
      ·
        refine ⟨55779716569439539900561943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37186477712959693267041295 55779716569439539900561943)
        ·
          refine ⟨83669574854159309850842915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55779716569439539900561943 83669574854159309850842915)
          ·
            refine ⟨125504362281238964776264373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83669574854159309850842915 125504362281238964776264373)
            ·
              refine ⟨11766033963866152947774785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 125504362281238964776264373 11766033963866152947774785)
              ·
                refine ⟨8824525472899614710831089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11766033963866152947774785 8824525472899614710831089)
                ·
                  refine ⟨6618394104674711033123317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8824525472899614710831089 6618394104674711033123317)
                  ·
                    refine ⟨620474447313254159355311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6618394104674711033123317 620474447313254159355311)
                    ·
                      rfl

theorem cell23_3625109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 5, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 5, 2, 2, 5].length) (baseStart_3625109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3625109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3625109 prefixEnd_3625109 := by exact prefixLift 3625109
  have htrace : WordTrace (prefixWord ++ tailWord_3625109) baseStart_3625109 baseEnd_3625109 := by
    simpa [prefixWord, tailWord_3625109, baseEnd_3625109] using wordTrace_append hprefix tailTrace_3625109
  have hstable : (prefixWord ++ tailWord_3625109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3625109).length < 2 ^ (prefixWord ++ tailWord_3625109).sum := by decide
  have hdescent : baseEnd_3625109 < baseStart_3625109 := by decide
  rcases family_descends (prefixWord ++ tailWord_3625109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3625116 : List Nat := [2, 2, 3, 2, 1, 1, 2, 1, 2, 5, 2]
def baseStart_3625116 : Nat := 118140960795 + 3625116 * 2 ^ 59
def prefixEnd_3625116 : Nat := 4983230072969 + 3 ^ 40 * 3625116 * 2
def baseEnd_3625116 : Nat := 1861426936304343950678401

theorem tailTrace_3625116 : CollatzResearch.WordTrace tailWord_3625116 prefixEnd_3625116 1861426936304343950678401 := by
  unfold tailWord_3625116
  simp only [CollatzResearch.WordTrace]
  refine ⟨66109421367415663683603601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88145895156554218244804801 66109421367415663683603601)
  ·
    refine ⟨49582066025561747762702701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66109421367415663683603601 49582066025561747762702701)
    ·
      refine ⟨18593274759585655411013513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49582066025561747762702701 18593274759585655411013513)
      ·
        refine ⟨13944956069689241558260135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18593274759585655411013513 13944956069689241558260135)
        ·
          refine ⟨20917434104533862337390203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13944956069689241558260135 20917434104533862337390203)
          ·
            refine ⟨31376151156800793506085305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20917434104533862337390203 31376151156800793506085305)
            ·
              refine ⟨23532113367600595129563979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31376151156800793506085305 23532113367600595129563979)
              ·
                refine ⟨35298170051400892694345969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23532113367600595129563979 35298170051400892694345969)
                ·
                  refine ⟨26473627538550669520759477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35298170051400892694345969 26473627538550669520759477)
                  ·
                    refine ⟨2481902581739125267571201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 26473627538550669520759477 2481902581739125267571201)
                    ·
                      refine ⟨1861426936304343950678401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2481902581739125267571201 1861426936304343950678401)
                      ·
                        rfl

theorem cell23_3625116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 2, 1, 2, 5, 2].length) (baseStart_3625116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3625116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3625116 prefixEnd_3625116 := by exact prefixLift 3625116
  have htrace : WordTrace (prefixWord ++ tailWord_3625116) baseStart_3625116 baseEnd_3625116 := by
    simpa [prefixWord, tailWord_3625116, baseEnd_3625116] using wordTrace_append hprefix tailTrace_3625116
  have hstable : (prefixWord ++ tailWord_3625116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3625116).length < 2 ^ (prefixWord ++ tailWord_3625116).sum := by decide
  have hdescent : baseEnd_3625116 < baseStart_3625116 := by decide
  rcases family_descends (prefixWord ++ tailWord_3625116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3625119 : List Nat := [1, 1, 2, 6, 1, 1, 1, 1, 1, 1, 7]
def baseStart_3625119 : Nat := 118140960795 + 3625119 * 2 ^ 59
def prefixEnd_3625119 : Nat := 4983230072969 + 3 ^ 40 * 3625119 * 2
def baseEnd_3625119 : Nat := 1861428476746307438940887

theorem tailTrace_3625119 : CollatzResearch.WordTrace tailWord_3625119 prefixEnd_3625119 1861428476746307438940887 := by
  unfold tailWord_3625119
  simp only [CollatzResearch.WordTrace]
  refine ⟨132218952153820458879566411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88145968102546972586377607 132218952153820458879566411)
  ·
    refine ⟨198328428230730688319349617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132218952153820458879566411 198328428230730688319349617)
    ·
      refine ⟨148746321173048016239512213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 198328428230730688319349617 148746321173048016239512213)
      ·
        refine ⟨6972483804986625761227135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 148746321173048016239512213 6972483804986625761227135)
        ·
          refine ⟨10458725707479938641840703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6972483804986625761227135 10458725707479938641840703)
          ·
            refine ⟨15688088561219907962761055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10458725707479938641840703 15688088561219907962761055)
            ·
              refine ⟨23532132841829861944141583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15688088561219907962761055 23532132841829861944141583)
              ·
                refine ⟨35298199262744792916212375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23532132841829861944141583 35298199262744792916212375)
                ·
                  refine ⟨52947298894117189374318563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35298199262744792916212375 52947298894117189374318563)
                  ·
                    refine ⟨79420948341175784061477845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 52947298894117189374318563 79420948341175784061477845)
                    ·
                      refine ⟨1861428476746307438940887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 79420948341175784061477845 1861428476746307438940887)
                      ·
                        rfl

theorem cell23_3625119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 1, 1, 1, 1, 7].length) (baseStart_3625119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3625119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3625119 prefixEnd_3625119 := by exact prefixLift 3625119
  have htrace : WordTrace (prefixWord ++ tailWord_3625119) baseStart_3625119 baseEnd_3625119 := by
    simpa [prefixWord, tailWord_3625119, baseEnd_3625119] using wordTrace_append hprefix tailTrace_3625119
  have hstable : (prefixWord ++ tailWord_3625119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3625119).length < 2 ^ (prefixWord ++ tailWord_3625119).sum := by decide
  have hdescent : baseEnd_3625119 < baseStart_3625119 := by decide
  rcases family_descends (prefixWord ++ tailWord_3625119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3625124 : List Nat := [2, 3, 1, 2, 5, 1, 2, 1, 2, 2, 2]
def baseStart_3625124 : Nat := 118140960795 + 3625124 * 2 ^ 59
def prefixEnd_3625124 : Nat := 4983230072969 + 3 ^ 40 * 3625124 * 2
def baseEnd_3625124 : Nat := 1861431044149579919378365

theorem tailTrace_3625124 : CollatzResearch.WordTrace tailWord_3625124 prefixEnd_3625124 1861431044149579919378365 := by
  unfold tailWord_3625124
  simp only [CollatzResearch.WordTrace]
  refine ⟨66109567259401172366749213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88146089679201563155665617 66109567259401172366749213)
  ·
    refine ⟨24791087722275439637530955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66109567259401172366749213 24791087722275439637530955)
    ·
      refine ⟨37186631583413159456296433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24791087722275439637530955 37186631583413159456296433)
      ·
        refine ⟨27889973687559869592222325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37186631583413159456296433 27889973687559869592222325)
        ·
          refine ⟨2614685033208737774270843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 27889973687559869592222325 2614685033208737774270843)
          ·
            refine ⟨3922027549813106661406265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2614685033208737774270843 3922027549813106661406265)
            ·
              refine ⟨2941520662359829996054699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3922027549813106661406265 2941520662359829996054699)
              ·
                refine ⟨4412280993539744994082049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2941520662359829996054699 4412280993539744994082049)
                ·
                  refine ⟨3309210745154808745561537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4412280993539744994082049 3309210745154808745561537)
                  ·
                    refine ⟨2481908058866106559171153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3309210745154808745561537 2481908058866106559171153)
                    ·
                      refine ⟨1861431044149579919378365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2481908058866106559171153 1861431044149579919378365)
                      ·
                        rfl

theorem cell23_3625124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 5, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 5, 1, 2, 1, 2, 2, 2].length) (baseStart_3625124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3625124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3625124 prefixEnd_3625124 := by exact prefixLift 3625124
  have htrace : WordTrace (prefixWord ++ tailWord_3625124) baseStart_3625124 baseEnd_3625124 := by
    simpa [prefixWord, tailWord_3625124, baseEnd_3625124] using wordTrace_append hprefix tailTrace_3625124
  have hstable : (prefixWord ++ tailWord_3625124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3625124).length < 2 ^ (prefixWord ++ tailWord_3625124).sum := by decide
  have hdescent : baseEnd_3625124 < baseStart_3625124 := by decide
  rcases family_descends (prefixWord ++ tailWord_3625124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3625132 : List Nat := [2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 9]
def baseStart_3625132 : Nat := 118140960795 + 3625132 * 2 ^ 59
def prefixEnd_3625132 : Nat := 4983230072969 + 3 ^ 40 * 3625132 * 2
def baseEnd_3625132 : Nat := 1861435151994815888078327

theorem tailTrace_3625132 : CollatzResearch.WordTrace tailWord_3625132 prefixEnd_3625132 1861435151994815888078327 := by
  unfold tailWord_3625132
  simp only [CollatzResearch.WordTrace]
  refine ⟨66109713151386681049894825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88146284201848908066526433 66109713151386681049894825)
  ·
    refine ⟨49582284863540010787421119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66109713151386681049894825 49582284863540010787421119)
    ·
      refine ⟨74373427295310016181131679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49582284863540010787421119 74373427295310016181131679)
      ·
        refine ⟨111560140942965024271697519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74373427295310016181131679 111560140942965024271697519)
        ·
          refine ⟨167340211414447536407546279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111560140942965024271697519 167340211414447536407546279)
          ·
            refine ⟨251010317121671304611319419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 167340211414447536407546279 251010317121671304611319419)
            ·
              refine ⟨376515475682506956916979129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 251010317121671304611319419 376515475682506956916979129)
              ·
                refine ⟨282386606761880217687734347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 376515475682506956916979129 282386606761880217687734347)
                ·
                  refine ⟨423579910142820326531601521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 282386606761880217687734347 423579910142820326531601521)
                  ·
                    refine ⟨317684932607115244898701141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 423579910142820326531601521 317684932607115244898701141)
                    ·
                      refine ⟨1861435151994815888078327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 317684932607115244898701141 1861435151994815888078327)
                      ·
                        rfl

theorem cell23_3625132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 9].length) (baseStart_3625132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3625132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3625132 prefixEnd_3625132 := by exact prefixLift 3625132
  have htrace : WordTrace (prefixWord ++ tailWord_3625132) baseStart_3625132 baseEnd_3625132 := by
    simpa [prefixWord, tailWord_3625132, baseEnd_3625132] using wordTrace_append hprefix tailTrace_3625132
  have hstable : (prefixWord ++ tailWord_3625132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3625132).length < 2 ^ (prefixWord ++ tailWord_3625132).sum := by decide
  have hdescent : baseEnd_3625132 < baseStart_3625132 := by decide
  rcases family_descends (prefixWord ++ tailWord_3625132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3625139 : List Nat := [1, 1, 1, 2, 3, 2, 1, 3, 5, 4]
def baseStart_3625139 : Nat := 118140960795 + 3625139 * 2 ^ 59
def prefixEnd_3625139 : Nat := 4983230072969 + 3 ^ 40 * 3625139 * 2
def baseEnd_3625139 : Nat := 620479582119799120230265

theorem tailTrace_3625139 : CollatzResearch.WordTrace tailWord_3625139 prefixEnd_3625139 620479582119799120230265 := by
  unfold tailWord_3625139
  simp only [CollatzResearch.WordTrace]
  refine ⟨132219681613748002295294471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88146454409165334863529647 132219681613748002295294471)
  ·
    refine ⟨198329522420622003442941707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132219681613748002295294471 198329522420622003442941707)
    ·
      refine ⟨297494283630933005164412561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198329522420622003442941707 297494283630933005164412561)
      ·
        refine ⟨223120712723199753873309421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 297494283630933005164412561 223120712723199753873309421)
        ·
          refine ⟨83670267271199907702491033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 223120712723199753873309421 83670267271199907702491033)
          ·
            refine ⟨62752700453399930776868275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83670267271199907702491033 62752700453399930776868275)
            ·
              refine ⟨94129050680099896165302413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62752700453399930776868275 94129050680099896165302413)
              ·
                refine ⟨35298394005037461061988405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 94129050680099896165302413 35298394005037461061988405)
                ·
                  refine ⟨3309224437972261974561413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 35298394005037461061988405 3309224437972261974561413)
                  ·
                    refine ⟨620479582119799120230265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3309224437972261974561413 620479582119799120230265)
                    ·
                      rfl

theorem cell23_3625139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 3, 5, 4].length) (baseStart_3625139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3625139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3625139 prefixEnd_3625139 := by exact prefixLift 3625139
  have htrace : WordTrace (prefixWord ++ tailWord_3625139) baseStart_3625139 baseEnd_3625139 := by
    simpa [prefixWord, tailWord_3625139, baseEnd_3625139] using wordTrace_append hprefix tailTrace_3625139
  have hstable : (prefixWord ++ tailWord_3625139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3625139).length < 2 ^ (prefixWord ++ tailWord_3625139).sum := by decide
  have hdescent : baseEnd_3625139 < baseStart_3625139 := by decide
  rcases family_descends (prefixWord ++ tailWord_3625139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3625169 : List Nat := [1, 2, 2, 1, 2, 2, 3, 4, 6]
def baseStart_3625169 : Nat := 118140960795 + 3625169 * 2 ^ 59
def prefixEnd_3625169 : Nat := 4983230072969 + 3 ^ 40 * 3625169 * 2
def baseEnd_3625169 : Nat := 206828238975448027035073

theorem tailTrace_3625169 : CollatzResearch.WordTrace tailWord_3625169 prefixEnd_3625169 206828238975448027035073 := by
  unfold tailWord_3625169
  simp only [CollatzResearch.WordTrace]
  refine ⟨132220775803639317418886561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88147183869092878279257707 132220775803639317418886561)
  ·
    refine ⟨99165581852729488064164921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132220775803639317418886561 99165581852729488064164921)
    ·
      refine ⟨74374186389547116048123691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99165581852729488064164921 74374186389547116048123691)
      ·
        refine ⟨111561279584320674072185537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74374186389547116048123691 111561279584320674072185537)
        ·
          refine ⟨83670959688240505554139153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 111561279584320674072185537 83670959688240505554139153)
          ·
            refine ⟨62753219766180379165604365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83670959688240505554139153 62753219766180379165604365)
            ·
              refine ⟨23532457412317642187101637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62753219766180379165604365 23532457412317642187101637)
              ·
                refine ⟨4412335764809557910081557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23532457412317642187101637 4412335764809557910081557)
                ·
                  refine ⟨206828238975448027035073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4412335764809557910081557 206828238975448027035073)
                  ·
                    rfl

theorem cell23_3625169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 3, 4, 6].length) (baseStart_3625169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3625169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3625169 prefixEnd_3625169 := by exact prefixLift 3625169
  have htrace : WordTrace (prefixWord ++ tailWord_3625169) baseStart_3625169 baseEnd_3625169 := by
    simpa [prefixWord, tailWord_3625169, baseEnd_3625169] using wordTrace_append hprefix tailTrace_3625169
  have hstable : (prefixWord ++ tailWord_3625169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3625169).length < 2 ^ (prefixWord ++ tailWord_3625169).sum := by decide
  have hdescent : baseEnd_3625169 < baseStart_3625169 := by decide
  rcases family_descends (prefixWord ++ tailWord_3625169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3625220 : List Nat := [2, 3, 2, 2, 4, 1, 1, 2, 6]
def baseStart_3625220 : Nat := 118140960795 + 3625220 * 2 ^ 59
def prefixEnd_3625220 : Nat := 4983230072969 + 3 ^ 40 * 3625220 * 2
def baseEnd_3625220 : Nat := 206831148699156838197547

theorem tailTrace_3625220 : CollatzResearch.WordTrace tailWord_3625220 prefixEnd_3625220 206831148699156838197547 := by
  unfold tailWord_3625220
  simp only [CollatzResearch.WordTrace]
  refine ⟨66111317963227276564496557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88148423950969702085995409 66111317963227276564496557)
  ·
    refine ⟨24791744236210228711686209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66111317963227276564496557 24791744236210228711686209)
    ·
      refine ⟨18593808177157671533764657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24791744236210228711686209 18593808177157671533764657)
      ·
        refine ⟨13945356132868253650323493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18593808177157671533764657 13945356132868253650323493)
        ·
          refine ⟨2614754274912797559435655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13945356132868253650323493 2614754274912797559435655)
          ·
            refine ⟨3922131412369196339153483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2614754274912797559435655 3922131412369196339153483)
            ·
              refine ⟨5883197118553794508730225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3922131412369196339153483 5883197118553794508730225)
              ·
                refine ⟨4412397838915345881547669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5883197118553794508730225 4412397838915345881547669)
                ·
                  refine ⟨206831148699156838197547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4412397838915345881547669 206831148699156838197547)
                  ·
                    rfl

theorem cell23_3625220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 4, 1, 1, 2, 6].length) (baseStart_3625220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3625220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3625220 prefixEnd_3625220 := by exact prefixLift 3625220
  have htrace : WordTrace (prefixWord ++ tailWord_3625220) baseStart_3625220 baseEnd_3625220 := by
    simpa [prefixWord, tailWord_3625220, baseEnd_3625220] using wordTrace_append hprefix tailTrace_3625220
  have hstable : (prefixWord ++ tailWord_3625220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3625220).length < 2 ^ (prefixWord ++ tailWord_3625220).sum := by decide
  have hdescent : baseEnd_3625220 < baseStart_3625220 := by decide
  rcases family_descends (prefixWord ++ tailWord_3625220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3625230 : List Nat := [4, 1, 1, 2, 1, 2, 1, 6, 1, 1, 3]
def baseStart_3625230 : Nat := 118140960795 + 3625230 * 2 ^ 59
def prefixEnd_3625230 : Nat := 4983230072969 + 3 ^ 40 * 3625230 * 2
def baseEnd_3625230 : Nat := 1861485473098956504652877

theorem tailTrace_3625230 : CollatzResearch.WordTrace tailWord_3625230 prefixEnd_3625230 1861485473098956504652877 := by
  unfold tailWord_3625230
  simp only [CollatzResearch.WordTrace]
  refine ⟨16527875082052290604607143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 88148667104278883224571429 16527875082052290604607143)
  ·
    refine ⟨24791812623078435906910715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16527875082052290604607143 24791812623078435906910715)
    ·
      refine ⟨37187718934617653860366073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24791812623078435906910715 37187718934617653860366073)
      ·
        refine ⟨27890789200963240395274555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37187718934617653860366073 27890789200963240395274555)
        ·
          refine ⟨41836183801444860592911833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27890789200963240395274555 41836183801444860592911833)
          ·
            refine ⟨31377137851083645444683875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41836183801444860592911833 31377137851083645444683875)
            ·
              refine ⟨47065706776625468167025813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31377137851083645444683875 47065706776625468167025813)
              ·
                refine ⟨2206205005154318820329335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 47065706776625468167025813 2206205005154318820329335)
                ·
                  refine ⟨3309307507731478230494003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2206205005154318820329335 3309307507731478230494003)
                  ·
                    refine ⟨4963961261597217345741005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3309307507731478230494003 4963961261597217345741005)
                    ·
                      refine ⟨1861485473098956504652877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4963961261597217345741005 1861485473098956504652877)
                      ·
                        rfl

theorem cell23_3625230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 6, 1, 1, 3].length) (baseStart_3625230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3625230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3625230 prefixEnd_3625230 := by exact prefixLift 3625230
  have htrace : WordTrace (prefixWord ++ tailWord_3625230) baseStart_3625230 baseEnd_3625230 := by
    simpa [prefixWord, tailWord_3625230, baseEnd_3625230] using wordTrace_append hprefix tailTrace_3625230
  have hstable : (prefixWord ++ tailWord_3625230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3625230).length < 2 ^ (prefixWord ++ tailWord_3625230).sum := by decide
  have hdescent : baseEnd_3625230 < baseStart_3625230 := by decide
  rcases family_descends (prefixWord ++ tailWord_3625230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3625273 : List Nat := [1, 2, 1, 6, 1, 2, 2, 1, 1, 1, 5]
def baseStart_3625273 : Nat := 118140960795 + 3625273 * 2 ^ 59
def prefixEnd_3625273 : Nat := 4983230072969 + 3 ^ 40 * 3625273 * 2
def baseEnd_3625273 : Nat := 1861507552767099836415179

theorem tailTrace_3625273 : CollatzResearch.WordTrace tailWord_3625273 prefixEnd_3625273 1861507552767099836415179 := by
  unfold tailWord_3625273
  simp only [CollatzResearch.WordTrace]
  refine ⟨132224568995262543180672473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88149712663508362120448315 132224568995262543180672473)
  ·
    refine ⟨99168426746446907385504355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132224568995262543180672473 99168426746446907385504355)
    ·
      refine ⟨148752640119670361078256533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99168426746446907385504355 148752640119670361078256533)
      ·
        refine ⟨6972780005609548175543275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 148752640119670361078256533 6972780005609548175543275)
        ·
          refine ⟨10459170008414322263314913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6972780005609548175543275 10459170008414322263314913)
          ·
            refine ⟨7844377506310741697486185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10459170008414322263314913 7844377506310741697486185)
            ·
              refine ⟨5883283129733056273114639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7844377506310741697486185 5883283129733056273114639)
              ·
                refine ⟨8824924694599584409671959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5883283129733056273114639 8824924694599584409671959)
                ·
                  refine ⟨13237387041899376614507939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8824924694599584409671959 13237387041899376614507939)
                  ·
                    refine ⟨19856080562849064921761909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13237387041899376614507939 19856080562849064921761909)
                    ·
                      refine ⟨1861507552767099836415179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19856080562849064921761909 1861507552767099836415179)
                      ·
                        rfl

theorem cell23_3625273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 2, 1, 1, 1, 5].length) (baseStart_3625273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3625273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3625273 prefixEnd_3625273 := by exact prefixLift 3625273
  have htrace : WordTrace (prefixWord ++ tailWord_3625273) baseStart_3625273 baseEnd_3625273 := by
    simpa [prefixWord, tailWord_3625273, baseEnd_3625273] using wordTrace_append hprefix tailTrace_3625273
  have hstable : (prefixWord ++ tailWord_3625273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3625273).length < 2 ^ (prefixWord ++ tailWord_3625273).sum := by decide
  have hdescent : baseEnd_3625273 < baseStart_3625273 := by decide
  rcases family_descends (prefixWord ++ tailWord_3625273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3625289 : List Nat := [1, 2, 1, 1, 2, 3, 1, 3, 2, 7]
def baseStart_3625289 : Nat := 118140960795 + 3625289 * 2 ^ 59
def prefixEnd_3625289 : Nat := 4983230072969 + 3 ^ 40 * 3625289 * 2
def baseEnd_3625289 : Nat := 620505256152523924605035

theorem tailTrace_3625289 : CollatzResearch.WordTrace tailWord_3625289 prefixEnd_3625289 620505256152523924605035 := by
  unfold tailWord_3625289
  simp only [CollatzResearch.WordTrace]
  refine ⟨132225152563204577913254921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88150101708803051942169947 132225152563204577913254921)
  ·
    refine ⟨99168864422403433434941191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132225152563204577913254921 99168864422403433434941191)
    ·
      refine ⟨148753296633605150152411787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99168864422403433434941191 148753296633605150152411787)
      ·
        refine ⟨223129944950407725228617681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148753296633605150152411787 223129944950407725228617681)
        ·
          refine ⟨167347458712805793921463261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 223129944950407725228617681 167347458712805793921463261)
          ·
            refine ⟨62755297017302172720548723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 167347458712805793921463261 62755297017302172720548723)
            ·
              refine ⟨94132945525953259080823085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62755297017302172720548723 94132945525953259080823085)
              ·
                refine ⟨35299854572232472155308657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 94132945525953259080823085 35299854572232472155308657)
                ·
                  refine ⟨26474890929174354116481493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35299854572232472155308657 26474890929174354116481493)
                  ·
                    refine ⟨620505256152523924605035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 26474890929174354116481493 620505256152523924605035)
                    ·
                      rfl

theorem cell23_3625289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 3, 2, 7].length) (baseStart_3625289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3625289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3625289 prefixEnd_3625289 := by exact prefixLift 3625289
  have htrace : WordTrace (prefixWord ++ tailWord_3625289) baseStart_3625289 baseEnd_3625289 := by
    simpa [prefixWord, tailWord_3625289, baseEnd_3625289] using wordTrace_append hprefix tailTrace_3625289
  have hstable : (prefixWord ++ tailWord_3625289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3625289).length < 2 ^ (prefixWord ++ tailWord_3625289).sum := by decide
  have hdescent : baseEnd_3625289 < baseStart_3625289 := by decide
  rcases family_descends (prefixWord ++ tailWord_3625289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3625299 : List Nat := [1, 1, 1, 2, 1, 1, 4, 2, 1, 4, 5]
def baseStart_3625299 : Nat := 118140960795 + 3625299 * 2 ^ 59
def prefixEnd_3625299 : Nat := 4983230072969 + 3 ^ 40 * 3625299 * 2
def baseEnd_3625299 : Nat := 1861520903264116734690059

theorem tailTrace_3625299 : CollatzResearch.WordTrace tailWord_3625299 prefixEnd_3625299 1861520903264116734690059 := by
  unfold tailWord_3625299
  simp only [CollatzResearch.WordTrace]
  refine ⟨132225517293168349621118951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88150344862112233080745967 132225517293168349621118951)
  ·
    refine ⟨198338275939752524431678427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132225517293168349621118951 198338275939752524431678427)
    ·
      refine ⟨297507413909628786647517641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198338275939752524431678427 297507413909628786647517641)
      ·
        refine ⟨223130560432221589985638231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 297507413909628786647517641 223130560432221589985638231)
        ·
          refine ⟨334695840648332384978457347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 223130560432221589985638231 334695840648332384978457347)
          ·
            refine ⟨502043760972498577467686021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 334695840648332384978457347 502043760972498577467686021)
            ·
              refine ⟨94133205182343483275191129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 502043760972498577467686021 94133205182343483275191129)
              ·
                refine ⟨70599903886757612456393347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 94133205182343483275191129 70599903886757612456393347)
                ·
                  refine ⟨105899855830136418684590021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 70599903886757612456393347 105899855830136418684590021)
                  ·
                    refine ⟨19856222968150578503360629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 105899855830136418684590021 19856222968150578503360629)
                    ·
                      refine ⟨1861520903264116734690059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19856222968150578503360629 1861520903264116734690059)
                      ·
                        rfl

theorem cell23_3625299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 2, 1, 4, 5].length) (baseStart_3625299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3625299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3625299 prefixEnd_3625299 := by exact prefixLift 3625299
  have htrace : WordTrace (prefixWord ++ tailWord_3625299) baseStart_3625299 baseEnd_3625299 := by
    simpa [prefixWord, tailWord_3625299, baseEnd_3625299] using wordTrace_append hprefix tailTrace_3625299
  have hstable : (prefixWord ++ tailWord_3625299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3625299).length < 2 ^ (prefixWord ++ tailWord_3625299).sum := by decide
  have hdescent : baseEnd_3625299 < baseStart_3625299 := by decide
  rcases family_descends (prefixWord ++ tailWord_3625299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3625356 : List Nat := [2, 2, 1, 2, 1, 4, 1, 1, 1, 4, 4]
def baseStart_3625356 : Nat := 118140960795 + 3625356 * 2 ^ 59
def prefixEnd_3625356 : Nat := 4983230072969 + 3 ^ 40 * 3625356 * 2
def baseEnd_3625356 : Nat := 1861550171661423011677297

theorem tailTrace_3625356 : CollatzResearch.WordTrace tailWord_3625356 prefixEnd_3625356 1861550171661423011677297 := by
  unfold tailWord_3625356
  simp only [CollatzResearch.WordTrace]
  refine ⟨66113798126980924177971961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88151730835974565570629281 66113798126980924177971961)
  ·
    refine ⟨49585348595235693133478971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66113798126980924177971961 49585348595235693133478971)
    ·
      refine ⟨74378022892853539700218457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49585348595235693133478971 74378022892853539700218457)
      ·
        refine ⟨55783517169640154775163843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74378022892853539700218457 55783517169640154775163843)
        ·
          refine ⟨83675275754460232162745765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55783517169640154775163843 83675275754460232162745765)
          ·
            refine ⟨15689114203961293530514831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 83675275754460232162745765 15689114203961293530514831)
            ·
              refine ⟨23533671305941940295772247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15689114203961293530514831 23533671305941940295772247)
              ·
                refine ⟨35300506958912910443658371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23533671305941940295772247 35300506958912910443658371)
                ·
                  refine ⟨52950760438369365665487557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35300506958912910443658371 52950760438369365665487557)
                  ·
                    refine ⟨9928267582194256062278917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 52950760438369365665487557 9928267582194256062278917)
                    ·
                      refine ⟨1861550171661423011677297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9928267582194256062278917 1861550171661423011677297)
                      ·
                        rfl

theorem cell23_3625356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 1, 1, 1, 4, 4].length) (baseStart_3625356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3625356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3625356 prefixEnd_3625356 := by exact prefixLift 3625356
  have htrace : WordTrace (prefixWord ++ tailWord_3625356) baseStart_3625356 baseEnd_3625356 := by
    simpa [prefixWord, tailWord_3625356, baseEnd_3625356] using wordTrace_append hprefix tailTrace_3625356
  have hstable : (prefixWord ++ tailWord_3625356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3625356).length < 2 ^ (prefixWord ++ tailWord_3625356).sum := by decide
  have hdescent : baseEnd_3625356 < baseStart_3625356 := by decide
  rcases family_descends (prefixWord ++ tailWord_3625356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3625393 : List Nat := [1, 2, 2, 4, 1, 2, 1, 2, 2, 3, 3]
def baseStart_3625393 : Nat := 118140960795 + 3625393 * 2 ^ 59
def prefixEnd_3625393 : Nat := 4983230072969 + 3 ^ 40 * 3625393 * 2
def baseEnd_3625393 : Nat := 1861569170445639366914627

theorem tailTrace_3625393 : CollatzResearch.WordTrace tailWord_3625393 prefixEnd_3625393 1861569170445639366914627 := by
  unfold tailWord_3625393
  simp only [CollatzResearch.WordTrace]
  refine ⟨132228945754827803675040833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88152630503218535783360555 132228945754827803675040833)
  ·
    refine ⟨99171709316120852756280625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132228945754827803675040833 99171709316120852756280625)
    ·
      refine ⟨74378781987090639567210469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99171709316120852756280625 74378781987090639567210469)
      ·
        refine ⟨13946021622579494918851963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 74378781987090639567210469 13946021622579494918851963)
        ·
          refine ⟨20919032433869242378277945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13946021622579494918851963 20919032433869242378277945)
          ·
            refine ⟨15689274325401931783708459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20919032433869242378277945 15689274325401931783708459)
            ·
              refine ⟨23533911488102897675562689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15689274325401931783708459 23533911488102897675562689)
              ·
                refine ⟨17650433616077173256672017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23533911488102897675562689 17650433616077173256672017)
                ·
                  refine ⟨13237825212057879942504013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17650433616077173256672017 13237825212057879942504013)
                  ·
                    refine ⟨4964184454521704978439005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13237825212057879942504013 4964184454521704978439005)
                    ·
                      refine ⟨1861569170445639366914627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4964184454521704978439005 1861569170445639366914627)
                      ·
                        rfl

theorem cell23_3625393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 1, 2, 2, 3, 3].length) (baseStart_3625393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3625393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3625393 prefixEnd_3625393 := by exact prefixLift 3625393
  have htrace : WordTrace (prefixWord ++ tailWord_3625393) baseStart_3625393 baseEnd_3625393 := by
    simpa [prefixWord, tailWord_3625393, baseEnd_3625393] using wordTrace_append hprefix tailTrace_3625393
  have hstable : (prefixWord ++ tailWord_3625393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3625393).length < 2 ^ (prefixWord ++ tailWord_3625393).sum := by decide
  have hdescent : baseEnd_3625393 < baseStart_3625393 := by decide
  rcases family_descends (prefixWord ++ tailWord_3625393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
