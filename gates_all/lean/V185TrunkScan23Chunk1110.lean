import V185TrunkScan23Chunk1109

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_6573815 : List Nat := [1, 1, 3, 1, 1, 1, 6, 2, 3, 4]
def baseStart_6573815 : Nat := 118140960795 + 6573815 * 2 ^ 59
def prefixEnd_6573815 : Nat := 4983230072969 + 3 ^ 40 * 6573815 * 2
def baseEnd_6573815 : Nat := 1125175609578767550760027

theorem tailTrace_6573815 : CollatzResearch.WordTrace tailWord_6573815 prefixEnd_6573815 1125175609578767550760027 := by
  unfold tailWord_6573815
  simp only [CollatzResearch.WordTrace]
  refine ⟨239766730679198448062946899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159844487119465632041964599 239766730679198448062946899)
  ·
    refine ⟨359650096018797672094420349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 239766730679198448062946899 359650096018797672094420349)
    ·
      refine ⟨134868786007049127035407631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 359650096018797672094420349 134868786007049127035407631)
      ·
        refine ⟨202303179010573690553111447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134868786007049127035407631 202303179010573690553111447)
        ·
          refine ⟨303454768515860535829667171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 202303179010573690553111447 303454768515860535829667171)
          ·
            refine ⟨455182152773790803744500757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 303454768515860535829667171 455182152773790803744500757)
            ·
              refine ⟨21336663411271443925523473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 455182152773790803744500757 21336663411271443925523473)
              ·
                refine ⟨16002497558453582944142605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21336663411271443925523473 16002497558453582944142605)
                ·
                  refine ⟨6000936584420093604053477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16002497558453582944142605 6000936584420093604053477)
                  ·
                    refine ⟨1125175609578767550760027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6000936584420093604053477 1125175609578767550760027)
                    ·
                      rfl

theorem cell23_6573815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 6, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 6, 2, 3, 4].length) (baseStart_6573815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6573815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6573815 prefixEnd_6573815 := by exact prefixLift 6573815
  have htrace : WordTrace (prefixWord ++ tailWord_6573815) baseStart_6573815 baseEnd_6573815 := by
    simpa [prefixWord, tailWord_6573815, baseEnd_6573815] using wordTrace_append hprefix tailTrace_6573815
  have hstable : (prefixWord ++ tailWord_6573815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6573815).length < 2 ^ (prefixWord ++ tailWord_6573815).sum := by decide
  have hdescent : baseEnd_6573815 < baseStart_6573815 := by decide
  rcases family_descends (prefixWord ++ tailWord_6573815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6573818 : List Nat := [3, 1, 1, 1, 1, 3, 1, 1, 1, 6, 4]
def baseStart_6573818 : Nat := 118140960795 + 6573818 * 2 ^ 59
def prefixEnd_6573818 : Nat := 4983230072969 + 3 ^ 40 * 6573818 * 2
def baseEnd_6573818 : Nat := 3375528369178266140542567

theorem tailTrace_6573818 : CollatzResearch.WordTrace tailWord_6573818 prefixEnd_6573818 3375528369178266140542567 := by
  unfold tailWord_6573818
  simp only [CollatzResearch.WordTrace]
  refine ⟨59941710024546894893826527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 159844560065458386383537405 59941710024546894893826527)
  ·
    refine ⟨89912565036820342340739791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59941710024546894893826527 89912565036820342340739791)
    ·
      refine ⟨134868847555230513511109687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89912565036820342340739791 134868847555230513511109687)
      ·
        refine ⟨202303271332845770266664531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134868847555230513511109687 202303271332845770266664531)
        ·
          refine ⟨303454906999268655399996797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 202303271332845770266664531 303454906999268655399996797)
          ·
            refine ⟨113795590124725745774998799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 303454906999268655399996797 113795590124725745774998799)
            ·
              refine ⟨170693385187088618662498199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 113795590124725745774998799 170693385187088618662498199)
              ·
                refine ⟨256040077780632927993747299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 170693385187088618662498199 256040077780632927993747299)
                ·
                  refine ⟨384060116670949391990620949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 256040077780632927993747299 384060116670949391990620949)
                  ·
                    refine ⟨18002817968950752749560357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 384060116670949391990620949 18002817968950752749560357)
                    ·
                      refine ⟨3375528369178266140542567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18002817968950752749560357 3375528369178266140542567)
                      ·
                        rfl

theorem cell23_6573818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 1, 1, 6, 4].length) (baseStart_6573818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6573818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6573818 prefixEnd_6573818 := by exact prefixLift 6573818
  have htrace : WordTrace (prefixWord ++ tailWord_6573818) baseStart_6573818 baseEnd_6573818 := by
    simpa [prefixWord, tailWord_6573818, baseEnd_6573818] using wordTrace_append hprefix tailTrace_6573818
  have hstable : (prefixWord ++ tailWord_6573818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6573818).length < 2 ^ (prefixWord ++ tailWord_6573818).sum := by decide
  have hdescent : baseEnd_6573818 < baseStart_6573818 := by decide
  rcases family_descends (prefixWord ++ tailWord_6573818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6573825 : List Nat := [1, 2, 4, 1, 1, 1, 4, 1, 1, 4, 3]
def baseStart_6573825 : Nat := 118140960795 + 6573825 * 2 ^ 59
def prefixEnd_6573825 : Nat := 4983230072969 + 3 ^ 40 * 6573825 * 2
def baseEnd_6573825 : Nat := 3375531963542847613155035

theorem tailTrace_6573825 : CollatzResearch.WordTrace tailWord_6573825 prefixEnd_6573825 3375531963542847613155035 := by
  unfold tailWord_6573825
  simp only [CollatzResearch.WordTrace]
  refine ⟨239767095409162219770810929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159844730272774813180540619 239767095409162219770810929)
  ·
    refine ⟨179825321556871664828108197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 239767095409162219770810929 179825321556871664828108197)
    ·
      refine ⟨33717247791913437155270287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 179825321556871664828108197 33717247791913437155270287)
      ·
        refine ⟨50575871687870155732905431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33717247791913437155270287 50575871687870155732905431)
        ·
          refine ⟨75863807531805233599358147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50575871687870155732905431 75863807531805233599358147)
          ·
            refine ⟨113795711297707850399037221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75863807531805233599358147 113795711297707850399037221)
            ·
              refine ⟨21336695868320221949819479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 113795711297707850399037221 21336695868320221949819479)
              ·
                refine ⟨32005043802480332924729219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21336695868320221949819479 32005043802480332924729219)
                ·
                  refine ⟨48007565703720499387093829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32005043802480332924729219 48007565703720499387093829)
                  ·
                    refine ⟨9001418569447593635080093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 48007565703720499387093829 9001418569447593635080093)
                    ·
                      refine ⟨3375531963542847613155035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9001418569447593635080093 3375531963542847613155035)
                      ·
                        rfl

theorem cell23_6573825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 4, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 4, 1, 1, 4, 3].length) (baseStart_6573825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6573825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6573825 prefixEnd_6573825 := by exact prefixLift 6573825
  have htrace : WordTrace (prefixWord ++ tailWord_6573825) baseStart_6573825 baseEnd_6573825 := by
    simpa [prefixWord, tailWord_6573825, baseEnd_6573825] using wordTrace_append hprefix tailTrace_6573825
  have hstable : (prefixWord ++ tailWord_6573825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6573825).length < 2 ^ (prefixWord ++ tailWord_6573825).sum := by decide
  have hdescent : baseEnd_6573825 < baseStart_6573825 := by decide
  rcases family_descends (prefixWord ++ tailWord_6573825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6573848 : List Nat := [2, 1, 2, 3, 1, 1, 2, 1, 1, 1, 8]
def baseStart_6573848 : Nat := 118140960795 + 6573848 * 2 ^ 59
def prefixEnd_6573848 : Nat := 4983230072969 + 3 ^ 40 * 6573848 * 2
def baseEnd_6573848 : Nat := 3375543773597901023167429

theorem tailTrace_6573848 : CollatzResearch.WordTrace tailWord_6573848 prefixEnd_6573848 3375543773597901023167429 := by
  unfold tailWord_6573848
  simp only [CollatzResearch.WordTrace]
  refine ⟨119883967144039447349449099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159845289525385929799265465 119883967144039447349449099)
  ·
    refine ⟨179825950716059171024173649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119883967144039447349449099 179825950716059171024173649)
    ·
      refine ⟨134869463037044378268130237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 179825950716059171024173649 134869463037044378268130237)
      ·
        refine ⟨50576048638891641850548839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 134869463037044378268130237 50576048638891641850548839)
        ·
          refine ⟨75864072958337462775823259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50576048638891641850548839 75864072958337462775823259)
          ·
            refine ⟨113796109437506194163734889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75864072958337462775823259 113796109437506194163734889)
            ·
              refine ⟨85347082078129645622801167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 113796109437506194163734889 85347082078129645622801167)
              ·
                refine ⟨128020623117194468434201751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 85347082078129645622801167 128020623117194468434201751)
                ·
                  refine ⟨192030934675791702651302627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 128020623117194468434201751 192030934675791702651302627)
                  ·
                    refine ⟨288046402013687553976953941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 192030934675791702651302627 288046402013687553976953941)
                    ·
                      refine ⟨3375543773597901023167429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 288046402013687553976953941 3375543773597901023167429)
                      ·
                        rfl

theorem cell23_6573848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 1, 1, 1, 8].length) (baseStart_6573848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6573848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6573848 prefixEnd_6573848 := by exact prefixLift 6573848
  have htrace : WordTrace (prefixWord ++ tailWord_6573848) baseStart_6573848 baseEnd_6573848 := by
    simpa [prefixWord, tailWord_6573848, baseEnd_6573848] using wordTrace_append hprefix tailTrace_6573848
  have hstable : (prefixWord ++ tailWord_6573848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6573848).length < 2 ^ (prefixWord ++ tailWord_6573848).sum := by decide
  have hdescent : baseEnd_6573848 < baseStart_6573848 := by decide
  rcases family_descends (prefixWord ++ tailWord_6573848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6573906 : List Nat := [3, 2, 2, 1, 1, 4, 1, 4, 1, 1, 3]
def baseStart_6573906 : Nat := 118140960795 + 6573906 * 2 ^ 59
def prefixEnd_6573906 : Nat := 4983230072969 + 3 ^ 40 * 6573906 * 2
def baseEnd_6573906 : Nat := 3375573555475861796242163

theorem tailTrace_6573906 : CollatzResearch.WordTrace tailWord_6573906 prefixEnd_6573906 3375573555475861796242163 := by
  unfold tailWord_6573906
  simp only [CollatzResearch.WordTrace]
  refine ⟨59942512430467192651127393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 159846699814579180403006381 59942512430467192651127393)
  ·
    refine ⟨44956884322850394488345545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59942512430467192651127393 44956884322850394488345545)
    ·
      refine ⟨33717663242137795866259159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44956884322850394488345545 33717663242137795866259159)
      ·
        refine ⟨50576494863206693799388739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33717663242137795866259159 50576494863206693799388739)
        ·
          refine ⟨75864742294810040699083109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50576494863206693799388739 75864742294810040699083109)
          ·
            refine ⟨14224639180276882631078083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 75864742294810040699083109 14224639180276882631078083)
            ·
              refine ⟨21336958770415323946617125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14224639180276882631078083 21336958770415323946617125)
              ·
                refine ⟨4000679769452873239990711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21336958770415323946617125 4000679769452873239990711)
                ·
                  refine ⟨6001019654179309859986067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4000679769452873239990711 6001019654179309859986067)
                  ·
                    refine ⟨9001529481268964789979101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6001019654179309859986067 9001529481268964789979101)
                    ·
                      refine ⟨3375573555475861796242163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9001529481268964789979101 3375573555475861796242163)
                      ·
                        rfl

theorem cell23_6573906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 1, 4, 1, 1, 3].length) (baseStart_6573906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6573906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6573906 prefixEnd_6573906 := by exact prefixLift 6573906
  have htrace : WordTrace (prefixWord ++ tailWord_6573906) baseStart_6573906 baseEnd_6573906 := by
    simpa [prefixWord, tailWord_6573906, baseEnd_6573906] using wordTrace_append hprefix tailTrace_6573906
  have hstable : (prefixWord ++ tailWord_6573906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6573906).length < 2 ^ (prefixWord ++ tailWord_6573906).sum := by decide
  have hdescent : baseEnd_6573906 < baseStart_6573906 := by decide
  rcases family_descends (prefixWord ++ tailWord_6573906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6573922 : List Nat := [3, 3, 2, 1, 2, 1, 1, 3, 1, 6]
def baseStart_6573922 : Nat := 118140960795 + 6573922 * 2 ^ 59
def prefixEnd_6573922 : Nat := 4983230072969 + 3 ^ 40 * 6573922 * 2
def baseEnd_6573922 : Nat := 1125193923722111244547363

theorem tailTrace_6573922 : CollatzResearch.WordTrace tailWord_6573922 prefixEnd_6573922 1125193923722111244547363 := by
  unfold tailWord_6573922
  simp only [CollatzResearch.WordTrace]
  refine ⟨59942658322452701334273005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 159847088859873870224728013 59942658322452701334273005)
  ·
    refine ⟨22478496870919763000352377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59942658322452701334273005 22478496870919763000352377)
    ·
      refine ⟨16858872653189822250264283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22478496870919763000352377 16858872653189822250264283)
      ·
        refine ⟨25288308979784733375396425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16858872653189822250264283 25288308979784733375396425)
        ·
          refine ⟨18966231734838550031547319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25288308979784733375396425 18966231734838550031547319)
          ·
            refine ⟨28449347602257825047320979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18966231734838550031547319 28449347602257825047320979)
            ·
              refine ⟨42674021403386737570981469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28449347602257825047320979 42674021403386737570981469)
              ·
                refine ⟨16002758026270026589118051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42674021403386737570981469 16002758026270026589118051)
                ·
                  refine ⟨24004137039405039883677077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16002758026270026589118051 24004137039405039883677077)
                  ·
                    refine ⟨1125193923722111244547363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24004137039405039883677077 1125193923722111244547363)
                    ·
                      rfl

theorem cell23_6573922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 1, 3, 1, 6].length) (baseStart_6573922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6573922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6573922 prefixEnd_6573922 := by exact prefixLift 6573922
  have htrace : WordTrace (prefixWord ++ tailWord_6573922) baseStart_6573922 baseEnd_6573922 := by
    simpa [prefixWord, tailWord_6573922, baseEnd_6573922] using wordTrace_append hprefix tailTrace_6573922
  have hstable : (prefixWord ++ tailWord_6573922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6573922).length < 2 ^ (prefixWord ++ tailWord_6573922).sum := by decide
  have hdescent : baseEnd_6573922 < baseStart_6573922 := by decide
  rcases family_descends (prefixWord ++ tailWord_6573922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6573932 : List Nat := [2, 2, 1, 1, 4, 2, 2, 1, 3, 2, 3]
def baseStart_6573932 : Nat := 118140960795 + 6573932 * 2 ^ 59
def prefixEnd_6573932 : Nat := 4983230072969 + 3 ^ 40 * 6573932 * 2
def baseEnd_6573932 : Nat := 3375586905972878694517043

theorem tailTrace_6573932 : CollatzResearch.WordTrace tailWord_6573932 prefixEnd_6573932 3375586905972878694517043 := by
  unfold tailWord_6573932
  simp only [CollatzResearch.WordTrace]
  refine ⟨119885499009887288522478025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159847332013183051363304033 119885499009887288522478025)
  ·
    refine ⟨89914124257415466391858519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119885499009887288522478025 89914124257415466391858519)
    ·
      refine ⟨134871186386123199587787779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89914124257415466391858519 134871186386123199587787779)
      ·
        refine ⟨202306779579184799381681669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134871186386123199587787779 202306779579184799381681669)
        ·
          refine ⟨37932521171097149884065313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 202306779579184799381681669 37932521171097149884065313)
          ·
            refine ⟨28449390878322862413048985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37932521171097149884065313 28449390878322862413048985)
            ·
              refine ⟨21337043158742146809786739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28449390878322862413048985 21337043158742146809786739)
              ·
                refine ⟨32005564738113220214680109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21337043158742146809786739 32005564738113220214680109)
                ·
                  refine ⟨12002086776792457580505041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32005564738113220214680109 12002086776792457580505041)
                  ·
                    refine ⟨9001565082594343185378781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12002086776792457580505041 9001565082594343185378781)
                    ·
                      refine ⟨3375586905972878694517043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9001565082594343185378781 3375586905972878694517043)
                      ·
                        rfl

theorem cell23_6573932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 2, 3].length) (baseStart_6573932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6573932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6573932 prefixEnd_6573932 := by exact prefixLift 6573932
  have htrace : WordTrace (prefixWord ++ tailWord_6573932) baseStart_6573932 baseEnd_6573932 := by
    simpa [prefixWord, tailWord_6573932, baseEnd_6573932] using wordTrace_append hprefix tailTrace_6573932
  have hstable : (prefixWord ++ tailWord_6573932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6573932).length < 2 ^ (prefixWord ++ tailWord_6573932).sum := by decide
  have hdescent : baseEnd_6573932 < baseStart_6573932 := by decide
  rcases family_descends (prefixWord ++ tailWord_6573932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6573946 : List Nat := [3, 1, 1, 1, 1, 1, 5, 5, 1, 2, 2]
def baseStart_6573946 : Nat := 118140960795 + 6573946 * 2 ^ 59
def prefixEnd_6573946 : Nat := 4983230072969 + 3 ^ 40 * 6573946 * 2
def baseEnd_6573946 : Nat := 3375594094702041639741979

theorem tailTrace_6573946 : CollatzResearch.WordTrace tailWord_6573946 prefixEnd_6573946 3375594094702041639741979 := by
  unfold tailWord_6573946
  simp only [CollatzResearch.WordTrace]
  refine ⟨59942877160430964358991423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 159847672427815904957310461 59942877160430964358991423)
  ·
    refine ⟨89914315740646446538487135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59942877160430964358991423 89914315740646446538487135)
    ·
      refine ⟨134871473610969669807730703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89914315740646446538487135 134871473610969669807730703)
      ·
        refine ⟨202307210416454504711596055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134871473610969669807730703 202307210416454504711596055)
        ·
          refine ⟨303460815624681757067394083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 202307210416454504711596055 303460815624681757067394083)
          ·
            refine ⟨455191223437022635601091125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 303460815624681757067394083 455191223437022635601091125)
            ·
              refine ⟨42674177197220872087602293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 455191223437022635601091125 42674177197220872087602293)
              ·
                refine ⟨4000704112239456758212715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 42674177197220872087602293 4000704112239456758212715)
                ·
                  refine ⟨6001056168359185137319073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4000704112239456758212715 6001056168359185137319073)
                  ·
                    refine ⟨4500792126269388852989305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6001056168359185137319073 4500792126269388852989305)
                    ·
                      refine ⟨3375594094702041639741979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4500792126269388852989305 3375594094702041639741979)
                      ·
                        rfl

theorem cell23_6573946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 5, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 5, 5, 1, 2, 2].length) (baseStart_6573946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6573946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6573946 prefixEnd_6573946 := by exact prefixLift 6573946
  have htrace : WordTrace (prefixWord ++ tailWord_6573946) baseStart_6573946 baseEnd_6573946 := by
    simpa [prefixWord, tailWord_6573946, baseEnd_6573946] using wordTrace_append hprefix tailTrace_6573946
  have hstable : (prefixWord ++ tailWord_6573946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6573946).length < 2 ^ (prefixWord ++ tailWord_6573946).sum := by decide
  have hdescent : baseEnd_6573946 < baseStart_6573946 := by decide
  rcases family_descends (prefixWord ++ tailWord_6573946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6573976 : List Nat := [2, 1, 2, 6, 1, 2, 1, 1, 1, 2, 4]
def baseStart_6573976 : Nat := 118140960795 + 6573976 * 2 ^ 59
def prefixEnd_6573976 : Nat := 4983230072969 + 3 ^ 40 * 6573976 * 2
def baseEnd_6573976 : Nat := 3375609499121676522366841

theorem tailTrace_6573976 : CollatzResearch.WordTrace tailWord_6573976 prefixEnd_6573976 3375609499121676522366841 := by
  unfold tailWord_6573976
  simp only [CollatzResearch.WordTrace]
  refine ⟨119886301415807586279778891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159848401887743448373038521 119886301415807586279778891)
  ·
    refine ⟨179829452123711379419668337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119886301415807586279778891 179829452123711379419668337)
    ·
      refine ⟨134872089092783534564751253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 179829452123711379419668337 134872089092783534564751253)
      ·
        refine ⟨6322129176224228182722715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 134872089092783534564751253 6322129176224228182722715)
        ·
          refine ⟨9483193764336342274084073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6322129176224228182722715 9483193764336342274084073)
          ·
            refine ⟨7112395323252256705563055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9483193764336342274084073 7112395323252256705563055)
            ·
              refine ⟨10668592984878385058344583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7112395323252256705563055 10668592984878385058344583)
              ·
                refine ⟨16002889477317577587516875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10668592984878385058344583 16002889477317577587516875)
                ·
                  refine ⟨24004334215976366381275313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16002889477317577587516875 24004334215976366381275313)
                  ·
                    refine ⟨18003250661982274785956485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24004334215976366381275313 18003250661982274785956485)
                    ·
                      refine ⟨3375609499121676522366841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18003250661982274785956485 3375609499121676522366841)
                      ·
                        rfl

theorem cell23_6573976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 2, 1, 1, 1, 2, 4].length) (baseStart_6573976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6573976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6573976 prefixEnd_6573976 := by exact prefixLift 6573976
  have htrace : WordTrace (prefixWord ++ tailWord_6573976) baseStart_6573976 baseEnd_6573976 := by
    simpa [prefixWord, tailWord_6573976, baseEnd_6573976] using wordTrace_append hprefix tailTrace_6573976
  have hstable : (prefixWord ++ tailWord_6573976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6573976).length < 2 ^ (prefixWord ++ tailWord_6573976).sum := by decide
  have hdescent : baseEnd_6573976 < baseStart_6573976 := by decide
  rcases family_descends (prefixWord ++ tailWord_6573976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6573986 : List Nat := [3, 3, 1, 2, 4, 1, 2, 7]
def baseStart_6573986 : Nat := 118140960795 + 6573986 * 2 ^ 59
def prefixEnd_6573986 : Nat := 4983230072969 + 3 ^ 40 * 6573986 * 2
def baseEnd_6573986 : Nat := 125022764219563758638585

theorem tailTrace_6573986 : CollatzResearch.WordTrace tailWord_6573986 prefixEnd_6573986 125022764219563758638585 := by
  unfold tailWord_6573986
  simp only [CollatzResearch.WordTrace]
  refine ⟨59943241890394736066855453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 159848645041052629511614541 59943241890394736066855453)
  ·
    refine ⟨22478715708898026025070795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59943241890394736066855453 22478715708898026025070795)
    ·
      refine ⟨33718073563347039037606193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22478715708898026025070795 33718073563347039037606193)
      ·
        refine ⟨25288555172510279278204645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33718073563347039037606193 25288555172510279278204645)
        ·
          refine ⟨4741604094845677364663371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25288555172510279278204645 4741604094845677364663371)
          ·
            refine ⟨7112406142268516046995057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4741604094845677364663371 7112406142268516046995057)
            ·
              refine ⟨5334304606701387035246293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7112406142268516046995057 5334304606701387035246293)
              ·
                refine ⟨125022764219563758638585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5334304606701387035246293 125022764219563758638585)
                ·
                  rfl

theorem cell23_6573986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 4, 1, 2, 7].length) (baseStart_6573986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6573986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6573986 prefixEnd_6573986 := by exact prefixLift 6573986
  have htrace : WordTrace (prefixWord ++ tailWord_6573986) baseStart_6573986 baseEnd_6573986 := by
    simpa [prefixWord, tailWord_6573986, baseEnd_6573986] using wordTrace_append hprefix tailTrace_6573986
  have hstable : (prefixWord ++ tailWord_6573986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6573986).length < 2 ^ (prefixWord ++ tailWord_6573986).sum := by decide
  have hdescent : baseEnd_6573986 < baseStart_6573986 := by decide
  rcases family_descends (prefixWord ++ tailWord_6573986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6574070 : List Nat := [5, 1, 1, 1, 4, 1, 2, 2, 2, 2, 2]
def baseStart_6574070 : Nat := 118140960795 + 6574070 * 2 ^ 59
def prefixEnd_6574070 : Nat := 4983230072969 + 3 ^ 40 * 6574070 * 2
def baseEnd_6574070 : Nat := 3375657766303199154591409

theorem tailTrace_6574070 : CollatzResearch.WordTrace tailWord_6574070 prefixEnd_6574070 3375657766303199154591409 := by
  unfold tailWord_6574070
  simp only [CollatzResearch.WordTrace]
  refine ⟨14986001955829664163342479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 159850687528849751075653109 14986001955829664163342479)
  ·
    refine ⟨22479002933744496245013719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14986001955829664163342479 22479002933744496245013719)
    ·
      refine ⟨33718504400616744367520579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22479002933744496245013719 33718504400616744367520579)
      ·
        refine ⟨50577756600925116551280869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33718504400616744367520579 50577756600925116551280869)
        ·
          refine ⟨9483329362673459353365163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 50577756600925116551280869 9483329362673459353365163)
          ·
            refine ⟨14224994044010189030047745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9483329362673459353365163 14224994044010189030047745)
            ·
              refine ⟨10668745533007641772535809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14224994044010189030047745 10668745533007641772535809)
              ·
                refine ⟨8001559149755731329401857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10668745533007641772535809 8001559149755731329401857)
                ·
                  refine ⟨6001169362316798497051393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8001559149755731329401857 6001169362316798497051393)
                  ·
                    refine ⟨4500877021737598872788545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6001169362316798497051393 4500877021737598872788545)
                    ·
                      refine ⟨3375657766303199154591409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4500877021737598872788545 3375657766303199154591409)
                      ·
                        rfl

theorem cell23_6574070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 2, 2, 2, 2, 2].length) (baseStart_6574070 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6574070 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6574070 prefixEnd_6574070 := by exact prefixLift 6574070
  have htrace : WordTrace (prefixWord ++ tailWord_6574070) baseStart_6574070 baseEnd_6574070 := by
    simpa [prefixWord, tailWord_6574070, baseEnd_6574070] using wordTrace_append hprefix tailTrace_6574070
  have hstable : (prefixWord ++ tailWord_6574070).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6574070).length < 2 ^ (prefixWord ++ tailWord_6574070).sum := by decide
  have hdescent : baseEnd_6574070 < baseStart_6574070 := by decide
  rcases family_descends (prefixWord ++ tailWord_6574070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6574072 : List Nat := [2, 1, 2, 1, 1, 3, 4, 2, 2, 5]
def baseStart_6574072 : Nat := 118140960795 + 6574072 * 2 ^ 59
def prefixEnd_6574072 : Nat := 4983230072969 + 3 ^ 40 * 6574072 * 2
def baseEnd_6574072 : Nat := 1125219597754836048922133

theorem tailTrace_6574072 : CollatzResearch.WordTrace tailWord_6574072 prefixEnd_6574072 1125219597754836048922133 := by
  unfold tailWord_6574072
  simp only [CollatzResearch.WordTrace]
  refine ⟨119888052119633690477526235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159850736159511587303368313 119888052119633690477526235)
  ·
    refine ⟨179832078179450535716289353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119888052119633690477526235 179832078179450535716289353)
    ·
      refine ⟨134874058634587901787217015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 179832078179450535716289353 134874058634587901787217015)
      ·
        refine ⟨202311087951881852680825523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134874058634587901787217015 202311087951881852680825523)
        ·
          refine ⟨303466631927822779021238285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 202311087951881852680825523 303466631927822779021238285)
          ·
            refine ⟨113799986972933542132964357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 303466631927822779021238285 113799986972933542132964357)
            ·
              refine ⟨21337497557425039149930817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 113799986972933542132964357 21337497557425039149930817)
              ·
                refine ⟨16003123168068779362448113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21337497557425039149930817 16003123168068779362448113)
                ·
                  refine ⟨12002342376051584521836085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16003123168068779362448113 12002342376051584521836085)
                  ·
                    refine ⟨1125219597754836048922133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12002342376051584521836085 1125219597754836048922133)
                    ·
                      rfl

theorem cell23_6574072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 4, 2, 2, 5].length) (baseStart_6574072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6574072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6574072 prefixEnd_6574072 := by exact prefixLift 6574072
  have htrace : WordTrace (prefixWord ++ tailWord_6574072) baseStart_6574072 baseEnd_6574072 := by
    simpa [prefixWord, tailWord_6574072, baseEnd_6574072] using wordTrace_append hprefix tailTrace_6574072
  have hstable : (prefixWord ++ tailWord_6574072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6574072).length < 2 ^ (prefixWord ++ tailWord_6574072).sum := by decide
  have hdescent : baseEnd_6574072 < baseStart_6574072 := by decide
  rcases family_descends (prefixWord ++ tailWord_6574072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6574092 : List Nat := [2, 2, 1, 2, 3, 1, 2, 2, 1, 3, 4]
def baseStart_6574092 : Nat := 118140960795 + 6574092 * 2 ^ 59
def prefixEnd_6574092 : Nat := 4983230072969 + 3 ^ 40 * 6574092 * 2
def baseEnd_6574092 : Nat := 3375669062877598068516307

theorem tailTrace_6574092 : CollatzResearch.WordTrace tailWord_6574092 prefixEnd_6574092 3375669062877598068516307 := by
  unfold tailWord_6574092
  simp only [CollatzResearch.WordTrace]
  refine ⟨119888416849597462185390265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159851222466129949580520353 119888416849597462185390265)
  ·
    refine ⟨89916312637198096639042699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119888416849597462185390265 89916312637198096639042699)
    ·
      refine ⟨134874468955797144958564049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89916312637198096639042699 134874468955797144958564049)
      ·
        refine ⟨101155851716847858718923037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 134874468955797144958564049 101155851716847858718923037)
        ·
          refine ⟨37933444393817947019596139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 101155851716847858718923037 37933444393817947019596139)
          ·
            refine ⟨56900166590726920529394209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37933444393817947019596139 56900166590726920529394209)
            ·
              refine ⟨42675124943045190397045657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56900166590726920529394209 42675124943045190397045657)
              ·
                refine ⟨32006343707283892797784243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42675124943045190397045657 32006343707283892797784243)
                ·
                  refine ⟨48009515560925839196676365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32006343707283892797784243 48009515560925839196676365)
                  ·
                    refine ⟨18003568335347189698753637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 48009515560925839196676365 18003568335347189698753637)
                    ·
                      refine ⟨3375669062877598068516307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18003568335347189698753637 3375669062877598068516307)
                      ·
                        rfl

theorem cell23_6574092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 2, 2, 1, 3, 4].length) (baseStart_6574092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6574092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6574092 prefixEnd_6574092 := by exact prefixLift 6574092
  have htrace : WordTrace (prefixWord ++ tailWord_6574092) baseStart_6574092 baseEnd_6574092 := by
    simpa [prefixWord, tailWord_6574092, baseEnd_6574092] using wordTrace_append hprefix tailTrace_6574092
  have hstable : (prefixWord ++ tailWord_6574092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6574092).length < 2 ^ (prefixWord ++ tailWord_6574092).sum := by decide
  have hdescent : baseEnd_6574092 < baseStart_6574092 := by decide
  rcases family_descends (prefixWord ++ tailWord_6574092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6574093 : List Nat := [1, 7, 1, 2, 1, 1, 1, 2, 7]
def baseStart_6574093 : Nat := 118140960795 + 6574093 * 2 ^ 59
def prefixEnd_6574093 : Nat := 4983230072969 + 3 ^ 40 * 6574093 * 2
def baseEnd_6574093 : Nat := 375074397373139173844867

theorem tailTrace_6574093 : CollatzResearch.WordTrace tailWord_6574093 prefixEnd_6574093 375074397373139173844867 := by
  unfold tailWord_6574093
  simp only [CollatzResearch.WordTrace]
  refine ⟨239776870172191301541566933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159851246781460867694377955 239776870172191301541566933)
  ·
    refine ⟨5619770394660733629880475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 239776870172191301541566933 5619770394660733629880475)
    ·
      refine ⟨8429655591991100444820713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5619770394660733629880475 8429655591991100444820713)
      ·
        refine ⟨6322241693993325333615535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8429655591991100444820713 6322241693993325333615535)
        ·
          refine ⟨9483362540989988000423303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6322241693993325333615535 9483362540989988000423303)
          ·
            refine ⟨14225043811484982000634955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9483362540989988000423303 14225043811484982000634955)
            ·
              refine ⟨21337565717227473000952433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14225043811484982000634955 21337565717227473000952433)
              ·
                refine ⟨16003174287920604750714325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21337565717227473000952433 16003174287920604750714325)
                ·
                  refine ⟨375074397373139173844867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16003174287920604750714325 375074397373139173844867)
                  ·
                    rfl

theorem cell23_6574093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 1, 2, 7].length) (baseStart_6574093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6574093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6574093 prefixEnd_6574093 := by exact prefixLift 6574093
  have htrace : WordTrace (prefixWord ++ tailWord_6574093) baseStart_6574093 baseEnd_6574093 := by
    simpa [prefixWord, tailWord_6574093, baseEnd_6574093] using wordTrace_append hprefix tailTrace_6574093
  have hstable : (prefixWord ++ tailWord_6574093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6574093).length < 2 ^ (prefixWord ++ tailWord_6574093).sum := by decide
  have hdescent : baseEnd_6574093 < baseStart_6574093 := by decide
  rcases family_descends (prefixWord ++ tailWord_6574093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6574109 : List Nat := [1, 4, 2, 2, 2, 2, 1, 1, 1, 3, 4]
def baseStart_6574109 : Nat := 118140960795 + 6574109 * 2 ^ 59
def prefixEnd_6574109 : Nat := 4983230072969 + 3 ^ 40 * 6574109 * 2
def baseEnd_6574109 : Nat := 3375677792048724502003729

theorem tailTrace_6574109 : CollatzResearch.WordTrace tailWord_6574109 prefixEnd_6574109 3375677792048724502003729 := by
  unfold tailWord_6574109
  simp only [CollatzResearch.WordTrace]
  refine ⟨239777453740133336274149381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159851635826755557516099587 239777453740133336274149381)
  ·
    refine ⟨44958272576275000551403009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 239777453740133336274149381 44958272576275000551403009)
    ·
      refine ⟨33718704432206250413552257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44958272576275000551403009 33718704432206250413552257)
      ·
        refine ⟨25289028324154687810164193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33718704432206250413552257 25289028324154687810164193)
        ·
          refine ⟨18966771243116015857623145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25289028324154687810164193 18966771243116015857623145)
          ·
            refine ⟨14225078432337011893217359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18966771243116015857623145 14225078432337011893217359)
            ·
              refine ⟨21337617648505517839826039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14225078432337011893217359 21337617648505517839826039)
              ·
                refine ⟨32006426472758276759739059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21337617648505517839826039 32006426472758276759739059)
                ·
                  refine ⟨48009639709137415139608589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32006426472758276759739059 48009639709137415139608589)
                  ·
                    refine ⟨18003614890926530677353221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 48009639709137415139608589 18003614890926530677353221)
                    ·
                      refine ⟨3375677792048724502003729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18003614890926530677353221 3375677792048724502003729)
                      ·
                        rfl

theorem cell23_6574109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 1, 1, 1, 3, 4].length) (baseStart_6574109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6574109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6574109 prefixEnd_6574109 := by exact prefixLift 6574109
  have htrace : WordTrace (prefixWord ++ tailWord_6574109) baseStart_6574109 baseEnd_6574109 := by
    simpa [prefixWord, tailWord_6574109, baseEnd_6574109] using wordTrace_append hprefix tailTrace_6574109
  have hstable : (prefixWord ++ tailWord_6574109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6574109).length < 2 ^ (prefixWord ++ tailWord_6574109).sum := by decide
  have hdescent : baseEnd_6574109 < baseStart_6574109 := by decide
  rcases family_descends (prefixWord ++ tailWord_6574109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6574126 : List Nat := [4, 1, 3, 1, 1, 2, 1, 2, 2, 4, 2]
def baseStart_6574126 : Nat := 118140960795 + 6574126 * 2 ^ 59
def prefixEnd_6574126 : Nat := 4983230072969 + 3 ^ 40 * 6574126 * 2
def baseEnd_6574126 : Nat := 3375686521219850935491151

theorem tailTrace_6574126 : CollatzResearch.WordTrace tailWord_6574126 prefixEnd_6574126 3375686521219850935491151 := by
  unfold tailWord_6574126
  simp only [CollatzResearch.WordTrace]
  refine ⟨29972259222633968522189779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 159852049187381165451678821 29972259222633968522189779)
  ·
    refine ⟨44958388833950952783284669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29972259222633968522189779 44958388833950952783284669)
    ·
      refine ⟨16859395812731607293731751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44958388833950952783284669 16859395812731607293731751)
      ·
        refine ⟨25289093719097410940597627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16859395812731607293731751 25289093719097410940597627)
        ·
          refine ⟨37933640578646116410896441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25289093719097410940597627 37933640578646116410896441)
          ·
            refine ⟨28450230433984587308172331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37933640578646116410896441 28450230433984587308172331)
            ·
              refine ⟨42675345650976880962258497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28450230433984587308172331 42675345650976880962258497)
              ·
                refine ⟨32006509238232660721693873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42675345650976880962258497 32006509238232660721693873)
                ·
                  refine ⟨24004881928674495541270405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32006509238232660721693873 24004881928674495541270405)
                  ·
                    refine ⟨4500915361626467913988201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24004881928674495541270405 4500915361626467913988201)
                    ·
                      refine ⟨3375686521219850935491151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4500915361626467913988201 3375686521219850935491151)
                      ·
                        rfl

theorem cell23_6574126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 1, 2, 2, 4, 2].length) (baseStart_6574126 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6574126 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6574126 prefixEnd_6574126 := by exact prefixLift 6574126
  have htrace : WordTrace (prefixWord ++ tailWord_6574126) baseStart_6574126 baseEnd_6574126 := by
    simpa [prefixWord, tailWord_6574126, baseEnd_6574126] using wordTrace_append hprefix tailTrace_6574126
  have hstable : (prefixWord ++ tailWord_6574126).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6574126).length < 2 ^ (prefixWord ++ tailWord_6574126).sum := by decide
  have hdescent : baseEnd_6574126 < baseStart_6574126 := by decide
  rcases family_descends (prefixWord ++ tailWord_6574126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6574136 : List Nat := [2, 1, 2, 1, 6, 1, 2, 1, 3, 4]
def baseStart_6574136 : Nat := 118140960795 + 6574136 * 2 ^ 59
def prefixEnd_6574136 : Nat := 4983230072969 + 3 ^ 40 * 6574136 * 2
def baseEnd_6574136 : Nat := 1125230552008798632122035

theorem tailTrace_6574136 : CollatzResearch.WordTrace tailWord_6574136 prefixEnd_6574136 1125230552008798632122035 := by
  unfold tailWord_6574136
  simp only [CollatzResearch.WordTrace]
  refine ⟨119889219255517759942691131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159852292340690346590254841 119889219255517759942691131)
  ·
    refine ⟨179833828883276639914036697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119889219255517759942691131 179833828883276639914036697)
    ·
      refine ⟨134875371662457479935527523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 179833828883276639914036697 134875371662457479935527523)
      ·
        refine ⟨202313057493686219903291285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134875371662457479935527523 202313057493686219903291285)
        ·
          refine ⟨9483424570016541557966779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 202313057493686219903291285 9483424570016541557966779)
          ·
            refine ⟨14225136855024812336950169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9483424570016541557966779 14225136855024812336950169)
            ·
              refine ⟨10668852641268609252712627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14225136855024812336950169 10668852641268609252712627)
              ·
                refine ⟨16003278961902913879068941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10668852641268609252712627 16003278961902913879068941)
                ·
                  refine ⟨6001229610713592704650853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16003278961902913879068941 6001229610713592704650853)
                  ·
                    refine ⟨1125230552008798632122035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6001229610713592704650853 1125230552008798632122035)
                    ·
                      rfl

theorem cell23_6574136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 2, 1, 3, 4].length) (baseStart_6574136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6574136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6574136 prefixEnd_6574136 := by exact prefixLift 6574136
  have htrace : WordTrace (prefixWord ++ tailWord_6574136) baseStart_6574136 baseEnd_6574136 := by
    simpa [prefixWord, tailWord_6574136, baseEnd_6574136] using wordTrace_append hprefix tailTrace_6574136
  have hstable : (prefixWord ++ tailWord_6574136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6574136).length < 2 ^ (prefixWord ++ tailWord_6574136).sum := by decide
  have hdescent : baseEnd_6574136 < baseStart_6574136 := by decide
  rcases family_descends (prefixWord ++ tailWord_6574136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6574166 : List Nat := [5, 2, 2, 1, 1, 1, 1, 2, 8]
def baseStart_6574166 : Nat := 118140960795 + 6574166 * 2 ^ 59
def prefixEnd_6574166 : Nat := 4983230072969 + 3 ^ 40 * 6574166 * 2
def baseEnd_6574166 : Nat := 375078562271781197665663

theorem tailTrace_6574166 : CollatzResearch.WordTrace tailWord_6574166 prefixEnd_6574166 375078562271781197665663 := by
  unfold tailWord_6574166
  simp only [CollatzResearch.WordTrace]
  refine ⟨14986220793807927188060897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 159853021800617890005982901 14986220793807927188060897)
  ·
    refine ⟨11239665595355945391045673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14986220793807927188060897 11239665595355945391045673)
    ·
      refine ⟨8429749196516959043284255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11239665595355945391045673 8429749196516959043284255)
      ·
        refine ⟨12644623794775438564926383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8429749196516959043284255 12644623794775438564926383)
        ·
          refine ⟨18966935692163157847389575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12644623794775438564926383 18966935692163157847389575)
          ·
            refine ⟨28450403538244736771084363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18966935692163157847389575 28450403538244736771084363)
            ·
              refine ⟨42675605307367105156626545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28450403538244736771084363 42675605307367105156626545)
              ·
                refine ⟨32006703980525328867469909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42675605307367105156626545 32006703980525328867469909)
                ·
                  refine ⟨375078562271781197665663, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 32006703980525328867469909 375078562271781197665663)
                  ·
                    rfl

theorem cell23_6574166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 1, 2, 8].length) (baseStart_6574166 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6574166 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6574166 prefixEnd_6574166 := by exact prefixLift 6574166
  have htrace : WordTrace (prefixWord ++ tailWord_6574166) baseStart_6574166 baseEnd_6574166 := by
    simpa [prefixWord, tailWord_6574166, baseEnd_6574166] using wordTrace_append hprefix tailTrace_6574166
  have hstable : (prefixWord ++ tailWord_6574166).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6574166).length < 2 ^ (prefixWord ++ tailWord_6574166).sum := by decide
  have hdescent : baseEnd_6574166 < baseStart_6574166 := by decide
  rcases family_descends (prefixWord ++ tailWord_6574166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6574169 : List Nat := [1, 2, 1, 2, 2, 1, 3, 3, 1, 5, 2]
def baseStart_6574169 : Nat := 118140960795 + 6574169 * 2 ^ 59
def prefixEnd_6574169 : Nat := 4983230072969 + 3 ^ 40 * 6574169 * 2
def baseEnd_6574169 : Nat := 3375708600887994267253453

theorem tailTrace_6574169 : CollatzResearch.WordTrace tailWord_6574169 prefixEnd_6574169 3375708600887994267253453 := by
  unfold tailWord_6574169
  simp only [CollatzResearch.WordTrace]
  refine ⟨239779642119915966521333561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159853094746610644347555707 239779642119915966521333561)
  ·
    refine ⟨179834731589936974891000171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 239779642119915966521333561 179834731589936974891000171)
    ·
      refine ⟨269752097384905462336500257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179834731589936974891000171 269752097384905462336500257)
      ·
        refine ⟨202314073038679096752375193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 269752097384905462336500257 202314073038679096752375193)
        ·
          refine ⟨151735554779009322564281395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 202314073038679096752375193 151735554779009322564281395)
          ·
            refine ⟨227603332168513983846422093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 151735554779009322564281395 227603332168513983846422093)
            ·
              refine ⟨85351249563192743942408285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 227603332168513983846422093 85351249563192743942408285)
              ·
                refine ⟨32006718586197278978403107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 85351249563192743942408285 32006718586197278978403107)
                ·
                  refine ⟨48010077879295918467604661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32006718586197278978403107 48010077879295918467604661)
                  ·
                    refine ⟨4500944801183992356337937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 48010077879295918467604661 4500944801183992356337937)
                    ·
                      refine ⟨3375708600887994267253453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4500944801183992356337937 3375708600887994267253453)
                      ·
                        rfl

theorem cell23_6574169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 3, 1, 5, 2].length) (baseStart_6574169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6574169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6574169 prefixEnd_6574169 := by exact prefixLift 6574169
  have htrace : WordTrace (prefixWord ++ tailWord_6574169) baseStart_6574169 baseEnd_6574169 := by
    simpa [prefixWord, tailWord_6574169, baseEnd_6574169] using wordTrace_append hprefix tailTrace_6574169
  have hstable : (prefixWord ++ tailWord_6574169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6574169).length < 2 ^ (prefixWord ++ tailWord_6574169).sum := by decide
  have hdescent : baseEnd_6574169 < baseStart_6574169 := by decide
  rcases family_descends (prefixWord ++ tailWord_6574169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6574179 : List Nat := [1, 1, 1, 5, 1, 1, 4, 3, 1, 5]
def baseStart_6574179 : Nat := 118140960795 + 6574179 * 2 ^ 59
def prefixEnd_6574179 : Nat := 4983230072969 + 3 ^ 40 * 6574179 * 2
def baseEnd_6574179 : Nat := 1125237911898179742709469

theorem tailTrace_6574179 : CollatzResearch.WordTrace tailWord_6574179 prefixEnd_6574179 1125237911898179742709469 := by
  unfold tailWord_6574179
  simp only [CollatzResearch.WordTrace]
  refine ⟨239780006849879738229197591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159853337899919825486131727 239780006849879738229197591)
  ·
    refine ⟨359670010274819607343796387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 239780006849879738229197591 359670010274819607343796387)
    ·
      refine ⟨539505015412229411015694581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 359670010274819607343796387 539505015412229411015694581)
      ·
        refine ⟨50578595194896507282721367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 539505015412229411015694581 50578595194896507282721367)
        ·
          refine ⟨75867892792344760924082051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50578595194896507282721367 75867892792344760924082051)
          ·
            refine ⟨113801839188517141386123077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75867892792344760924082051 113801839188517141386123077)
            ·
              refine ⟨21337844847846964009898077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 113801839188517141386123077 21337844847846964009898077)
              ·
                refine ⟨8001691817942611503711779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21337844847846964009898077 8001691817942611503711779)
                ·
                  refine ⟨12002537726913917255567669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8001691817942611503711779 12002537726913917255567669)
                  ·
                    refine ⟨1125237911898179742709469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12002537726913917255567669 1125237911898179742709469)
                    ·
                      rfl

theorem cell23_6574179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 4, 3, 1, 5].length) (baseStart_6574179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6574179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6574179 prefixEnd_6574179 := by exact prefixLift 6574179
  have htrace : WordTrace (prefixWord ++ tailWord_6574179) baseStart_6574179 baseEnd_6574179 := by
    simpa [prefixWord, tailWord_6574179, baseEnd_6574179] using wordTrace_append hprefix tailTrace_6574179
  have hstable : (prefixWord ++ tailWord_6574179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6574179).length < 2 ^ (prefixWord ++ tailWord_6574179).sum := by decide
  have hdescent : baseEnd_6574179 < baseStart_6574179 := by decide
  rcases family_descends (prefixWord ++ tailWord_6574179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6574216 : List Nat := [2, 1, 3, 4, 1, 2, 1, 1, 3, 1, 4]
def baseStart_6574216 : Nat := 118140960795 + 6574216 * 2 ^ 59
def prefixEnd_6574216 : Nat := 4983230072969 + 3 ^ 40 * 6574216 * 2
def baseEnd_6574216 : Nat := 3375732734478755583365737

theorem tailTrace_6574216 : CollatzResearch.WordTrace tailWord_6574216 prefixEnd_6574216 3375732734478755583365737 := by
  unfold tailWord_6574216
  simp only [CollatzResearch.WordTrace]
  refine ⟨119890678175372846774147251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159854237567163795698863001 119890678175372846774147251)
  ·
    refine ⟨179836017263059270161220877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119890678175372846774147251 179836017263059270161220877)
    ·
      refine ⟨67438506473647226310457829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 179836017263059270161220877 67438506473647226310457829)
      ·
        refine ⟨12644719963808854933210843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 67438506473647226310457829 12644719963808854933210843)
        ·
          refine ⟨18967079945713282399816265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12644719963808854933210843 18967079945713282399816265)
          ·
            refine ⟨14225309959284961799862199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18967079945713282399816265 14225309959284961799862199)
            ·
              refine ⟨21337964938927442699793299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14225309959284961799862199 21337964938927442699793299)
              ·
                refine ⟨32006947408391164049689949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21337964938927442699793299 32006947408391164049689949)
                ·
                  refine ⟨12002605278146686518633731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32006947408391164049689949 12002605278146686518633731)
                  ·
                    refine ⟨18003907917220029777950597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12002605278146686518633731 18003907917220029777950597)
                    ·
                      refine ⟨3375732734478755583365737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18003907917220029777950597 3375732734478755583365737)
                      ·
                        rfl

theorem cell23_6574216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 1, 1, 3, 1, 4].length) (baseStart_6574216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6574216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6574216 prefixEnd_6574216 := by exact prefixLift 6574216
  have htrace : WordTrace (prefixWord ++ tailWord_6574216) baseStart_6574216 baseEnd_6574216 := by
    simpa [prefixWord, tailWord_6574216, baseEnd_6574216] using wordTrace_append hprefix tailTrace_6574216
  have hstable : (prefixWord ++ tailWord_6574216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6574216).length < 2 ^ (prefixWord ++ tailWord_6574216).sum := by decide
  have hdescent : baseEnd_6574216 < baseStart_6574216 := by decide
  rcases family_descends (prefixWord ++ tailWord_6574216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6574229 : List Nat := [1, 3, 2, 1, 1, 1, 5, 2, 1, 2, 4]
def baseStart_6574229 : Nat := 118140960795 + 6574229 * 2 ^ 59
def prefixEnd_6574229 : Nat := 4983230072969 + 3 ^ 40 * 6574229 * 2
def baseEnd_6574229 : Nat := 3375739409727264032503177

theorem tailTrace_6574229 : CollatzResearch.WordTrace tailWord_6574229 prefixEnd_6574229 3375739409727264032503177 := by
  unfold tailWord_6574229
  simp only [CollatzResearch.WordTrace]
  refine ⟨239781830499698596768517741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159854553666465731179011827 239781830499698596768517741)
  ·
    refine ⟨89918186437386973788194153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 239781830499698596768517741 89918186437386973788194153)
    ·
      refine ⟨67438639828040230341145615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89918186437386973788194153 67438639828040230341145615)
      ·
        refine ⟨101157959742060345511718423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67438639828040230341145615 101157959742060345511718423)
        ·
          refine ⟨151736939613090518267577635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101157959742060345511718423 151736939613090518267577635)
          ·
            refine ⟨227605409419635777401366453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 151736939613090518267577635 227605409419635777401366453)
            ·
              refine ⟨21338007133090854131378105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 227605409419635777401366453 21338007133090854131378105)
              ·
                refine ⟨16003505349818140598533579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21338007133090854131378105 16003505349818140598533579)
                ·
                  refine ⟨24005258024727210897800369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16003505349818140598533579 24005258024727210897800369)
                  ·
                    refine ⟨18003943518545408173350277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24005258024727210897800369 18003943518545408173350277)
                    ·
                      refine ⟨3375739409727264032503177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18003943518545408173350277 3375739409727264032503177)
                      ·
                        rfl

theorem cell23_6574229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 5, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 5, 2, 1, 2, 4].length) (baseStart_6574229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6574229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6574229 prefixEnd_6574229 := by exact prefixLift 6574229
  have htrace : WordTrace (prefixWord ++ tailWord_6574229) baseStart_6574229 baseEnd_6574229 := by
    simpa [prefixWord, tailWord_6574229, baseEnd_6574229] using wordTrace_append hprefix tailTrace_6574229
  have hstable : (prefixWord ++ tailWord_6574229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6574229).length < 2 ^ (prefixWord ++ tailWord_6574229).sum := by decide
  have hdescent : baseEnd_6574229 < baseStart_6574229 := by decide
  rcases family_descends (prefixWord ++ tailWord_6574229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6574244 : List Nat := [2, 3, 1, 2, 5, 1, 2, 2, 1, 1, 3]
def baseStart_6574244 : Nat := 118140960795 + 6574244 * 2 ^ 59
def prefixEnd_6574244 : Nat := 4983230072969 + 3 ^ 40 * 6574244 * 2
def baseEnd_6574244 : Nat := 3375747111937081473815609

theorem tailTrace_6574244 : CollatzResearch.WordTrace tailWord_6574244 prefixEnd_6574244 3375747111937081473815609 := by
  unfold tailWord_6574244
  simp only [CollatzResearch.WordTrace]
  refine ⟨119891188797322127165156893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159854918396429502886875857 119891188797322127165156893)
  ·
    refine ⟨44959195798995797686933835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 119891188797322127165156893 44959195798995797686933835)
    ·
      refine ⟨67438793698493696530400753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44959195798995797686933835 67438793698493696530400753)
      ·
        refine ⟨50579095273870272397800565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67438793698493696530400753 50579095273870272397800565)
        ·
          refine ⟨4741790181925338037293803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 50579095273870272397800565 4741790181925338037293803)
          ·
            refine ⟨7112685272888007055940705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4741790181925338037293803 7112685272888007055940705)
            ·
              refine ⟨5334513954666005291955529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7112685272888007055940705 5334513954666005291955529)
              ·
                refine ⟨4000885465999503968966647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5334513954666005291955529 4000885465999503968966647)
                ·
                  refine ⟨6001328198999255953449971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4000885465999503968966647 6001328198999255953449971)
                  ·
                    refine ⟨9001992298498883930174957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6001328198999255953449971 9001992298498883930174957)
                    ·
                      refine ⟨3375747111937081473815609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9001992298498883930174957 3375747111937081473815609)
                      ·
                        rfl

theorem cell23_6574244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 5, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 5, 1, 2, 2, 1, 1, 3].length) (baseStart_6574244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6574244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6574244 prefixEnd_6574244 := by exact prefixLift 6574244
  have htrace : WordTrace (prefixWord ++ tailWord_6574244) baseStart_6574244 baseEnd_6574244 := by
    simpa [prefixWord, tailWord_6574244, baseEnd_6574244] using wordTrace_append hprefix tailTrace_6574244
  have hstable : (prefixWord ++ tailWord_6574244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6574244).length < 2 ^ (prefixWord ++ tailWord_6574244).sum := by decide
  have hdescent : baseEnd_6574244 < baseStart_6574244 := by decide
  rcases family_descends (prefixWord ++ tailWord_6574244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6574273 : List Nat := [1, 2, 6, 1, 2, 1, 3, 7]
def baseStart_6574273 : Nat := 118140960795 + 6574273 * 2 ^ 59
def prefixEnd_6574273 : Nat := 4983230072969 + 3 ^ 40 * 6574273 * 2
def baseEnd_6574273 : Nat := 125028222328743031864925

theorem tailTrace_6574273 : CollatzResearch.WordTrace tailWord_6574273 prefixEnd_6574273 125028222328743031864925 := by
  unfold tailWord_6574273
  simp only [CollatzResearch.WordTrace]
  refine ⟨239783435311539192283119473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159855623541026128188746315 239783435311539192283119473)
  ·
    refine ⟨179837576483654394212339605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 239783435311539192283119473 179837576483654394212339605)
    ·
      refine ⟨8429886397671299728703419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 179837576483654394212339605 8429886397671299728703419)
      ·
        refine ⟨12644829596506949593055129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8429886397671299728703419 12644829596506949593055129)
        ·
          refine ⟨9483622197380212194791347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12644829596506949593055129 9483622197380212194791347)
          ·
            refine ⟨14225433296070318292187021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9483622197380212194791347 14225433296070318292187021)
            ·
              refine ⟨5334537486026369359570133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14225433296070318292187021 5334537486026369359570133)
              ·
                refine ⟨125028222328743031864925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5334537486026369359570133 125028222328743031864925)
                ·
                  rfl

theorem cell23_6574273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 3, 7].length) (baseStart_6574273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6574273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6574273 prefixEnd_6574273 := by exact prefixLift 6574273
  have htrace : WordTrace (prefixWord ++ tailWord_6574273) baseStart_6574273 baseEnd_6574273 := by
    simpa [prefixWord, tailWord_6574273, baseEnd_6574273] using wordTrace_append hprefix tailTrace_6574273
  have hstable : (prefixWord ++ tailWord_6574273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6574273).length < 2 ^ (prefixWord ++ tailWord_6574273).sum := by decide
  have hdescent : baseEnd_6574273 < baseStart_6574273 := by decide
  rcases family_descends (prefixWord ++ tailWord_6574273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6574284 : List Nat := [2, 2, 1, 6, 1, 1, 2, 3, 1, 2, 2]
def baseStart_6574284 : Nat := 118140960795 + 6574284 * 2 ^ 59
def prefixEnd_6574284 : Nat := 4983230072969 + 3 ^ 40 * 6574284 * 2
def baseEnd_6574284 : Nat := 3375767651163261317315425

theorem tailTrace_6574284 : CollatzResearch.WordTrace tailWord_6574284 prefixEnd_6574284 3375767651163261317315425 := by
  unfold tailWord_6574284
  simp only [CollatzResearch.WordTrace]
  refine ⟨119891918257249670580884953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159855891009666227441179937 119891918257249670580884953)
  ·
    refine ⟨89918938692937252935663715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119891918257249670580884953 89918938692937252935663715)
    ·
      refine ⟨134878408039405879403495573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89918938692937252935663715 134878408039405879403495573)
      ·
        refine ⟨6322425376847150597038855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 134878408039405879403495573 6322425376847150597038855)
        ·
          refine ⟨9483638065270725895558283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6322425376847150597038855 9483638065270725895558283)
          ·
            refine ⟨14225457097906088843337425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9483638065270725895558283 14225457097906088843337425)
            ·
              refine ⟨10669092823429566632503069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14225457097906088843337425 10669092823429566632503069)
              ·
                refine ⟨4000909808786087487188651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10669092823429566632503069 4000909808786087487188651)
                ·
                  refine ⟨6001364713179131230782977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4000909808786087487188651 6001364713179131230782977)
                  ·
                    refine ⟨4501023534884348423087233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6001364713179131230782977 4501023534884348423087233)
                    ·
                      refine ⟨3375767651163261317315425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4501023534884348423087233 3375767651163261317315425)
                      ·
                        rfl

theorem cell23_6574284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 2, 3, 1, 2, 2].length) (baseStart_6574284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6574284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6574284 prefixEnd_6574284 := by exact prefixLift 6574284
  have htrace : WordTrace (prefixWord ++ tailWord_6574284) baseStart_6574284 baseEnd_6574284 := by
    simpa [prefixWord, tailWord_6574284, baseEnd_6574284] using wordTrace_append hprefix tailTrace_6574284
  have hstable : (prefixWord ++ tailWord_6574284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6574284).length < 2 ^ (prefixWord ++ tailWord_6574284).sum := by decide
  have hdescent : baseEnd_6574284 < baseStart_6574284 := by decide
  rcases family_descends (prefixWord ++ tailWord_6574284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6574317 : List Nat := [1, 5, 1, 2, 3, 1, 3, 1, 2, 1, 3]
def baseStart_6574317 : Nat := 118140960795 + 6574317 * 2 ^ 59
def prefixEnd_6574317 : Nat := 4983230072969 + 3 ^ 40 * 6574317 * 2
def baseEnd_6574317 : Nat := 3375784596024859688202773

theorem tailTrace_6574317 : CollatzResearch.WordTrace tailWord_6574317 prefixEnd_6574317 3375784596024859688202773 := by
  unfold tailWord_6574317
  simp only [CollatzResearch.WordTrace]
  refine ⟨239785040123379787797721205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159856693415586525198480803 239785040123379787797721205)
  ·
    refine ⟨22479847511566855106036363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 239785040123379787797721205 22479847511566855106036363)
    ·
      refine ⟨33719771267350282659054545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22479847511566855106036363 33719771267350282659054545)
      ·
        refine ⟨25289828450512711994290909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33719771267350282659054545 25289828450512711994290909)
        ·
          refine ⟨9483685668942266997859091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25289828450512711994290909 9483685668942266997859091)
          ·
            refine ⟨14225528503413400496788637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9483685668942266997859091 14225528503413400496788637)
            ·
              refine ⟨5334573188780025186295739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14225528503413400496788637 5334573188780025186295739)
              ·
                refine ⟨8001859783170037779443609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5334573188780025186295739 8001859783170037779443609)
                ·
                  refine ⟨6001394837377528334582707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8001859783170037779443609 6001394837377528334582707)
                  ·
                    refine ⟨9002092256066292501874061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6001394837377528334582707 9002092256066292501874061)
                    ·
                      refine ⟨3375784596024859688202773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9002092256066292501874061 3375784596024859688202773)
                      ·
                        rfl

theorem cell23_6574317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 3, 1, 2, 1, 3].length) (baseStart_6574317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6574317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6574317 prefixEnd_6574317 := by exact prefixLift 6574317
  have htrace : WordTrace (prefixWord ++ tailWord_6574317) baseStart_6574317 baseEnd_6574317 := by
    simpa [prefixWord, tailWord_6574317, baseEnd_6574317] using wordTrace_append hprefix tailTrace_6574317
  have hstable : (prefixWord ++ tailWord_6574317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6574317).length < 2 ^ (prefixWord ++ tailWord_6574317).sum := by decide
  have hdescent : baseEnd_6574317 < baseStart_6574317 := by decide
  rcases family_descends (prefixWord ++ tailWord_6574317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6574326 : List Nat := [5, 1, 1, 1, 1, 1, 2, 2, 2, 4, 3]
def baseStart_6574326 : Nat := 118140960795 + 6574326 * 2 ^ 59
def prefixEnd_6574326 : Nat := 4983230072969 + 3 ^ 40 * 6574326 * 2
def baseEnd_6574326 : Nat := 3375789217350750152990231

theorem tailTrace_6574326 : CollatzResearch.WordTrace tailWord_6574326 prefixEnd_6574326 3375789217350750152990231 := by
  unfold tailWord_6574326
  simp only [CollatzResearch.WordTrace]
  refine ⟨14986585523771698895924927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 159856912253564788223199221 14986585523771698895924927)
  ·
    refine ⟨22479878285657548343887391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14986585523771698895924927 22479878285657548343887391)
    ·
      refine ⟨33719817428486322515831087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22479878285657548343887391 33719817428486322515831087)
      ·
        refine ⟨50579726142729483773746631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33719817428486322515831087 50579726142729483773746631)
        ·
          refine ⟨75869589214094225660619947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50579726142729483773746631 75869589214094225660619947)
          ·
            refine ⟨113804383821141338490929921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75869589214094225660619947 113804383821141338490929921)
            ·
              refine ⟨85353287865856003868197441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 113804383821141338490929921 85353287865856003868197441)
              ·
                refine ⟨64014965899392002901148081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 85353287865856003868197441 64014965899392002901148081)
                ·
                  refine ⟨48011224424544002175861061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 64014965899392002901148081 48011224424544002175861061)
                  ·
                    refine ⟨9002104579602000407973949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 48011224424544002175861061 9002104579602000407973949)
                    ·
                      refine ⟨3375789217350750152990231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9002104579602000407973949 3375789217350750152990231)
                      ·
                        rfl

theorem cell23_6574326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 2, 2, 4, 3].length) (baseStart_6574326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6574326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6574326 prefixEnd_6574326 := by exact prefixLift 6574326
  have htrace : WordTrace (prefixWord ++ tailWord_6574326) baseStart_6574326 baseEnd_6574326 := by
    simpa [prefixWord, tailWord_6574326, baseEnd_6574326] using wordTrace_append hprefix tailTrace_6574326
  have hstable : (prefixWord ++ tailWord_6574326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6574326).length < 2 ^ (prefixWord ++ tailWord_6574326).sum := by decide
  have hdescent : baseEnd_6574326 < baseStart_6574326 := by decide
  rcases family_descends (prefixWord ++ tailWord_6574326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6574343 : List Nat := [1, 1, 4, 5, 1, 1, 1, 1, 2, 1, 5]
def baseStart_6574343 : Nat := 118140960795 + 6574343 * 2 ^ 59
def prefixEnd_6574343 : Nat := 4983230072969 + 3 ^ 40 * 6574343 * 2
def baseEnd_6574343 : Nat := 3375797946521876586477653

theorem tailTrace_6574343 : CollatzResearch.WordTrace tailWord_6574343 prefixEnd_6574343 3375797946521876586477653 := by
  unfold tailWord_6574343
  simp only [CollatzResearch.WordTrace]
  refine ⟨239785988421285594238167683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159857325614190396158778455 239785988421285594238167683)
  ·
    refine ⟨359678982631928391357251525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 239785988421285594238167683 359678982631928391357251525)
    ·
      refine ⟨67439809243486573379484661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 359678982631928391357251525 67439809243486573379484661)
      ·
        refine ⟨6322482116576866254326687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 67439809243486573379484661 6322482116576866254326687)
        ·
          refine ⟨9483723174865299381490031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6322482116576866254326687 9483723174865299381490031)
          ·
            refine ⟨14225584762297949072235047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9483723174865299381490031 14225584762297949072235047)
            ·
              refine ⟨21338377143446923608352571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14225584762297949072235047 21338377143446923608352571)
              ·
                refine ⟨32007565715170385412528857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21338377143446923608352571 32007565715170385412528857)
                ·
                  refine ⟨24005674286377789059396643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32007565715170385412528857 24005674286377789059396643)
                  ·
                    refine ⟨36008511429566683589094965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24005674286377789059396643 36008511429566683589094965)
                    ·
                      refine ⟨3375797946521876586477653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36008511429566683589094965 3375797946521876586477653)
                      ·
                        rfl

theorem cell23_6574343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 1, 1, 2, 1, 5].length) (baseStart_6574343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6574343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6574343 prefixEnd_6574343 := by exact prefixLift 6574343
  have htrace : WordTrace (prefixWord ++ tailWord_6574343) baseStart_6574343 baseEnd_6574343 := by
    simpa [prefixWord, tailWord_6574343, baseEnd_6574343] using wordTrace_append hprefix tailTrace_6574343
  have hstable : (prefixWord ++ tailWord_6574343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6574343).length < 2 ^ (prefixWord ++ tailWord_6574343).sum := by decide
  have hdescent : baseEnd_6574343 < baseStart_6574343 := by decide
  rcases family_descends (prefixWord ++ tailWord_6574343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6574369 : List Nat := [1, 2, 3, 2, 1, 1, 3, 1, 1, 1, 7]
def baseStart_6574369 : Nat := 118140960795 + 6574369 * 2 ^ 59
def prefixEnd_6574369 : Nat := 4983230072969 + 3 ^ 40 * 6574369 * 2
def baseEnd_6574369 : Nat := 3375811297018893484752533

theorem tailTrace_6574369 : CollatzResearch.WordTrace tailWord_6574369 prefixEnd_6574369 3375811297018893484752533 := by
  unfold tailWord_6574369
  simp only [CollatzResearch.WordTrace]
  refine ⟨239786936719191400678614161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159857957812794267119076107 239786936719191400678614161)
  ·
    refine ⟨179840202539393550508960621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 239786936719191400678614161 179840202539393550508960621)
    ·
      refine ⟨67440075952272581440860233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 179840202539393550508960621 67440075952272581440860233)
      ·
        refine ⟨50580056964204436080645175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67440075952272581440860233 50580056964204436080645175)
        ·
          refine ⟨75870085446306654120967763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50580056964204436080645175 75870085446306654120967763)
          ·
            refine ⟨113805128169459981181451645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75870085446306654120967763 113805128169459981181451645)
            ·
              refine ⟨42676923063547492943044367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 113805128169459981181451645 42676923063547492943044367)
              ·
                refine ⟨64015384595321239414566551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42676923063547492943044367 64015384595321239414566551)
                ·
                  refine ⟨96023076892981859121849827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 64015384595321239414566551 96023076892981859121849827)
                  ·
                    refine ⟨144034615339472788682774741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 96023076892981859121849827 144034615339472788682774741)
                    ·
                      refine ⟨3375811297018893484752533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 144034615339472788682774741 3375811297018893484752533)
                      ·
                        rfl

theorem cell23_6574369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 3, 1, 1, 1, 7].length) (baseStart_6574369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6574369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6574369 prefixEnd_6574369 := by exact prefixLift 6574369
  have htrace : WordTrace (prefixWord ++ tailWord_6574369) baseStart_6574369 baseEnd_6574369 := by
    simpa [prefixWord, tailWord_6574369, baseEnd_6574369] using wordTrace_append hprefix tailTrace_6574369
  have hstable : (prefixWord ++ tailWord_6574369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6574369).length < 2 ^ (prefixWord ++ tailWord_6574369).sum := by decide
  have hdescent : baseEnd_6574369 < baseStart_6574369 := by decide
  rcases family_descends (prefixWord ++ tailWord_6574369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6574393 : List Nat := [1, 2, 1, 6, 1, 2, 2, 1, 2, 5]
def baseStart_6574393 : Nat := 118140960795 + 6574393 * 2 ^ 59
def prefixEnd_6574393 : Nat := 4983230072969 + 3 ^ 40 * 6574393 * 2
def baseEnd_6574393 : Nat := 1125274540184867130284141

theorem tailTrace_6574393 : CollatzResearch.WordTrace tailWord_6574393 prefixEnd_6574393 1125274540184867130284141 := by
  unfold tailWord_6574393
  simp only [CollatzResearch.WordTrace]
  refine ⟨239787812071104452777487833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159858541380736301851658555 239787812071104452777487833)
  ·
    refine ⟨179840859053328339583115875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 239787812071104452777487833 179840859053328339583115875)
    ·
      refine ⟨269761288579992509374673813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179840859053328339583115875 269761288579992509374673813)
      ·
        refine ⟨12645060402187148876937835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 269761288579992509374673813 12645060402187148876937835)
        ·
          refine ⟨18967590603280723315406753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12645060402187148876937835 18967590603280723315406753)
          ·
            refine ⟨14225692952460542486555065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18967590603280723315406753 14225692952460542486555065)
            ·
              refine ⟨10669269714345406864916299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14225692952460542486555065 10669269714345406864916299)
              ·
                refine ⟨16003904571518110297374449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10669269714345406864916299 16003904571518110297374449)
                ·
                  refine ⟨12002928428638582723030837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16003904571518110297374449 12002928428638582723030837)
                  ·
                    refine ⟨1125274540184867130284141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12002928428638582723030837 1125274540184867130284141)
                    ·
                      rfl

theorem cell23_6574393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 2, 1, 2, 5].length) (baseStart_6574393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6574393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6574393 prefixEnd_6574393 := by exact prefixLift 6574393
  have htrace : WordTrace (prefixWord ++ tailWord_6574393) baseStart_6574393 baseEnd_6574393 := by
    simpa [prefixWord, tailWord_6574393, baseEnd_6574393] using wordTrace_append hprefix tailTrace_6574393
  have hstable : (prefixWord ++ tailWord_6574393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6574393).length < 2 ^ (prefixWord ++ tailWord_6574393).sum := by decide
  have hdescent : baseEnd_6574393 < baseStart_6574393 := by decide
  rcases family_descends (prefixWord ++ tailWord_6574393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6574409 : List Nat := [1, 2, 1, 1, 2, 3, 1, 3, 2, 1, 6]
def baseStart_6574409 : Nat := 118140960795 + 6574409 * 2 ^ 59
def prefixEnd_6574409 : Nat := 4983230072969 + 3 ^ 40 * 6574409 * 2
def baseEnd_6574409 : Nat := 3375831836245073328252349

theorem tailTrace_6574409 : CollatzResearch.WordTrace tailWord_6574409 prefixEnd_6574409 3375831836245073328252349 := by
  unfold tailWord_6574409
  simp only [CollatzResearch.WordTrace]
  refine ⟨239788395639046487510070281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159858930426030991673380187 239788395639046487510070281)
  ·
    refine ⟨179841296729284865632552711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 239788395639046487510070281 179841296729284865632552711)
    ·
      refine ⟨269761945093927298448829067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179841296729284865632552711 269761945093927298448829067)
      ·
        refine ⟨404642917640890947673243601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 269761945093927298448829067 404642917640890947673243601)
        ·
          refine ⟨303482188230668210754932701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 404642917640890947673243601 303482188230668210754932701)
          ·
            refine ⟨113805820586500579033099763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 303482188230668210754932701 113805820586500579033099763)
            ·
              refine ⟨170708730879750868549649645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 113805820586500579033099763 170708730879750868549649645)
              ·
                refine ⟨64015774079906575706118617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 170708730879750868549649645 64015774079906575706118617)
                ·
                  refine ⟨48011830559929931779588963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 64015774079906575706118617 48011830559929931779588963)
                  ·
                    refine ⟨72017745839894897669383445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 48011830559929931779588963 72017745839894897669383445)
                    ·
                      refine ⟨3375831836245073328252349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 72017745839894897669383445 3375831836245073328252349)
                      ·
                        rfl

theorem cell23_6574409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 3, 2, 1, 6].length) (baseStart_6574409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6574409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6574409 prefixEnd_6574409 := by exact prefixLift 6574409
  have htrace : WordTrace (prefixWord ++ tailWord_6574409) baseStart_6574409 baseEnd_6574409 := by
    simpa [prefixWord, tailWord_6574409, baseEnd_6574409] using wordTrace_append hprefix tailTrace_6574409
  have hstable : (prefixWord ++ tailWord_6574409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6574409).length < 2 ^ (prefixWord ++ tailWord_6574409).sum := by decide
  have hdescent : baseEnd_6574409 < baseStart_6574409 := by decide
  rcases family_descends (prefixWord ++ tailWord_6574409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6574436 : List Nat := [2, 3, 1, 1, 3, 1, 1, 5, 6]
def baseStart_6574436 : Nat := 118140960795 + 6574436 * 2 ^ 59
def prefixEnd_6574436 : Nat := 4983230072969 + 3 ^ 40 * 6574436 * 2
def baseEnd_6574436 : Nat := 375093966691416080290525

theorem tailTrace_6574436 : CollatzResearch.WordTrace tailWord_6574436 prefixEnd_6574436 375093966691416080290525 := by
  unfold tailWord_6574436
  simp only [CollatzResearch.WordTrace]
  refine ⟨119894690204974335560651581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159859586939965780747535441 119894690204974335560651581)
  ·
    refine ⟨44960508826865375835244343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 119894690204974335560651581 44960508826865375835244343)
    ·
      refine ⟨67440763240298063752866515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44960508826865375835244343 67440763240298063752866515)
      ·
        refine ⟨101161144860447095629299773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67440763240298063752866515 101161144860447095629299773)
        ·
          refine ⟨37935429322667660860987415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 101161144860447095629299773 37935429322667660860987415)
          ·
            refine ⟨56903143984001491291481123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37935429322667660860987415 56903143984001491291481123)
            ·
              refine ⟨85354715976002236937221685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56903143984001491291481123 85354715976002236937221685)
              ·
                refine ⟨8002004622750209712864533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 85354715976002236937221685 8002004622750209712864533)
                ·
                  refine ⟨375093966691416080290525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8002004622750209712864533 375093966691416080290525)
                  ·
                    rfl

theorem cell23_6574436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 5, 6].length) (baseStart_6574436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6574436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6574436 prefixEnd_6574436 := by exact prefixLift 6574436
  have htrace : WordTrace (prefixWord ++ tailWord_6574436) baseStart_6574436 baseEnd_6574436 := by
    simpa [prefixWord, tailWord_6574436, baseEnd_6574436] using wordTrace_append hprefix tailTrace_6574436
  have hstable : (prefixWord ++ tailWord_6574436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6574436).length < 2 ^ (prefixWord ++ tailWord_6574436).sum := by decide
  have hdescent : baseEnd_6574436 < baseStart_6574436 := by decide
  rcases family_descends (prefixWord ++ tailWord_6574436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6574450 : List Nat := [3, 2, 1, 2, 1, 5, 1, 1, 2, 2, 3]
def baseStart_6574450 : Nat := 118140960795 + 6574450 * 2 ^ 59
def prefixEnd_6574450 : Nat := 4983230072969 + 3 ^ 40 * 6574450 * 2
def baseEnd_6574450 : Nat := 3375852888951907667839661

theorem tailTrace_6574450 : CollatzResearch.WordTrace tailWord_6574450 prefixEnd_6574450 3375852888951907667839661 := by
  unfold tailWord_6574450
  simp only [CollatzResearch.WordTrace]
  refine ⟨59947472757974487878078201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 159859927354598634341541869 59947472757974487878078201)
  ·
    refine ⟨44960604568480865908558651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59947472757974487878078201 44960604568480865908558651)
    ·
      refine ⟨67440906852721298862837977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44960604568480865908558651 67440906852721298862837977)
      ·
        refine ⟨50580680139540974147128483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67440906852721298862837977 50580680139540974147128483)
        ·
          refine ⟨75871020209311461220692725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50580680139540974147128483 75871020209311461220692725)
          ·
            refine ⟨7112908144622949489439943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 75871020209311461220692725 7112908144622949489439943)
            ·
              refine ⟨10669362216934424234159915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7112908144622949489439943 10669362216934424234159915)
              ·
                refine ⟨16004043325401636351239873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10669362216934424234159915 16004043325401636351239873)
                ·
                  refine ⟨12003032494051227263429905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16004043325401636351239873 12003032494051227263429905)
                  ·
                    refine ⟨9002274370538420447572429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12003032494051227263429905 9002274370538420447572429)
                    ·
                      refine ⟨3375852888951907667839661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9002274370538420447572429 3375852888951907667839661)
                      ·
                        rfl

theorem cell23_6574450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 5, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 5, 1, 1, 2, 2, 3].length) (baseStart_6574450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6574450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6574450 prefixEnd_6574450 := by exact prefixLift 6574450
  have htrace : WordTrace (prefixWord ++ tailWord_6574450) baseStart_6574450 baseEnd_6574450 := by
    simpa [prefixWord, tailWord_6574450, baseEnd_6574450] using wordTrace_append hprefix tailTrace_6574450
  have hstable : (prefixWord ++ tailWord_6574450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6574450).length < 2 ^ (prefixWord ++ tailWord_6574450).sum := by decide
  have hdescent : baseEnd_6574450 < baseStart_6574450 := by decide
  rcases family_descends (prefixWord ++ tailWord_6574450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6574513 : List Nat := [1, 2, 2, 4, 1, 2, 1, 2, 4, 4]
def baseStart_6574513 : Nat := 118140960795 + 6574513 * 2 ^ 59
def prefixEnd_6574513 : Nat := 4983230072969 + 3 ^ 40 * 6574513 * 2
def baseEnd_6574513 : Nat := 1125295079411046973783957

theorem tailTrace_6574513 : CollatzResearch.WordTrace tailWord_6574513 prefixEnd_6574513 1125295079411046973783957 := by
  unfold tailWord_6574513
  simp only [CollatzResearch.WordTrace]
  refine ⟨239792188830669713271856193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159861459220446475514570795 239792188830669713271856193)
  ·
    refine ⟨179844141623002284953892145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 239792188830669713271856193 179844141623002284953892145)
    ·
      refine ⟨134883106217251713715419109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 179844141623002284953892145 134883106217251713715419109)
      ·
        refine ⟨25290582415734696321641083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 134883106217251713715419109 25290582415734696321641083)
        ·
          refine ⟨37935873623602044482461625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25290582415734696321641083 37935873623602044482461625)
          ·
            refine ⟨28451905217701533361846219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37935873623602044482461625 28451905217701533361846219)
            ·
              refine ⟨42677857826552300042769329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28451905217701533361846219 42677857826552300042769329)
              ·
                refine ⟨32008393369914225032076997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42677857826552300042769329 32008393369914225032076997)
                ·
                  refine ⟨6001573756858917193514437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32008393369914225032076997 6001573756858917193514437)
                  ·
                    refine ⟨1125295079411046973783957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6001573756858917193514437 1125295079411046973783957)
                    ·
                      rfl

theorem cell23_6574513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 1, 2, 4, 4].length) (baseStart_6574513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6574513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6574513 prefixEnd_6574513 := by exact prefixLift 6574513
  have htrace : WordTrace (prefixWord ++ tailWord_6574513) baseStart_6574513 baseEnd_6574513 := by
    simpa [prefixWord, tailWord_6574513, baseEnd_6574513] using wordTrace_append hprefix tailTrace_6574513
  have hstable : (prefixWord ++ tailWord_6574513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6574513).length < 2 ^ (prefixWord ++ tailWord_6574513).sum := by decide
  have hdescent : baseEnd_6574513 < baseStart_6574513 := by decide
  rcases family_descends (prefixWord ++ tailWord_6574513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6574526 : List Nat := [4, 2, 1, 1, 1, 1, 13]
def baseStart_6574526 : Nat := 118140960795 + 6574526 * 2 ^ 59
def prefixEnd_6574526 : Nat := 4983230072969 + 3 ^ 40 * 6574526 * 2
def baseEnd_6574526 : Nat := 41677677944217893462831

theorem tailTrace_6574526 : CollatzResearch.WordTrace tailWord_6574526 prefixEnd_6574526 41677677944217893462831 := by
  unfold tailWord_6574526
  simp only [CollatzResearch.WordTrace]
  refine ⟨29974082872452827061509929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 159861775319748410994719621 29974082872452827061509929)
  ·
    refine ⟨22480562154339620296132447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29974082872452827061509929 22480562154339620296132447)
    ·
      refine ⟨33720843231509430444198671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22480562154339620296132447 33720843231509430444198671)
      ·
        refine ⟨50581264847264145666298007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33720843231509430444198671 50581264847264145666298007)
        ·
          refine ⟨75871897270896218499447011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50581264847264145666298007 75871897270896218499447011)
          ·
            refine ⟨113807845906344327749170517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75871897270896218499447011 113807845906344327749170517)
            ·
              refine ⟨41677677944217893462831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 13 113807845906344327749170517 41677677944217893462831)
              ·
                rfl

theorem cell23_6574526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 13].length) (baseStart_6574526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6574526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6574526 prefixEnd_6574526 := by exact prefixLift 6574526
  have htrace : WordTrace (prefixWord ++ tailWord_6574526) baseStart_6574526 baseEnd_6574526 := by
    simpa [prefixWord, tailWord_6574526, baseEnd_6574526] using wordTrace_append hprefix tailTrace_6574526
  have hstable : (prefixWord ++ tailWord_6574526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6574526).length < 2 ^ (prefixWord ++ tailWord_6574526).sum := by decide
  have hdescent : baseEnd_6574526 < baseStart_6574526 := by decide
  rcases family_descends (prefixWord ++ tailWord_6574526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6574537 : List Nat := [1, 2, 1, 1, 2, 1, 4, 6, 1, 2, 2]
def baseStart_6574537 : Nat := 118140960795 + 6574537 * 2 ^ 59
def prefixEnd_6574537 : Nat := 4983230072969 + 3 ^ 40 * 6574537 * 2
def baseEnd_6574537 : Nat := 3375897561768848827451761

theorem tailTrace_6574537 : CollatzResearch.WordTrace tailWord_6574537 prefixEnd_6574537 3375897561768848827451761 := by
  unfold tailWord_6574537
  simp only [CollatzResearch.WordTrace]
  refine ⟨239793064182582765370729865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159862042788388510247153243 239793064182582765370729865)
  ·
    refine ⟨179844798136937074028047399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 239793064182582765370729865 179844798136937074028047399)
    ·
      refine ⟨269767197205405611042071099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179844798136937074028047399 269767197205405611042071099)
      ·
        refine ⟨404650795808108416563106649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 269767197205405611042071099 404650795808108416563106649)
        ·
          refine ⟨303488096856081312422329987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 404650795808108416563106649 303488096856081312422329987)
          ·
            refine ⟨455232145284121968633494981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 303488096856081312422329987 455232145284121968633494981)
            ·
              refine ⟨85356027240772869118780309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 455232145284121968633494981 85356027240772869118780309)
              ·
                refine ⟨4001063776911228239942827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 85356027240772869118780309 4001063776911228239942827)
                ·
                  refine ⟨6001595665366842359914241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4001063776911228239942827 6001595665366842359914241)
                  ·
                    refine ⟨4501196749025131769935681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6001595665366842359914241 4501196749025131769935681)
                    ·
                      refine ⟨3375897561768848827451761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4501196749025131769935681 3375897561768848827451761)
                      ·
                        rfl

theorem cell23_6574537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 6, 1, 2, 2].length) (baseStart_6574537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6574537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6574537 prefixEnd_6574537 := by exact prefixLift 6574537
  have htrace : WordTrace (prefixWord ++ tailWord_6574537) baseStart_6574537 baseEnd_6574537 := by
    simpa [prefixWord, tailWord_6574537, baseEnd_6574537] using wordTrace_append hprefix tailTrace_6574537
  have hstable : (prefixWord ++ tailWord_6574537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6574537).length < 2 ^ (prefixWord ++ tailWord_6574537).sum := by decide
  have hdescent : baseEnd_6574537 < baseStart_6574537 := by decide
  rcases family_descends (prefixWord ++ tailWord_6574537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6574550 : List Nat := [5, 2, 1, 1, 1, 1, 2, 3, 1, 2, 4]
def baseStart_6574550 : Nat := 118140960795 + 6574550 * 2 ^ 59
def prefixEnd_6574550 : Nat := 4983230072969 + 3 ^ 40 * 6574550 * 2
def baseEnd_6574550 : Nat := 3375904237017357276589201

theorem tailTrace_6574550 : CollatzResearch.WordTrace tailWord_6574550 prefixEnd_6574550 3375904237017357276589201 := by
  unfold tailWord_6574550
  simp only [CollatzResearch.WordTrace]
  refine ⟨14987096145720979286934569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 159862358887690445727302069 14987096145720979286934569)
  ·
    refine ⟨11240322109290734465200927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14987096145720979286934569 11240322109290734465200927)
    ·
      refine ⟨16860483163936101697801391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11240322109290734465200927 16860483163936101697801391)
      ·
        refine ⟨25290724745904152546702087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16860483163936101697801391 25290724745904152546702087)
        ·
          refine ⟨37936087118856228820053131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25290724745904152546702087 37936087118856228820053131)
          ·
            refine ⟨56904130678284343230079697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37936087118856228820053131 56904130678284343230079697)
            ·
              refine ⟨42678098008713257422559773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56904130678284343230079697 42678098008713257422559773)
              ·
                refine ⟨16004286753267471533459915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42678098008713257422559773 16004286753267471533459915)
                ·
                  refine ⟨24006430129901207300189873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16004286753267471533459915 24006430129901207300189873)
                  ·
                    refine ⟨18004822597425905475142405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24006430129901207300189873 18004822597425905475142405)
                    ·
                      refine ⟨3375904237017357276589201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18004822597425905475142405 3375904237017357276589201)
                      ·
                        rfl

theorem cell23_6574550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 2, 3, 1, 2, 4].length) (baseStart_6574550 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6574550 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6574550 prefixEnd_6574550 := by exact prefixLift 6574550
  have htrace : WordTrace (prefixWord ++ tailWord_6574550) baseStart_6574550 baseEnd_6574550 := by
    simpa [prefixWord, tailWord_6574550, baseEnd_6574550] using wordTrace_append hprefix tailTrace_6574550
  have hstable : (prefixWord ++ tailWord_6574550).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6574550).length < 2 ^ (prefixWord ++ tailWord_6574550).sum := by decide
  have hdescent : baseEnd_6574550 < baseStart_6574550 := by decide
  rcases family_descends (prefixWord ++ tailWord_6574550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6574553 : List Nat := [1, 2, 1, 2, 4, 1, 2, 3, 1, 3, 3]
def baseStart_6574553 : Nat := 118140960795 + 6574553 * 2 ^ 59
def prefixEnd_6574553 : Nat := 4983230072969 + 3 ^ 40 * 6574553 * 2
def baseEnd_6574553 : Nat := 3375905777459320764851687

theorem tailTrace_6574553 : CollatzResearch.WordTrace tailWord_6574553 prefixEnd_6574553 3375905777459320764851687 := by
  unfold tailWord_6574553
  simp only [CollatzResearch.WordTrace]
  refine ⟨239793647750524800103312313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159862431833683200068874875 239793647750524800103312313)
  ·
    refine ⟨179845235812893600077484235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 239793647750524800103312313 179845235812893600077484235)
    ·
      refine ⟨269767853719340400116226353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179845235812893600077484235 269767853719340400116226353)
      ·
        refine ⟨202325890289505300087169765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 269767853719340400116226353 202325890289505300087169765)
        ·
          refine ⟨37936104429282243766344331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 202325890289505300087169765 37936104429282243766344331)
          ·
            refine ⟨56904156643923365649516497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37936104429282243766344331 56904156643923365649516497)
            ·
              refine ⟨42678117482942524237137373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56904156643923365649516497 42678117482942524237137373)
              ·
                refine ⟨16004294056103446588926515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42678117482942524237137373 16004294056103446588926515)
                ·
                  refine ⟨24006441084155169883389773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16004294056103446588926515 24006441084155169883389773)
                  ·
                    refine ⟨9002415406558188706271165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24006441084155169883389773 9002415406558188706271165)
                    ·
                      refine ⟨3375905777459320764851687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9002415406558188706271165 3375905777459320764851687)
                      ·
                        rfl

theorem cell23_6574553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 2, 3, 1, 3, 3].length) (baseStart_6574553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6574553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6574553 prefixEnd_6574553 := by exact prefixLift 6574553
  have htrace : WordTrace (prefixWord ++ tailWord_6574553) baseStart_6574553 baseEnd_6574553 := by
    simpa [prefixWord, tailWord_6574553, baseEnd_6574553] using wordTrace_append hprefix tailTrace_6574553
  have hstable : (prefixWord ++ tailWord_6574553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6574553).length < 2 ^ (prefixWord ++ tailWord_6574553).sum := by decide
  have hdescent : baseEnd_6574553 < baseStart_6574553 := by decide
  rcases family_descends (prefixWord ++ tailWord_6574553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6574570 : List Nat := [3, 1, 3, 1, 3, 2, 1, 2, 1, 3, 3]
def baseStart_6574570 : Nat := 118140960795 + 6574570 * 2 ^ 59
def prefixEnd_6574570 : Nat := 4983230072969 + 3 ^ 40 * 6574570 * 2
def baseEnd_6574570 : Nat := 3375914506630447198339109

theorem tailTrace_6574570 : CollatzResearch.WordTrace tailWord_6574570 prefixEnd_6574570 3375914506630447198339109 := by
  unfold tailWord_6574570
  simp only [CollatzResearch.WordTrace]
  refine ⟨59948566947865803001670291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 159862845194308808004454109 59948566947865803001670291)
  ·
    refine ⟨89922850421798704502505437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59948566947865803001670291 89922850421798704502505437)
    ·
      refine ⟨33721068908174514188439539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 89922850421798704502505437 33721068908174514188439539)
      ·
        refine ⟨50581603362261771282659309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33721068908174514188439539 50581603362261771282659309)
        ·
          refine ⟨18968101260848164230997241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50581603362261771282659309 18968101260848164230997241)
          ·
            refine ⟨14226075945636123173247931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18968101260848164230997241 14226075945636123173247931)
            ·
              refine ⟨21339113918454184759871897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14226075945636123173247931 21339113918454184759871897)
              ·
                refine ⟨16004335438840638569903923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21339113918454184759871897 16004335438840638569903923)
                ·
                  refine ⟨24006503158260957854855885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16004335438840638569903923 24006503158260957854855885)
                  ·
                    refine ⟨9002438684347859195570957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24006503158260957854855885 9002438684347859195570957)
                    ·
                      refine ⟨3375914506630447198339109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9002438684347859195570957 3375914506630447198339109)
                      ·
                        rfl

theorem cell23_6574570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 1, 2, 1, 3, 3].length) (baseStart_6574570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6574570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6574570 prefixEnd_6574570 := by exact prefixLift 6574570
  have htrace : WordTrace (prefixWord ++ tailWord_6574570) baseStart_6574570 baseEnd_6574570 := by
    simpa [prefixWord, tailWord_6574570, baseEnd_6574570] using wordTrace_append hprefix tailTrace_6574570
  have hstable : (prefixWord ++ tailWord_6574570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6574570).length < 2 ^ (prefixWord ++ tailWord_6574570).sum := by decide
  have hdescent : baseEnd_6574570 < baseStart_6574570 := by decide
  rcases family_descends (prefixWord ++ tailWord_6574570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6574593 : List Nat := [1, 2, 4, 1, 3, 1, 1, 1, 2, 3, 4]
def baseStart_6574593 : Nat := 118140960795 + 6574593 * 2 ^ 59
def prefixEnd_6574593 : Nat := 4983230072969 + 3 ^ 40 * 6574593 * 2
def baseEnd_6574593 : Nat := 3375926316685500608351503

theorem tailTrace_6574593 : CollatzResearch.WordTrace tailWord_6574593 prefixEnd_6574593 3375926316685500608351503 := by
  unfold tailWord_6574593
  simp only [CollatzResearch.WordTrace]
  refine ⟨239795106670379886934768433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159863404446919924623178955 239795106670379886934768433)
  ·
    refine ⟨179846330002784915201076325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 239795106670379886934768433 179846330002784915201076325)
    ·
      refine ⟨33721186875522171600201811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 179846330002784915201076325 33721186875522171600201811)
      ·
        refine ⟨50581780313283257400302717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33721186875522171600201811 50581780313283257400302717)
        ·
          refine ⟨18968167617481221525113519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50581780313283257400302717 18968167617481221525113519)
          ·
            refine ⟨28452251426221832287670279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18968167617481221525113519 28452251426221832287670279)
            ·
              refine ⟨42678377139332748431505419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28452251426221832287670279 42678377139332748431505419)
              ·
                refine ⟨64017565708999122647258129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42678377139332748431505419 64017565708999122647258129)
                ·
                  refine ⟨48013174281749341985443597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 64017565708999122647258129 48013174281749341985443597)
                  ·
                    refine ⟨18004940355656003244541349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 48013174281749341985443597 18004940355656003244541349)
                    ·
                      refine ⟨3375926316685500608351503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18004940355656003244541349 3375926316685500608351503)
                      ·
                        rfl

theorem cell23_6574593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 1, 1, 2, 3, 4].length) (baseStart_6574593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6574593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6574593 prefixEnd_6574593 := by exact prefixLift 6574593
  have htrace : WordTrace (prefixWord ++ tailWord_6574593) baseStart_6574593 baseEnd_6574593 := by
    simpa [prefixWord, tailWord_6574593, baseEnd_6574593] using wordTrace_append hprefix tailTrace_6574593
  have hstable : (prefixWord ++ tailWord_6574593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6574593).length < 2 ^ (prefixWord ++ tailWord_6574593).sum := by decide
  have hdescent : baseEnd_6574593 < baseStart_6574593 := by decide
  rcases family_descends (prefixWord ++ tailWord_6574593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6574603 : List Nat := [1, 1, 1, 1, 7, 2, 1, 1, 2, 6]
def baseStart_6574603 : Nat := 118140960795 + 6574603 * 2 ^ 59
def prefixEnd_6574603 : Nat := 4983230072969 + 3 ^ 40 * 6574603 * 2
def baseEnd_6574603 : Nat := 1125310483830681856408819

theorem tailTrace_6574603 : CollatzResearch.WordTrace tailWord_6574603 prefixEnd_6574603 1125310483830681856408819 := by
  unfold tailWord_6574603
  simp only [CollatzResearch.WordTrace]
  refine ⟨239795471400343658642632463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159863647600229105761754975 239795471400343658642632463)
  ·
    refine ⟨359693207100515487963948695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 239795471400343658642632463 359693207100515487963948695)
    ·
      refine ⟨539539810650773231945923043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 359693207100515487963948695 539539810650773231945923043)
      ·
        refine ⟨809309715976159847918884565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 539539810650773231945923043 809309715976159847918884565)
        ·
          refine ⟨18968196468191246435598857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 809309715976159847918884565 18968196468191246435598857)
          ·
            refine ⟨14226147351143434826699143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18968196468191246435598857 14226147351143434826699143)
            ·
              refine ⟨21339221026715152240048715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14226147351143434826699143 21339221026715152240048715)
              ·
                refine ⟨32008831540072728360073073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21339221026715152240048715 32008831540072728360073073)
                ·
                  refine ⟨24006623655054546270054805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32008831540072728360073073 24006623655054546270054805)
                  ·
                    refine ⟨1125310483830681856408819, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24006623655054546270054805 1125310483830681856408819)
                    ·
                      rfl

theorem cell23_6574603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 1, 1, 2, 6].length) (baseStart_6574603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6574603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6574603 prefixEnd_6574603 := by exact prefixLift 6574603
  have htrace : WordTrace (prefixWord ++ tailWord_6574603) baseStart_6574603 baseEnd_6574603 := by
    simpa [prefixWord, tailWord_6574603, baseEnd_6574603] using wordTrace_append hprefix tailTrace_6574603
  have hstable : (prefixWord ++ tailWord_6574603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6574603).length < 2 ^ (prefixWord ++ tailWord_6574603).sum := by decide
  have hdescent : baseEnd_6574603 < baseStart_6574603 := by decide
  rcases family_descends (prefixWord ++ tailWord_6574603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6574613 : List Nat := [1, 3, 2, 1, 3, 1, 1, 2, 2, 4, 3]
def baseStart_6574613 : Nat := 118140960795 + 6574613 * 2 ^ 59
def prefixEnd_6574613 : Nat := 4983230072969 + 3 ^ 40 * 6574613 * 2
def baseEnd_6574613 : Nat := 3375936586298590530101411

theorem tailTrace_6574613 : CollatzResearch.WordTrace tailWord_6574613 prefixEnd_6574613 3375936586298590530101411 := by
  unfold tailWord_6574613
  simp only [CollatzResearch.WordTrace]
  refine ⟨239795836130307430350496493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159863890753538286900330995 239795836130307430350496493)
  ·
    refine ⟨89923438548865286381436185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 239795836130307430350496493 89923438548865286381436185)
    ·
      refine ⟨67442578911648964786077139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89923438548865286381436185 67442578911648964786077139)
      ·
        refine ⟨101163868367473447179115709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67442578911648964786077139 101163868367473447179115709)
        ·
          refine ⟨37936450637802542692168391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 101163868367473447179115709 37936450637802542692168391)
          ·
            refine ⟨56904675956703814038252587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37936450637802542692168391 56904675956703814038252587)
            ·
              refine ⟨85357013935055721057378881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56904675956703814038252587 85357013935055721057378881)
              ·
                refine ⟨64017760451291790793034161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 85357013935055721057378881 64017760451291790793034161)
                ·
                  refine ⟨48013320338468843094775621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 64017760451291790793034161 48013320338468843094775621)
                  ·
                    refine ⟨9002497563462908080270429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 48013320338468843094775621 9002497563462908080270429)
                    ·
                      refine ⟨3375936586298590530101411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9002497563462908080270429 3375936586298590530101411)
                      ·
                        rfl

theorem cell23_6574613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 2, 2, 4, 3].length) (baseStart_6574613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6574613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6574613 prefixEnd_6574613 := by exact prefixLift 6574613
  have htrace : WordTrace (prefixWord ++ tailWord_6574613) baseStart_6574613 baseEnd_6574613 := by
    simpa [prefixWord, tailWord_6574613, baseEnd_6574613] using wordTrace_append hprefix tailTrace_6574613
  have hstable : (prefixWord ++ tailWord_6574613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6574613).length < 2 ^ (prefixWord ++ tailWord_6574613).sum := by decide
  have hdescent : baseEnd_6574613 < baseStart_6574613 := by decide
  rcases family_descends (prefixWord ++ tailWord_6574613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6574631 : List Nat := [1, 1, 7, 2, 1, 1, 1, 3, 1, 3, 2]
def baseStart_6574631 : Nat := 118140960795 + 6574631 * 2 ^ 59
def prefixEnd_6574631 : Nat := 4983230072969 + 3 ^ 40 * 6574631 * 2
def baseEnd_6574631 : Nat := 3375945828950371459676329

theorem tailTrace_6574631 : CollatzResearch.WordTrace tailWord_6574631 prefixEnd_6574631 3375945828950371459676329 := by
  unfold tailWord_6574631
  simp only [CollatzResearch.WordTrace]
  refine ⟨239796492644242219424651747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159864328429494812949767831 239796492644242219424651747)
  ·
    refine ⟨359694738966363329136977621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 239796492644242219424651747 359694738966363329136977621)
    ·
      refine ⟨8430345444524140526647913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 359694738966363329136977621 8430345444524140526647913)
      ·
        refine ⟨6322759083393105394985935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8430345444524140526647913 6322759083393105394985935)
        ·
          refine ⟨9484138625089658092478903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6322759083393105394985935 9484138625089658092478903)
          ·
            refine ⟨14226207937634487138718355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9484138625089658092478903 14226207937634487138718355)
            ·
              refine ⟨21339311906451730708077533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14226207937634487138718355 21339311906451730708077533)
              ·
                refine ⟨8002241964919399015529075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21339311906451730708077533 8002241964919399015529075)
                ·
                  refine ⟨12003362947379098523293613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8002241964919399015529075 12003362947379098523293613)
                  ·
                    refine ⟨4501261105267161946235105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12003362947379098523293613 4501261105267161946235105)
                    ·
                      refine ⟨3375945828950371459676329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4501261105267161946235105 3375945828950371459676329)
                      ·
                        rfl

theorem cell23_6574631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 1, 3, 1, 3, 2].length) (baseStart_6574631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6574631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6574631 prefixEnd_6574631 := by exact prefixLift 6574631
  have htrace : WordTrace (prefixWord ++ tailWord_6574631) baseStart_6574631 baseEnd_6574631 := by
    simpa [prefixWord, tailWord_6574631, baseEnd_6574631] using wordTrace_append hprefix tailTrace_6574631
  have hstable : (prefixWord ++ tailWord_6574631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6574631).length < 2 ^ (prefixWord ++ tailWord_6574631).sum := by decide
  have hdescent : baseEnd_6574631 < baseStart_6574631 := by decide
  rcases family_descends (prefixWord ++ tailWord_6574631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6574643 : List Nat := [1, 1, 1, 2, 4, 2, 1, 1, 4, 3, 3]
def baseStart_6574643 : Nat := 118140960795 + 6574643 * 2 ^ 59
def prefixEnd_6574643 : Nat := 4983230072969 + 3 ^ 40 * 6574643 * 2
def baseEnd_6574643 : Nat := 3375951990718225412726273

theorem tailTrace_6574643 : CollatzResearch.WordTrace tailWord_6574643 prefixEnd_6574643 3375951990718225412726273 := by
  unfold tailWord_6574643
  simp only [CollatzResearch.WordTrace]
  refine ⟨239796930320198745474088583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159864620213465830316059055 239796930320198745474088583)
  ·
    refine ⟨359695395480298118211132875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 239796930320198745474088583 359695395480298118211132875)
    ·
      refine ⟨539543093220447177316699313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 359695395480298118211132875 539543093220447177316699313)
      ·
        refine ⟨404657319915335382987524485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 539543093220447177316699313 404657319915335382987524485)
        ·
          refine ⟨75873247484125384310160841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 404657319915335382987524485 75873247484125384310160841)
          ·
            refine ⟨56904935613094038232620631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75873247484125384310160841 56904935613094038232620631)
            ·
              refine ⟨85357403419641057348930947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56904935613094038232620631 85357403419641057348930947)
              ·
                refine ⟨128036105129461586023396421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 85357403419641057348930947 128036105129461586023396421)
                ·
                  refine ⟨24006769711774047379386829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 128036105129461586023396421 24006769711774047379386829)
                  ·
                    refine ⟨9002538641915267767270061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24006769711774047379386829 9002538641915267767270061)
                    ·
                      refine ⟨3375951990718225412726273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9002538641915267767270061 3375951990718225412726273)
                      ·
                        rfl

theorem cell23_6574643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 1, 4, 3, 3].length) (baseStart_6574643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6574643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6574643 prefixEnd_6574643 := by exact prefixLift 6574643
  have htrace : WordTrace (prefixWord ++ tailWord_6574643) baseStart_6574643 baseEnd_6574643 := by
    simpa [prefixWord, tailWord_6574643, baseEnd_6574643] using wordTrace_append hprefix tailTrace_6574643
  have hstable : (prefixWord ++ tailWord_6574643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6574643).length < 2 ^ (prefixWord ++ tailWord_6574643).sum := by decide
  have hdescent : baseEnd_6574643 < baseStart_6574643 := by decide
  rcases family_descends (prefixWord ++ tailWord_6574643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6574650 : List Nat := [3, 1, 1, 1, 3, 3, 2, 4, 5]
def baseStart_6574650 : Nat := 118140960795 + 6574650 * 2 ^ 59
def prefixEnd_6574650 : Nat := 4983230072969 + 3 ^ 40 * 6574650 * 2
def baseEnd_6574650 : Nat := 375106176120311876148749

theorem tailTrace_6574650 : CollatzResearch.WordTrace tailWord_6574650 prefixEnd_6574650 375106176120311876148749 := by
  unfold tailWord_6574650
  simp only [CollatzResearch.WordTrace]
  refine ⟨59949296407793346417398351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 159864790420782257113062269 59949296407793346417398351)
  ·
    refine ⟨89923944611690019626097527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59949296407793346417398351 89923944611690019626097527)
    ·
      refine ⟨134885916917535029439146291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89923944611690019626097527 134885916917535029439146291)
      ·
        refine ⟨202328875376302544158719437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134885916917535029439146291 202328875376302544158719437)
        ·
          refine ⟨75873328266113454059519789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 202328875376302544158719437 75873328266113454059519789)
          ·
            refine ⟨28452498099792545272319921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 75873328266113454059519789 28452498099792545272319921)
            ·
              refine ⟨21339373574844408954239941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28452498099792545272319921 21339373574844408954239941)
              ·
                refine ⟨4001132545283326678919989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21339373574844408954239941 4001132545283326678919989)
                ·
                  refine ⟨375106176120311876148749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4001132545283326678919989 375106176120311876148749)
                  ·
                    rfl

theorem cell23_6574650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 2, 4, 5].length) (baseStart_6574650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6574650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6574650 prefixEnd_6574650 := by exact prefixLift 6574650
  have htrace : WordTrace (prefixWord ++ tailWord_6574650) baseStart_6574650 baseEnd_6574650 := by
    simpa [prefixWord, tailWord_6574650, baseEnd_6574650] using wordTrace_append hprefix tailTrace_6574650
  have hstable : (prefixWord ++ tailWord_6574650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6574650).length < 2 ^ (prefixWord ++ tailWord_6574650).sum := by decide
  have hdescent : baseEnd_6574650 < baseStart_6574650 := by decide
  rcases family_descends (prefixWord ++ tailWord_6574650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6574663 : List Nat := [1, 1, 4, 1, 4, 1, 1, 2, 1, 7]
def baseStart_6574663 : Nat := 118140960795 + 6574663 * 2 ^ 59
def prefixEnd_6574663 : Nat := 4983230072969 + 3 ^ 40 * 6574663 * 2
def baseEnd_6574663 : Nat := 1125320753443771778158727

theorem tailTrace_6574663 : CollatzResearch.WordTrace tailWord_6574663 prefixEnd_6574663 1125320753443771778158727 := by
  unfold tailWord_6574663
  simp only [CollatzResearch.WordTrace]
  refine ⟨239797659780126288889816643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159865106520084192593211095 239797659780126288889816643)
  ·
    refine ⟨359696489670189433334724965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 239797659780126288889816643 359696489670189433334724965)
    ·
      refine ⟨67443091813160518750260931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 359696489670189433334724965 67443091813160518750260931)
      ·
        refine ⟨101164637719740778125391397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67443091813160518750260931 101164637719740778125391397)
        ·
          refine ⟨18968369572451395898510887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 101164637719740778125391397 18968369572451395898510887)
          ·
            refine ⟨28452554358677093847766331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18968369572451395898510887 28452554358677093847766331)
            ·
              refine ⟨42678831538015640771649497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28452554358677093847766331 42678831538015640771649497)
              ·
                refine ⟨32009123653511730578737123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42678831538015640771649497 32009123653511730578737123)
                ·
                  refine ⟨48013685480267595868105685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32009123653511730578737123 48013685480267595868105685)
                  ·
                    refine ⟨1125320753443771778158727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 48013685480267595868105685 1125320753443771778158727)
                    ·
                      rfl

theorem cell23_6574663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 1, 2, 1, 7].length) (baseStart_6574663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6574663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6574663 prefixEnd_6574663 := by exact prefixLift 6574663
  have htrace : WordTrace (prefixWord ++ tailWord_6574663) baseStart_6574663 baseEnd_6574663 := by
    simpa [prefixWord, tailWord_6574663, baseEnd_6574663] using wordTrace_append hprefix tailTrace_6574663
  have hstable : (prefixWord ++ tailWord_6574663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6574663).length < 2 ^ (prefixWord ++ tailWord_6574663).sum := by decide
  have hdescent : baseEnd_6574663 < baseStart_6574663 := by decide
  rcases family_descends (prefixWord ++ tailWord_6574663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6574670 : List Nat := [4, 1, 1, 1, 1, 2, 2, 2, 2, 5, 2]
def baseStart_6574670 : Nat := 118140960795 + 6574670 * 2 ^ 59
def prefixEnd_6574670 : Nat := 4983230072969 + 3 ^ 40 * 6574670 * 2
def baseEnd_6574670 : Nat := 3375965854695896807088649

theorem tailTrace_6574670 : CollatzResearch.WordTrace tailWord_6574670 prefixEnd_6574670 3375965854695896807088649 := by
  unfold tailWord_6574670
  simp only [CollatzResearch.WordTrace]
  refine ⟨29974739386387616135665183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 159865276727400619390214309 29974739386387616135665183)
  ·
    refine ⟨44962109079581424203497775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29974739386387616135665183 44962109079581424203497775)
    ·
      refine ⟨67443163619372136305246663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44962109079581424203497775 67443163619372136305246663)
      ·
        refine ⟨101164745429058204457869995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67443163619372136305246663 101164745429058204457869995)
        ·
          refine ⟨151747118143587306686804993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101164745429058204457869995 151747118143587306686804993)
          ·
            refine ⟨113810338607690480015103745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 151747118143587306686804993 113810338607690480015103745)
            ·
              refine ⟨85357753955767860011327809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 113810338607690480015103745 85357753955767860011327809)
              ·
                refine ⟨64018315466825895008495857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 85357753955767860011327809 64018315466825895008495857)
                ·
                  refine ⟨48013736600119421256371893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 64018315466825895008495857 48013736600119421256371893)
                  ·
                    refine ⟨4501287806261195742784865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 48013736600119421256371893 4501287806261195742784865)
                    ·
                      refine ⟨3375965854695896807088649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4501287806261195742784865 3375965854695896807088649)
                      ·
                        rfl

theorem cell23_6574670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 2, 2, 5, 2].length) (baseStart_6574670 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6574670 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6574670 prefixEnd_6574670 := by exact prefixLift 6574670
  have htrace : WordTrace (prefixWord ++ tailWord_6574670) baseStart_6574670 baseEnd_6574670 := by
    simpa [prefixWord, tailWord_6574670, baseEnd_6574670] using wordTrace_append hprefix tailTrace_6574670
  have hstable : (prefixWord ++ tailWord_6574670).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6574670).length < 2 ^ (prefixWord ++ tailWord_6574670).sum := by decide
  have hdescent : baseEnd_6574670 < baseStart_6574670 := by decide
  rcases family_descends (prefixWord ++ tailWord_6574670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6574684 : List Nat := [2, 2, 4, 1, 3, 2, 1, 3, 5]
def baseStart_6574684 : Nat := 118140960795 + 6574684 * 2 ^ 59
def prefixEnd_6574684 : Nat := 4983230072969 + 3 ^ 40 * 6574684 * 2
def baseEnd_6574684 : Nat := 375108115936117750257065

theorem tailTrace_6574684 : CollatzResearch.WordTrace tailWord_6574684 prefixEnd_6574684 375108115936117750257065 := by
  unfold tailWord_6574684
  simp only [CollatzResearch.WordTrace]
  refine ⟨119899212856525104738165553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159865617142033472984220737 119899212856525104738165553)
  ·
    refine ⟨89924409642393828553624165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119899212856525104738165553 89924409642393828553624165)
    ·
      refine ⟨16860826807948842853804531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 89924409642393828553624165 16860826807948842853804531)
      ·
        refine ⟨25291240211923264280706797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16860826807948842853804531 25291240211923264280706797)
        ·
          refine ⟨9484215079471224105265049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25291240211923264280706797 9484215079471224105265049)
          ·
            refine ⟨7113161309603418078948787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9484215079471224105265049 7113161309603418078948787)
            ·
              refine ⟨10669741964405127118423181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7113161309603418078948787 10669741964405127118423181)
              ·
                refine ⟨4001153236651922669408693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10669741964405127118423181 4001153236651922669408693)
                ·
                  refine ⟨375108115936117750257065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4001153236651922669408693 375108115936117750257065)
                  ·
                    rfl

theorem cell23_6574684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 2, 1, 3, 5].length) (baseStart_6574684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6574684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6574684 prefixEnd_6574684 := by exact prefixLift 6574684
  have htrace : WordTrace (prefixWord ++ tailWord_6574684) baseStart_6574684 baseEnd_6574684 := by
    simpa [prefixWord, tailWord_6574684, baseEnd_6574684] using wordTrace_append hprefix tailTrace_6574684
  have hstable : (prefixWord ++ tailWord_6574684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6574684).length < 2 ^ (prefixWord ++ tailWord_6574684).sum := by decide
  have hdescent : baseEnd_6574684 < baseStart_6574684 := by decide
  rcases family_descends (prefixWord ++ tailWord_6574684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6574700 : List Nat := [2, 2, 1, 1, 3, 1, 2, 1, 4, 4, 2]
def baseStart_6574700 : Nat := 118140960795 + 6574700 * 2 ^ 59
def prefixEnd_6574700 : Nat := 4983230072969 + 3 ^ 40 * 6574700 * 2
def baseEnd_6574700 : Nat := 3375981259115531689713511

theorem tailTrace_6574700 : CollatzResearch.WordTrace tailWord_6574700 prefixEnd_6574700 3375981259115531689713511 := by
  unfold tailWord_6574700
  simp only [CollatzResearch.WordTrace]
  refine ⟨119899504640496122104456777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159866006187328162805942369 119899504640496122104456777)
  ·
    refine ⟨89924628480372091578342583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119899504640496122104456777 89924628480372091578342583)
    ·
      refine ⟨134886942720558137367513875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89924628480372091578342583 134886942720558137367513875)
      ·
        refine ⟨202330414080837206051270813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134886942720558137367513875 202330414080837206051270813)
        ·
          refine ⟨75873905280313952269226555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 202330414080837206051270813 75873905280313952269226555)
          ·
            refine ⟨113810857920470928403839833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75873905280313952269226555 113810857920470928403839833)
            ·
              refine ⟨85358143440353196302879875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 113810857920470928403839833 85358143440353196302879875)
              ·
                refine ⟨128037215160529794454319813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 85358143440353196302879875 128037215160529794454319813)
                ·
                  refine ⟨24006977842599336460184965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 128037215160529794454319813 24006977842599336460184965)
                  ·
                    refine ⟨4501308345487375586284681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24006977842599336460184965 4501308345487375586284681)
                    ·
                      refine ⟨3375981259115531689713511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4501308345487375586284681 3375981259115531689713511)
                      ·
                        rfl

theorem cell23_6574700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 4, 2].length) (baseStart_6574700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6574700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6574700 prefixEnd_6574700 := by exact prefixLift 6574700
  have htrace : WordTrace (prefixWord ++ tailWord_6574700) baseStart_6574700 baseEnd_6574700 := by
    simpa [prefixWord, tailWord_6574700, baseEnd_6574700] using wordTrace_append hprefix tailTrace_6574700
  have hstable : (prefixWord ++ tailWord_6574700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6574700).length < 2 ^ (prefixWord ++ tailWord_6574700).sum := by decide
  have hdescent : baseEnd_6574700 < baseStart_6574700 := by decide
  rcases family_descends (prefixWord ++ tailWord_6574700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6574794 : List Nat := [3, 1, 2, 1, 4, 1, 3, 1, 2, 3, 2]
def baseStart_6574794 : Nat := 118140960795 + 6574794 * 2 ^ 59
def prefixEnd_6574794 : Nat := 4983230072969 + 3 ^ 40 * 6574794 * 2
def baseEnd_6574794 : Nat := 3376029526297054321938079

theorem tailTrace_6574794 : CollatzResearch.WordTrace tailWord_6574794 prefixEnd_6574794 3376029526297054321938079 := by
  unfold tailWord_6574794
  simp only [CollatzResearch.WordTrace]
  refine ⟨59950609435662924565708859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 159868291828434465508556957 59950609435662924565708859)
  ·
    refine ⟨89925914153494386848563289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59950609435662924565708859 89925914153494386848563289)
    ·
      refine ⟨67444435615120790136422467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89925914153494386848563289 67444435615120790136422467)
      ·
        refine ⟨101166653422681185204633701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67444435615120790136422467 101166653422681185204633701)
        ·
          refine ⟨18968747516752722225868819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 101166653422681185204633701 18968747516752722225868819)
          ·
            refine ⟨28453121275129083338803229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18968747516752722225868819 28453121275129083338803229)
            ·
              refine ⟨10669920478173406252051211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28453121275129083338803229 10669920478173406252051211)
              ·
                refine ⟨16004880717260109378076817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10669920478173406252051211 16004880717260109378076817)
                ·
                  refine ⟨12003660537945082033557613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16004880717260109378076817 12003660537945082033557613)
                  ·
                    refine ⟨4501372701729405762584105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12003660537945082033557613 4501372701729405762584105)
                    ·
                      refine ⟨3376029526297054321938079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4501372701729405762584105 3376029526297054321938079)
                      ·
                        rfl

theorem cell23_6574794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 3, 1, 2, 3, 2].length) (baseStart_6574794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6574794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6574794 prefixEnd_6574794 := by exact prefixLift 6574794
  have htrace : WordTrace (prefixWord ++ tailWord_6574794) baseStart_6574794 baseEnd_6574794 := by
    simpa [prefixWord, tailWord_6574794, baseEnd_6574794] using wordTrace_append hprefix tailTrace_6574794
  have hstable : (prefixWord ++ tailWord_6574794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6574794).length < 2 ^ (prefixWord ++ tailWord_6574794).sum := by decide
  have hdescent : baseEnd_6574794 < baseStart_6574794 := by decide
  rcases family_descends (prefixWord ++ tailWord_6574794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6574804 : List Nat := [2, 4, 1, 3, 2, 1, 1, 3, 1, 5]
def baseStart_6574804 : Nat := 118140960795 + 6574804 * 2 ^ 59
def prefixEnd_6574804 : Nat := 4983230072969 + 3 ^ 40 * 6574804 * 2
def baseEnd_6574804 : Nat := 1125344887034533094271011

theorem tailTrace_6574804 : CollatzResearch.WordTrace tailWord_6574804 prefixEnd_6574804 1125344887034533094271011 := by
  unfold tailWord_6574804
  simp only [CollatzResearch.WordTrace]
  refine ⟨119901401236307734985349733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159868534981743646647132977 119901401236307734985349733)
  ·
    refine ⟨22481512731807700309753075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 119901401236307734985349733 22481512731807700309753075)
    ·
      refine ⟨33722269097711550464629613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22481512731807700309753075 33722269097711550464629613)
      ·
        refine ⟨12645850911641831424236105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33722269097711550464629613 12645850911641831424236105)
        ·
          refine ⟨9484388183731373568177079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12645850911641831424236105 9484388183731373568177079)
          ·
            refine ⟨14226582275597060352265619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9484388183731373568177079 14226582275597060352265619)
            ·
              refine ⟨21339873413395590528398429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14226582275597060352265619 21339873413395590528398429)
              ·
                refine ⟨8002452530023346448149411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21339873413395590528398429 8002452530023346448149411)
                ·
                  refine ⟨12003678795035019672224117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8002452530023346448149411 12003678795035019672224117)
                  ·
                    refine ⟨1125344887034533094271011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12003678795035019672224117 1125344887034533094271011)
                    ·
                      rfl

theorem cell23_6574804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 1, 3, 1, 5].length) (baseStart_6574804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6574804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6574804 prefixEnd_6574804 := by exact prefixLift 6574804
  have htrace : WordTrace (prefixWord ++ tailWord_6574804) baseStart_6574804 baseEnd_6574804 := by
    simpa [prefixWord, tailWord_6574804, baseEnd_6574804] using wordTrace_append hprefix tailTrace_6574804
  have hstable : (prefixWord ++ tailWord_6574804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6574804).length < 2 ^ (prefixWord ++ tailWord_6574804).sum := by decide
  have hdescent : baseEnd_6574804 < baseStart_6574804 := by decide
  rcases family_descends (prefixWord ++ tailWord_6574804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6574807 : List Nat := [1, 1, 3, 2, 1, 5, 1, 3, 1, 1, 4]
def baseStart_6574807 : Nat := 118140960795 + 6574807 * 2 ^ 59
def prefixEnd_6574807 : Nat := 4983230072969 + 3 ^ 40 * 6574807 * 2
def baseEnd_6574807 : Nat := 3376036201545562771075519

theorem tailTrace_6574807 : CollatzResearch.WordTrace tailWord_6574807 prefixEnd_6574807 3376036201545562771075519 := by
  unfold tailWord_6574807
  simp only [CollatzResearch.WordTrace]
  refine ⟨239802911891604601483058675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159868607927736400988705783 239802911891604601483058675)
  ·
    refine ⟨359704367837406902224588013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 239802911891604601483058675 359704367837406902224588013)
    ·
      refine ⟨134889137939027588334220505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 359704367837406902224588013 134889137939027588334220505)
      ·
        refine ⟨101166853454270691250665379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 134889137939027588334220505 101166853454270691250665379)
        ·
          refine ⟨151750280181406036875998069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101166853454270691250665379 151750280181406036875998069)
          ·
            refine ⟨14226588767006815957124819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 151750280181406036875998069 14226588767006815957124819)
            ·
              refine ⟨21339883150510223935687229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14226588767006815957124819 21339883150510223935687229)
              ·
                refine ⟨8002456181441333975882711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21339883150510223935687229 8002456181441333975882711)
                ·
                  refine ⟨12003684272162000963824067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8002456181441333975882711 12003684272162000963824067)
                  ·
                    refine ⟨18005526408243001445736101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12003684272162000963824067 18005526408243001445736101)
                    ·
                      refine ⟨3376036201545562771075519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18005526408243001445736101 3376036201545562771075519)
                      ·
                        rfl

theorem cell23_6574807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 1, 3, 1, 1, 4].length) (baseStart_6574807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6574807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6574807 prefixEnd_6574807 := by exact prefixLift 6574807
  have htrace : WordTrace (prefixWord ++ tailWord_6574807) baseStart_6574807 baseEnd_6574807 := by
    simpa [prefixWord, tailWord_6574807, baseEnd_6574807] using wordTrace_append hprefix tailTrace_6574807
  have hstable : (prefixWord ++ tailWord_6574807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6574807).length < 2 ^ (prefixWord ++ tailWord_6574807).sum := by decide
  have hdescent : baseEnd_6574807 < baseStart_6574807 := by decide
  rcases family_descends (prefixWord ++ tailWord_6574807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6574810 : List Nat := [3, 1, 1, 2, 2, 2, 2, 3, 1, 1, 5]
def baseStart_6574810 : Nat := 118140960795 + 6574810 * 2 ^ 59
def prefixEnd_6574810 : Nat := 4983230072969 + 3 ^ 40 * 6574810 * 2
def baseEnd_6574810 : Nat := 3376037741987526259338005

theorem tailTrace_6574810 : CollatzResearch.WordTrace tailWord_6574810 prefixEnd_6574810 3376037741987526259338005 := by
  unfold tailWord_6574810
  simp only [CollatzResearch.WordTrace]
  refine ⟨59950755327648433248854471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 159868680873729155330278589 59950755327648433248854471)
  ·
    refine ⟨89926132991472649873281707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59950755327648433248854471 89926132991472649873281707)
    ·
      refine ⟨134889199487208974809922561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89926132991472649873281707 134889199487208974809922561)
      ·
        refine ⟨101166899615406731107441921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 134889199487208974809922561 101166899615406731107441921)
        ·
          refine ⟨75875174711555048330581441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101166899615406731107441921 75875174711555048330581441)
          ·
            refine ⟨56906381033666286247936081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75875174711555048330581441 56906381033666286247936081)
            ·
              refine ⟨42679785775249714685952061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56906381033666286247936081 42679785775249714685952061)
              ·
                refine ⟨16004919665718643007232023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42679785775249714685952061 16004919665718643007232023)
                ·
                  refine ⟨24007379498577964510848035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16004919665718643007232023 24007379498577964510848035)
                  ·
                    refine ⟨36011069247866946766272053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24007379498577964510848035 36011069247866946766272053)
                    ·
                      refine ⟨3376037741987526259338005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36011069247866946766272053 3376037741987526259338005)
                      ·
                        rfl

theorem cell23_6574810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 2, 3, 1, 1, 5].length) (baseStart_6574810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6574810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6574810 prefixEnd_6574810 := by exact prefixLift 6574810
  have htrace : WordTrace (prefixWord ++ tailWord_6574810) baseStart_6574810 baseEnd_6574810 := by
    simpa [prefixWord, tailWord_6574810, baseEnd_6574810] using wordTrace_append hprefix tailTrace_6574810
  have hstable : (prefixWord ++ tailWord_6574810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6574810).length < 2 ^ (prefixWord ++ tailWord_6574810).sum := by decide
  have hdescent : baseEnd_6574810 < baseStart_6574810 := by decide
  rcases family_descends (prefixWord ++ tailWord_6574810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6574817 : List Nat := [1, 2, 3, 1, 4, 2, 1, 1, 4, 4]
def baseStart_6574817 : Nat := 118140960795 + 6574817 * 2 ^ 59
def prefixEnd_6574817 : Nat := 4983230072969 + 3 ^ 40 * 6574817 * 2
def baseEnd_6574817 : Nat := 1125347112117369243983491

theorem tailTrace_6574817 : CollatzResearch.WordTrace tailWord_6574817 prefixEnd_6574817 1125347112117369243983491 := by
  unfold tailWord_6574817
  simp only [CollatzResearch.WordTrace]
  refine ⟨239803276621568373190922705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159868851081045582127281803 239803276621568373190922705)
  ·
    refine ⟨179852457466176279893192029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 239803276621568373190922705 179852457466176279893192029)
    ·
      refine ⟨67444671549816104959947011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 179852457466176279893192029 67444671549816104959947011)
      ·
        refine ⟨101167007324724157439920517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67444671549816104959947011 101167007324724157439920517)
        ·
          refine ⟨18968813873385779519985097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 101167007324724157439920517 18968813873385779519985097)
          ·
            refine ⟨14226610405039334639988823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18968813873385779519985097 14226610405039334639988823)
            ·
              refine ⟨21339915607559001959983235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14226610405039334639988823 21339915607559001959983235)
              ·
                refine ⟨32009873411338502939974853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21339915607559001959983235 32009873411338502939974853)
                ·
                  refine ⟨6001851264625969301245285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32009873411338502939974853 6001851264625969301245285)
                  ·
                    refine ⟨1125347112117369243983491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6001851264625969301245285 1125347112117369243983491)
                    ·
                      rfl

theorem cell23_6574817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 1, 1, 4, 4].length) (baseStart_6574817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6574817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6574817 prefixEnd_6574817 := by exact prefixLift 6574817
  have htrace : WordTrace (prefixWord ++ tailWord_6574817) baseStart_6574817 baseEnd_6574817 := by
    simpa [prefixWord, tailWord_6574817, baseEnd_6574817] using wordTrace_append hprefix tailTrace_6574817
  have hstable : (prefixWord ++ tailWord_6574817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6574817).length < 2 ^ (prefixWord ++ tailWord_6574817).sum := by decide
  have hdescent : baseEnd_6574817 < baseStart_6574817 := by decide
  rcases family_descends (prefixWord ++ tailWord_6574817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6574843 : List Nat := [1, 1, 1, 1, 1, 3, 1, 2, 3, 9]
def baseStart_6574843 : Nat := 118140960795 + 6574843 * 2 ^ 59
def prefixEnd_6574843 : Nat := 4983230072969 + 3 ^ 40 * 6574843 * 2
def baseEnd_6574843 : Nat := 1125351562283041543408451

theorem tailTrace_6574843 : CollatzResearch.WordTrace tailWord_6574843 prefixEnd_6574843 1125351562283041543408451 := by
  unfold tailWord_6574843
  simp only [CollatzResearch.WordTrace]
  refine ⟨239804224919474179631369183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159869483279649453087579455 239804224919474179631369183)
  ·
    refine ⟨359706337379211269447053775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 239804224919474179631369183 359706337379211269447053775)
    ·
      refine ⟨539559506068816904170580663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 359706337379211269447053775 539559506068816904170580663)
      ·
        refine ⟨809339259103225356255870995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 539559506068816904170580663 809339259103225356255870995)
        ·
          refine ⟨1214008888654838034383806493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 809339259103225356255870995 1214008888654838034383806493)
          ·
            refine ⟨455253333245564262893927435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1214008888654838034383806493 455253333245564262893927435)
            ·
              refine ⟨682879999868346394340891153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 455253333245564262893927435 682879999868346394340891153)
              ·
                refine ⟨512159999901259795755668365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 682879999868346394340891153 512159999901259795755668365)
                ·
                  refine ⟨192059999962972423408375637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 512159999901259795755668365 192059999962972423408375637)
                  ·
                    refine ⟨1125351562283041543408451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 192059999962972423408375637 1125351562283041543408451)
                    ·
                      rfl

theorem cell23_6574843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 3, 9].length) (baseStart_6574843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6574843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6574843 prefixEnd_6574843 := by exact prefixLift 6574843
  have htrace : WordTrace (prefixWord ++ tailWord_6574843) baseStart_6574843 baseEnd_6574843 := by
    simpa [prefixWord, tailWord_6574843, baseEnd_6574843] using wordTrace_append hprefix tailTrace_6574843
  have hstable : (prefixWord ++ tailWord_6574843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6574843).length < 2 ^ (prefixWord ++ tailWord_6574843).sum := by decide
  have hdescent : baseEnd_6574843 < baseStart_6574843 := by decide
  rcases family_descends (prefixWord ++ tailWord_6574843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6574844 : List Nat := [2, 2, 2, 1, 3, 3, 2, 2, 1, 2, 3]
def baseStart_6574844 : Nat := 118140960795 + 6574844 * 2 ^ 59
def prefixEnd_6574844 : Nat := 4983230072969 + 3 ^ 40 * 6574844 * 2
def baseEnd_6574844 : Nat := 3376055200329779126312849

theorem tailTrace_6574844 : CollatzResearch.WordTrace tailWord_6574844 prefixEnd_6574844 3376055200329779126312849 := by
  unfold tailWord_6574844
  simp only [CollatzResearch.WordTrace]
  refine ⟨119902130696235278401077793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159869507594980371201437057 119902130696235278401077793)
  ·
    refine ⟨89926598022176458800808345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119902130696235278401077793 89926598022176458800808345)
    ·
      refine ⟨67444948516632344100606259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89926598022176458800808345 67444948516632344100606259)
      ·
        refine ⟨101167422774948516150909389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67444948516632344100606259 101167422774948516150909389)
        ·
          refine ⟨37937783540605693556591021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 101167422774948516150909389 37937783540605693556591021)
          ·
            refine ⟨14226668827727135083721633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37937783540605693556591021 14226668827727135083721633)
            ·
              refine ⟨10670001620795351312791225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14226668827727135083721633 10670001620795351312791225)
              ·
                refine ⟨8002501215596513484593419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10670001620795351312791225 8002501215596513484593419)
                ·
                  refine ⟨12003751823394770226890129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8002501215596513484593419 12003751823394770226890129)
                  ·
                    refine ⟨9002813867546077670167597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12003751823394770226890129 9002813867546077670167597)
                    ·
                      refine ⟨3376055200329779126312849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9002813867546077670167597 3376055200329779126312849)
                      ·
                        rfl

theorem cell23_6574844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 2, 2, 1, 2, 3].length) (baseStart_6574844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6574844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6574844 prefixEnd_6574844 := by exact prefixLift 6574844
  have htrace : WordTrace (prefixWord ++ tailWord_6574844) baseStart_6574844 baseEnd_6574844 := by
    simpa [prefixWord, tailWord_6574844, baseEnd_6574844] using wordTrace_append hprefix tailTrace_6574844
  have hstable : (prefixWord ++ tailWord_6574844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6574844).length < 2 ^ (prefixWord ++ tailWord_6574844).sum := by decide
  have hdescent : baseEnd_6574844 < baseStart_6574844 := by decide
  rcases family_descends (prefixWord ++ tailWord_6574844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6574857 : List Nat := [1, 2, 1, 1, 3, 2, 3, 2, 4, 1, 3]
def baseStart_6574857 : Nat := 118140960795 + 6574857 * 2 ^ 59
def prefixEnd_6574857 : Nat := 4983230072969 + 3 ^ 40 * 6574857 * 2
def baseEnd_6574857 : Nat := 3376061875578287575450289

theorem tailTrace_6574857 : CollatzResearch.WordTrace tailWord_6574857 prefixEnd_6574857 3376061875578287575450289 := by
  unfold tailWord_6574857
  simp only [CollatzResearch.WordTrace]
  refine ⟨239804735541423460022378825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159869823694282306681585883 239804735541423460022378825)
  ·
    refine ⟨179853551656067595016784119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 239804735541423460022378825 179853551656067595016784119)
    ·
      refine ⟨269780327484101392525176179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179853551656067595016784119 269780327484101392525176179)
      ·
        refine ⟨404670491226152088787764269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 269780327484101392525176179 404670491226152088787764269)
        ·
          refine ⟨151751434209807033295411601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 404670491226152088787764269 151751434209807033295411601)
          ·
            refine ⟨113813575657355274971558701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 151751434209807033295411601 113813575657355274971558701)
            ·
              refine ⟨42680090871508228114334513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 113813575657355274971558701 42680090871508228114334513)
              ·
                refine ⟨32010068153631171085750885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42680090871508228114334513 32010068153631171085750885)
                ·
                  refine ⟨6001887778805844578578291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32010068153631171085750885 6001887778805844578578291)
                  ·
                    refine ⟨9002831668208766867867437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6001887778805844578578291 9002831668208766867867437)
                    ·
                      refine ⟨3376061875578287575450289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9002831668208766867867437 3376061875578287575450289)
                      ·
                        rfl

theorem cell23_6574857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 3, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 3, 2, 4, 1, 3].length) (baseStart_6574857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6574857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6574857 prefixEnd_6574857 := by exact prefixLift 6574857
  have htrace : WordTrace (prefixWord ++ tailWord_6574857) baseStart_6574857 baseEnd_6574857 := by
    simpa [prefixWord, tailWord_6574857, baseEnd_6574857] using wordTrace_append hprefix tailTrace_6574857
  have hstable : (prefixWord ++ tailWord_6574857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6574857).length < 2 ^ (prefixWord ++ tailWord_6574857).sum := by decide
  have hdescent : baseEnd_6574857 < baseStart_6574857 := by decide
  rcases family_descends (prefixWord ++ tailWord_6574857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6574874 : List Nat := [3, 1, 1, 3, 2, 1, 2, 4, 2, 1, 3]
def baseStart_6574874 : Nat := 118140960795 + 6574874 * 2 ^ 59
def prefixEnd_6574874 : Nat := 4983230072969 + 3 ^ 40 * 6574874 * 2
def baseEnd_6574874 : Nat := 3376070604749414008937711

theorem tailTrace_6574874 : CollatzResearch.WordTrace tailWord_6574874 prefixEnd_6574874 3376070604749414008937711 := by
  unfold tailWord_6574874
  simp only [CollatzResearch.WordTrace]
  refine ⟨59951338895590467981436919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 159870237054907914617165117 59951338895590467981436919)
  ·
    refine ⟨89927008343385701972155379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59951338895590467981436919 89927008343385701972155379)
    ·
      refine ⟨134890512515078552958233069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89927008343385701972155379 134890512515078552958233069)
      ·
        refine ⟨50583942193154457359337401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 134890512515078552958233069 50583942193154457359337401)
        ·
          refine ⟨37937956644865843019503051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50583942193154457359337401 37937956644865843019503051)
          ·
            refine ⟨56906934967298764529254577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37937956644865843019503051 56906934967298764529254577)
            ·
              refine ⟨42680201225474073396940933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56906934967298764529254577 42680201225474073396940933)
              ·
                refine ⟨8002537729776388761926425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 42680201225474073396940933 8002537729776388761926425)
                ·
                  refine ⟨6001903297332291571444819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8002537729776388761926425 6001903297332291571444819)
                  ·
                    refine ⟨9002854945998437357167229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6001903297332291571444819 9002854945998437357167229)
                    ·
                      refine ⟨3376070604749414008937711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9002854945998437357167229 3376070604749414008937711)
                      ·
                        rfl

theorem cell23_6574874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 2, 4, 2, 1, 3].length) (baseStart_6574874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6574874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6574874 prefixEnd_6574874 := by exact prefixLift 6574874
  have htrace : WordTrace (prefixWord ++ tailWord_6574874) baseStart_6574874 baseEnd_6574874 := by
    simpa [prefixWord, tailWord_6574874, baseEnd_6574874] using wordTrace_append hprefix tailTrace_6574874
  have hstable : (prefixWord ++ tailWord_6574874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6574874).length < 2 ^ (prefixWord ++ tailWord_6574874).sum := by decide
  have hdescent : baseEnd_6574874 < baseStart_6574874 := by decide
  rcases family_descends (prefixWord ++ tailWord_6574874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6574901 : List Nat := [1, 3, 3, 1, 3, 1, 3, 2, 1, 3, 2]
def baseStart_6574901 : Nat := 118140960795 + 6574901 * 2 ^ 59
def prefixEnd_6574901 : Nat := 4983230072969 + 3 ^ 40 * 6574901 * 2
def baseEnd_6574901 : Nat := 3376084468727085403300087

theorem tailTrace_6574901 : CollatzResearch.WordTrace tailWord_6574901 prefixEnd_6574901 3376084468727085403300087 := by
  unfold tailWord_6574901
  simp only [CollatzResearch.WordTrace]
  refine ⟨239806340353264055536980557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159870893568842703691320371 239806340353264055536980557)
  ·
    refine ⟨89927377632474020826367709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 239806340353264055536980557 89927377632474020826367709)
    ·
      refine ⟨33722766612177757809887891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 89927377632474020826367709 33722766612177757809887891)
      ·
        refine ⟨50584149918266636714831837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33722766612177757809887891 50584149918266636714831837)
        ·
          refine ⟨18969056219349988768061939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50584149918266636714831837 18969056219349988768061939)
          ·
            refine ⟨28453584329024983152092909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18969056219349988768061939 28453584329024983152092909)
            ·
              refine ⟨10670094123384368682034841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28453584329024983152092909 10670094123384368682034841)
              ·
                refine ⟨8002570592538276511526131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10670094123384368682034841 8002570592538276511526131)
                ·
                  refine ⟨12003855888807414767289197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8002570592538276511526131 12003855888807414767289197)
                  ·
                    refine ⟨4501445958302780537733449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12003855888807414767289197 4501445958302780537733449)
                    ·
                      refine ⟨3376084468727085403300087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4501445958302780537733449 3376084468727085403300087)
                      ·
                        rfl

theorem cell23_6574901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 3, 2, 1, 3, 2].length) (baseStart_6574901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6574901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6574901 prefixEnd_6574901 := by exact prefixLift 6574901
  have htrace : WordTrace (prefixWord ++ tailWord_6574901) baseStart_6574901 baseEnd_6574901 := by
    simpa [prefixWord, tailWord_6574901, baseEnd_6574901] using wordTrace_append hprefix tailTrace_6574901
  have hstable : (prefixWord ++ tailWord_6574901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6574901).length < 2 ^ (prefixWord ++ tailWord_6574901).sum := by decide
  have hdescent : baseEnd_6574901 < baseStart_6574901 := by decide
  rcases family_descends (prefixWord ++ tailWord_6574901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6574947 : List Nat := [1, 1, 1, 5, 3, 1, 1, 1, 1, 5, 3]
def baseStart_6574947 : Nat := 118140960795 + 6574947 * 2 ^ 59
def prefixEnd_6574947 : Nat := 4983230072969 + 3 ^ 40 * 6574947 * 2
def baseEnd_6574947 : Nat := 3376108088837192223324875

theorem tailTrace_6574947 : CollatzResearch.WordTrace tailWord_6574947 prefixEnd_6574947 3376108088837192223324875 := by
  unfold tailWord_6574947
  simp only [CollatzResearch.WordTrace]
  refine ⟨239808018111097405393155095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159872012074064936928770063 239808018111097405393155095)
  ·
    refine ⟨359712027166646108089732643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 239808018111097405393155095 359712027166646108089732643)
    ·
      refine ⟨539568040749969162134598965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 359712027166646108089732643 539568040749969162134598965)
      ·
        refine ⟨50584503820309608950118653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 539568040749969162134598965 50584503820309608950118653)
        ·
          refine ⟨18969188932616103356294495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50584503820309608950118653 18969188932616103356294495)
          ·
            refine ⟨28453783398924155034441743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18969188932616103356294495 28453783398924155034441743)
            ·
              refine ⟨42680675098386232551662615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28453783398924155034441743 42680675098386232551662615)
              ·
                refine ⟨64021012647579348827493923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42680675098386232551662615 64021012647579348827493923)
                ·
                  refine ⟨96031518971369023241240885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 64021012647579348827493923 96031518971369023241240885)
                  ·
                    refine ⟨9002954903565845928866333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 96031518971369023241240885 9002954903565845928866333)
                    ·
                      refine ⟨3376108088837192223324875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9002954903565845928866333 3376108088837192223324875)
                      ·
                        rfl

theorem cell23_6574947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 1, 1, 1, 5, 3].length) (baseStart_6574947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6574947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6574947 prefixEnd_6574947 := by exact prefixLift 6574947
  have htrace : WordTrace (prefixWord ++ tailWord_6574947) baseStart_6574947 baseEnd_6574947 := by
    simpa [prefixWord, tailWord_6574947, baseEnd_6574947] using wordTrace_append hprefix tailTrace_6574947
  have hstable : (prefixWord ++ tailWord_6574947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6574947).length < 2 ^ (prefixWord ++ tailWord_6574947).sum := by decide
  have hdescent : baseEnd_6574947 < baseStart_6574947 := by decide
  rcases family_descends (prefixWord ++ tailWord_6574947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6574960 : List Nat := [2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 7]
def baseStart_6574960 : Nat := 118140960795 + 6574960 * 2 ^ 59
def prefixEnd_6574960 : Nat := 4983230072969 + 3 ^ 40 * 6574960 * 2
def baseEnd_6574960 : Nat := 3376114764085700672462315

theorem tailTrace_6574960 : CollatzResearch.WordTrace tailWord_6574960 prefixEnd_6574960 3376114764085700672462315 := by
  unfold tailWord_6574960
  simp only [CollatzResearch.WordTrace]
  refine ⟨119904246130025154306689167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159872328173366872408918889 119904246130025154306689167)
  ·
    refine ⟨179856369195037731460033751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119904246130025154306689167 179856369195037731460033751)
    ·
      refine ⟨269784553792556597190050627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179856369195037731460033751 269784553792556597190050627)
      ·
        refine ⟨404676830688834895785075941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 269784553792556597190050627 404676830688834895785075941)
        ·
          refine ⟨75876905754156542959701739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 404676830688834895785075941 75876905754156542959701739)
          ·
            refine ⟨113815358631234814439552609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75876905754156542959701739 113815358631234814439552609)
            ·
              refine ⟨85361518973426110829664457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 113815358631234814439552609 85361518973426110829664457)
              ·
                refine ⟨64021139230069583122248343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 85361518973426110829664457 64021139230069583122248343)
                ·
                  refine ⟨96031708845104374683372515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 64021139230069583122248343 96031708845104374683372515)
                  ·
                    refine ⟨144047563267656562025058773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 96031708845104374683372515 144047563267656562025058773)
                    ·
                      refine ⟨3376114764085700672462315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 144047563267656562025058773 3376114764085700672462315)
                      ·
                        rfl

theorem cell23_6574960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 7].length) (baseStart_6574960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6574960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6574960 prefixEnd_6574960 := by exact prefixLift 6574960
  have htrace : WordTrace (prefixWord ++ tailWord_6574960) baseStart_6574960 baseEnd_6574960 := by
    simpa [prefixWord, tailWord_6574960, baseEnd_6574960] using wordTrace_append hprefix tailTrace_6574960
  have hstable : (prefixWord ++ tailWord_6574960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6574960).length < 2 ^ (prefixWord ++ tailWord_6574960).sum := by decide
  have hdescent : baseEnd_6574960 < baseStart_6574960 := by decide
  rcases family_descends (prefixWord ++ tailWord_6574960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6574987 : List Nat := [1, 1, 1, 1, 4, 2, 2, 4, 2, 1, 4]
def baseStart_6574987 : Nat := 118140960795 + 6574987 * 2 ^ 59
def prefixEnd_6574987 : Nat := 4983230072969 + 3 ^ 40 * 6574987 * 2
def baseEnd_6574987 : Nat := 3376128628063372066824691

theorem tailTrace_6574987 : CollatzResearch.WordTrace tailWord_6574987 prefixEnd_6574987 3376128628063372066824691 := by
  unfold tailWord_6574987
  simp only [CollatzResearch.WordTrace]
  refine ⟨239809477030952492224611215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159872984687301661483074143 239809477030952492224611215)
  ·
    refine ⟨359714215546428738336916823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 239809477030952492224611215 359714215546428738336916823)
    ·
      refine ⟨539571323319643107505375235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 359714215546428738336916823 539571323319643107505375235)
      ·
        refine ⟨809356984979464661258062853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 539571323319643107505375235 809356984979464661258062853)
        ·
          refine ⟨151754434683649623985886785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 809356984979464661258062853 151754434683649623985886785)
          ·
            refine ⟨113815826012737217989415089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 151754434683649623985886785 113815826012737217989415089)
            ·
              refine ⟨85361869509552913492061317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 113815826012737217989415089 85361869509552913492061317)
              ·
                refine ⟨16005350533041171279761497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 85361869509552913492061317 16005350533041171279761497)
                ·
                  refine ⟨12004012899780878459821123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16005350533041171279761497 12004012899780878459821123)
                  ·
                    refine ⟨18006019349671317689731685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12004012899780878459821123 18006019349671317689731685)
                    ·
                      refine ⟨3376128628063372066824691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18006019349671317689731685 3376128628063372066824691)
                      ·
                        rfl

theorem cell23_6574987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 4, 2, 1, 4].length) (baseStart_6574987 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6574987 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6574987 prefixEnd_6574987 := by exact prefixLift 6574987
  have htrace : WordTrace (prefixWord ++ tailWord_6574987) baseStart_6574987 baseEnd_6574987 := by
    simpa [prefixWord, tailWord_6574987, baseEnd_6574987] using wordTrace_append hprefix tailTrace_6574987
  have hstable : (prefixWord ++ tailWord_6574987).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6574987).length < 2 ^ (prefixWord ++ tailWord_6574987).sum := by decide
  have hdescent : baseEnd_6574987 < baseStart_6574987 := by decide
  rcases family_descends (prefixWord ++ tailWord_6574987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6574998 : List Nat := [5, 3, 1, 1, 1, 1, 2, 1, 2, 3, 3]
def baseStart_6574998 : Nat := 118140960795 + 6574998 * 2 ^ 59
def prefixEnd_6574998 : Nat := 4983230072969 + 3 ^ 40 * 6574998 * 2
def baseEnd_6574998 : Nat := 3376134276350571523787141

theorem tailTrace_6574998 : CollatzResearch.WordTrace tailWord_6574998 prefixEnd_6574998 3376134276350571523787141 := by
  unfold tailWord_6574998
  simp only [CollatzResearch.WordTrace]
  refine ⟨14988117389619540068953853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 159873252155941760735507765 14988117389619540068953853)
  ·
    refine ⟨5620544021107327525857695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14988117389619540068953853 5620544021107327525857695)
    ·
      refine ⟨8430816031660991288786543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5620544021107327525857695 8430816031660991288786543)
      ·
        refine ⟨12646224047491486933179815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8430816031660991288786543 12646224047491486933179815)
        ·
          refine ⟨18969336071237230399769723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12646224047491486933179815 18969336071237230399769723)
          ·
            refine ⟨28454004106855845599654585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18969336071237230399769723 28454004106855845599654585)
            ·
              refine ⟨21340503080141884199740939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28454004106855845599654585 21340503080141884199740939)
              ·
                refine ⟨32010754620212826299611409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21340503080141884199740939 32010754620212826299611409)
                ·
                  refine ⟨24008065965159619724708557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32010754620212826299611409 24008065965159619724708557)
                  ·
                    refine ⟨9003024736934857396765709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24008065965159619724708557 9003024736934857396765709)
                    ·
                      refine ⟨3376134276350571523787141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9003024736934857396765709 3376134276350571523787141)
                      ·
                        rfl

theorem cell23_6574998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 2, 1, 2, 3, 3].length) (baseStart_6574998 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6574998 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6574998 prefixEnd_6574998 := by exact prefixLift 6574998
  have htrace : WordTrace (prefixWord ++ tailWord_6574998) baseStart_6574998 baseEnd_6574998 := by
    simpa [prefixWord, tailWord_6574998, baseEnd_6574998] using wordTrace_append hprefix tailTrace_6574998
  have hstable : (prefixWord ++ tailWord_6574998).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6574998).length < 2 ^ (prefixWord ++ tailWord_6574998).sum := by decide
  have hdescent : baseEnd_6574998 < baseStart_6574998 := by decide
  rcases family_descends (prefixWord ++ tailWord_6574998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6575031 : List Nat := [1, 1, 3, 1, 3, 1, 5, 3, 1, 4]
def baseStart_6575031 : Nat := 118140960795 + 6575031 * 2 ^ 59
def prefixEnd_6575031 : Nat := 4983230072969 + 3 ^ 40 * 6575031 * 2
def baseEnd_6575031 : Nat := 1125383740404056631558163

theorem tailTrace_6575031 : CollatzResearch.WordTrace tailWord_6575031 prefixEnd_6575031 1125383740404056631558163 := by
  unfold tailWord_6575031
  simp only [CollatzResearch.WordTrace]
  refine ⟨239811081842793087739212947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159874054561862058492808631 239811081842793087739212947)
  ·
    refine ⟨359716622764189631608819421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 239811081842793087739212947 359716622764189631608819421)
    ·
      refine ⟨134893733536571111853307283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 359716622764189631608819421 134893733536571111853307283)
      ·
        refine ⟨202340600304856667779960925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134893733536571111853307283 202340600304856667779960925)
        ·
          refine ⟨75877725114321250417485347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 202340600304856667779960925 75877725114321250417485347)
          ·
            refine ⟨113816587671481875626228021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75877725114321250417485347 113816587671481875626228021)
            ·
              refine ⟨10670305094201425839958877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 113816587671481875626228021 10670305094201425839958877)
              ·
                refine ⟨4001364410325534689984579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10670305094201425839958877 4001364410325534689984579)
                ·
                  refine ⟨6002046615488302034976869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4001364410325534689984579 6002046615488302034976869)
                  ·
                    refine ⟨1125383740404056631558163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6002046615488302034976869 1125383740404056631558163)
                    ·
                      rfl

theorem cell23_6575031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 5, 3, 1, 4].length) (baseStart_6575031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6575031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6575031 prefixEnd_6575031 := by exact prefixLift 6575031
  have htrace : WordTrace (prefixWord ++ tailWord_6575031) baseStart_6575031 baseEnd_6575031 := by
    simpa [prefixWord, tailWord_6575031, baseEnd_6575031] using wordTrace_append hprefix tailTrace_6575031
  have hstable : (prefixWord ++ tailWord_6575031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6575031).length < 2 ^ (prefixWord ++ tailWord_6575031).sum := by decide
  have hdescent : baseEnd_6575031 < baseStart_6575031 := by decide
  rcases family_descends (prefixWord ++ tailWord_6575031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6575048 : List Nat := [2, 1, 3, 1, 6, 1, 1, 1, 3, 4]
def baseStart_6575048 : Nat := 118140960795 + 6575048 * 2 ^ 59
def prefixEnd_6575048 : Nat := 4983230072969 + 3 ^ 40 * 6575048 * 2
def baseEnd_6575048 : Nat := 1125386650127765442720637

theorem tailTrace_6575048 : CollatzResearch.WordTrace tailWord_6575048 prefixEnd_6575048 1125386650127765442720637 := by
  unfold tailWord_6575048
  simp only [CollatzResearch.WordTrace]
  refine ⟨119905850941865749821290899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159874467922487666428387865 119905850941865749821290899)
  ·
    refine ⟨179858776412798624731936349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119905850941865749821290899 179858776412798624731936349)
    ·
      refine ⟨67447041154799484274476131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 179858776412798624731936349 67447041154799484274476131)
      ·
        refine ⟨101170561732199226411714197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67447041154799484274476131 101170561732199226411714197)
        ·
          refine ⟨4742370081196838738049103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 101170561732199226411714197 4742370081196838738049103)
          ·
            refine ⟨7113555121795258107073655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4742370081196838738049103 7113555121795258107073655)
            ·
              refine ⟨10670332682692887160610483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7113555121795258107073655 10670332682692887160610483)
              ·
                refine ⟨16005499024039330740915725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10670332682692887160610483 16005499024039330740915725)
                ·
                  refine ⟨6002062134014749027843397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16005499024039330740915725 6002062134014749027843397)
                  ·
                    refine ⟨1125386650127765442720637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6002062134014749027843397 1125386650127765442720637)
                    ·
                      rfl

theorem cell23_6575048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 6, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 6, 1, 1, 1, 3, 4].length) (baseStart_6575048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6575048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6575048 prefixEnd_6575048 := by exact prefixLift 6575048
  have htrace : WordTrace (prefixWord ++ tailWord_6575048) baseStart_6575048 baseEnd_6575048 := by
    simpa [prefixWord, tailWord_6575048, baseEnd_6575048] using wordTrace_append hprefix tailTrace_6575048
  have hstable : (prefixWord ++ tailWord_6575048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6575048).length < 2 ^ (prefixWord ++ tailWord_6575048).sum := by decide
  have hdescent : baseEnd_6575048 < baseStart_6575048 := by decide
  rcases family_descends (prefixWord ++ tailWord_6575048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6575057 : List Nat := [1, 2, 2, 1, 2, 1, 4, 2, 3, 5]
def baseStart_6575057 : Nat := 118140960795 + 6575057 * 2 ^ 59
def prefixEnd_6575057 : Nat := 4983230072969 + 3 ^ 40 * 6575057 * 2
def baseEnd_6575057 : Nat := 1125388190569728930983123

theorem tailTrace_6575057 : CollatzResearch.WordTrace tailWord_6575057 prefixEnd_6575057 1125388190569728930983123 := by
  unfold tailWord_6575057
  simp only [CollatzResearch.WordTrace]
  refine ⟨239812030140698894179659425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159874686760465929453106283 239812030140698894179659425)
  ·
    refine ⟨179859022605524170634744569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 239812030140698894179659425 179859022605524170634744569)
    ·
      refine ⟨134894266954143127976058427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 179859022605524170634744569 134894266954143127976058427)
      ·
        refine ⟨202341400431214691964087641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134894266954143127976058427 202341400431214691964087641)
        ·
          refine ⟨151756050323411018973065731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 202341400431214691964087641 151756050323411018973065731)
          ·
            refine ⟨227634075485116528459598597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 151756050323411018973065731 227634075485116528459598597)
            ·
              refine ⟨42681389153459349086174737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 227634075485116528459598597 42681389153459349086174737)
              ·
                refine ⟨32011041865094511814631053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42681389153459349086174737 32011041865094511814631053)
                ·
                  refine ⟨12004140699410441930486645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32011041865094511814631053 12004140699410441930486645)
                  ·
                    refine ⟨1125388190569728930983123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12004140699410441930486645 1125388190569728930983123)
                    ·
                      rfl

theorem cell23_6575057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 4, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 4, 2, 3, 5].length) (baseStart_6575057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6575057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6575057 prefixEnd_6575057 := by exact prefixLift 6575057
  have htrace : WordTrace (prefixWord ++ tailWord_6575057) baseStart_6575057 baseEnd_6575057 := by
    simpa [prefixWord, tailWord_6575057, baseEnd_6575057] using wordTrace_append hprefix tailTrace_6575057
  have hstable : (prefixWord ++ tailWord_6575057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6575057).length < 2 ^ (prefixWord ++ tailWord_6575057).sum := by decide
  have hdescent : baseEnd_6575057 < baseStart_6575057 := by decide
  rcases family_descends (prefixWord ++ tailWord_6575057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6575087 : List Nat := [1, 1, 2, 1, 4, 3, 1, 1, 3, 6]
def baseStart_6575087 : Nat := 118140960795 + 6575087 * 2 ^ 59
def prefixEnd_6575087 : Nat := 4983230072969 + 3 ^ 40 * 6575087 * 2
def baseEnd_6575087 : Nat := 1125393325376273891858077

theorem tailTrace_6575087 : CollatzResearch.WordTrace tailWord_6575087 prefixEnd_6575087 1125393325376273891858077 := by
  unfold tailWord_6575087
  simp only [CollatzResearch.WordTrace]
  refine ⟨239813124330590209303251515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159875416220393472868834343 239813124330590209303251515)
  ·
    refine ⟨359719686495885313954877273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 239813124330590209303251515 359719686495885313954877273)
    ·
      refine ⟨269789764871913985466157955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 359719686495885313954877273 269789764871913985466157955)
      ·
        refine ⟨404684647307870978199236933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 269789764871913985466157955 404684647307870978199236933)
        ·
          refine ⟨75878371370225808412356925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 404684647307870978199236933 75878371370225808412356925)
          ·
            refine ⟨28454389263834678154633847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 75878371370225808412356925 28454389263834678154633847)
            ·
              refine ⟨42681583895752017231950771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28454389263834678154633847 42681583895752017231950771)
              ·
                refine ⟨64022375843628025847926157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42681583895752017231950771 64022375843628025847926157)
                ·
                  refine ⟨24008390941360509692972309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 64022375843628025847926157 24008390941360509692972309)
                  ·
                    refine ⟨1125393325376273891858077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24008390941360509692972309 1125393325376273891858077)
                    ·
                      rfl

theorem cell23_6575087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 1, 1, 3, 6].length) (baseStart_6575087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6575087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6575087 prefixEnd_6575087 := by exact prefixLift 6575087
  have htrace : WordTrace (prefixWord ++ tailWord_6575087) baseStart_6575087 baseEnd_6575087 := by
    simpa [prefixWord, tailWord_6575087, baseEnd_6575087] using wordTrace_append hprefix tailTrace_6575087
  have hstable : (prefixWord ++ tailWord_6575087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6575087).length < 2 ^ (prefixWord ++ tailWord_6575087).sum := by decide
  have hdescent : baseEnd_6575087 < baseStart_6575087 := by decide
  rcases family_descends (prefixWord ++ tailWord_6575087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6575105 : List Nat := [1, 2, 4, 1, 2, 2, 4, 2, 1, 1, 3]
def baseStart_6575105 : Nat := 118140960795 + 6575105 * 2 ^ 59
def prefixEnd_6575105 : Nat := 4983230072969 + 3 ^ 40 * 6575105 * 2
def baseEnd_6575105 : Nat := 3376189218780602605149149

theorem tailTrace_6575105 : CollatzResearch.WordTrace tailWord_6575105 prefixEnd_6575105 3376189218780602605149149 := by
  unfold tailWord_6575105
  simp only [CollatzResearch.WordTrace]
  refine ⟨239813780844524998377406769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159875853896349998918271179 239813780844524998377406769)
  ·
    refine ⟨179860335633393748783055077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 239813780844524998377406769 179860335633393748783055077)
    ·
      refine ⟨33723812931261327896822827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 179860335633393748783055077 33723812931261327896822827)
      ·
        refine ⟨50585719396891991845234241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33723812931261327896822827 50585719396891991845234241)
        ·
          refine ⟨37939289547668993883925681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50585719396891991845234241 37939289547668993883925681)
          ·
            refine ⟨28454467160751745412944261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37939289547668993883925681 28454467160751745412944261)
            ·
              refine ⟨5335212592640952264927049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28454467160751745412944261 5335212592640952264927049)
              ·
                refine ⟨4001409444480714198695287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5335212592640952264927049 4001409444480714198695287)
                ·
                  refine ⟨6002114166721071298042931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4001409444480714198695287 6002114166721071298042931)
                  ·
                    refine ⟨9003171250081606947064397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6002114166721071298042931 9003171250081606947064397)
                    ·
                      refine ⟨3376189218780602605149149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9003171250081606947064397 3376189218780602605149149)
                      ·
                        rfl

theorem cell23_6575105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 4, 2, 1, 1, 3].length) (baseStart_6575105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6575105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6575105 prefixEnd_6575105 := by exact prefixLift 6575105
  have htrace : WordTrace (prefixWord ++ tailWord_6575105) baseStart_6575105 baseEnd_6575105 := by
    simpa [prefixWord, tailWord_6575105, baseEnd_6575105] using wordTrace_append hprefix tailTrace_6575105
  have hstable : (prefixWord ++ tailWord_6575105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6575105).length < 2 ^ (prefixWord ++ tailWord_6575105).sum := by decide
  have hdescent : baseEnd_6575105 < baseStart_6575105 := by decide
  rcases family_descends (prefixWord ++ tailWord_6575105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6575122 : List Nat := [3, 2, 5, 1, 1, 1, 1, 2, 3, 1, 3]
def baseStart_6575122 : Nat := 118140960795 + 6575122 * 2 ^ 59
def prefixEnd_6575122 : Nat := 4983230072969 + 3 ^ 40 * 6575122 * 2
def baseEnd_6575122 : Nat := 3376197947951729038636571

theorem tailTrace_6575122 : CollatzResearch.WordTrace tailWord_6575122 prefixEnd_6575122 3376197947951729038636571 := by
  unfold tailWord_6575122
  simp only [CollatzResearch.WordTrace]
  refine ⟨59953600221365852570193905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 159876267256975606853850413 59953600221365852570193905)
  ·
    refine ⟨44965200166024389427645429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59953600221365852570193905 44965200166024389427645429)
    ·
      refine ⟨4215487515564786508841759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 44965200166024389427645429 4215487515564786508841759)
      ·
        refine ⟨6323231273347179763262639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4215487515564786508841759 6323231273347179763262639)
        ·
          refine ⟨9484846910020769644893959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6323231273347179763262639 9484846910020769644893959)
          ·
            refine ⟨14227270365031154467340939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9484846910020769644893959 14227270365031154467340939)
            ·
              refine ⟨21340905547546731701011409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14227270365031154467340939 21340905547546731701011409)
              ·
                refine ⟨16005679160660048775758557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21340905547546731701011409 16005679160660048775758557)
                ·
                  refine ⟨6002129685247518290909459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16005679160660048775758557 6002129685247518290909459)
                  ·
                    refine ⟨9003194527871277436364189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6002129685247518290909459 9003194527871277436364189)
                    ·
                      refine ⟨3376197947951729038636571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9003194527871277436364189 3376197947951729038636571)
                      ·
                        rfl

theorem cell23_6575122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 1, 2, 3, 1, 3].length) (baseStart_6575122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6575122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6575122 prefixEnd_6575122 := by exact prefixLift 6575122
  have htrace : WordTrace (prefixWord ++ tailWord_6575122) baseStart_6575122 baseEnd_6575122 := by
    simpa [prefixWord, tailWord_6575122, baseEnd_6575122] using wordTrace_append hprefix tailTrace_6575122
  have hstable : (prefixWord ++ tailWord_6575122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6575122).length < 2 ^ (prefixWord ++ tailWord_6575122).sum := by decide
  have hdescent : baseEnd_6575122 < baseStart_6575122 := by decide
  rcases family_descends (prefixWord ++ tailWord_6575122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6575128 : List Nat := [2, 1, 2, 3, 2, 3, 1, 2, 3, 2, 2]
def baseStart_6575128 : Nat := 118140960795 + 6575128 * 2 ^ 59
def prefixEnd_6575128 : Nat := 4983230072969 + 3 ^ 40 * 6575128 * 2
def baseEnd_6575128 : Nat := 3376201028835656015161543

theorem tailTrace_6575128 : CollatzResearch.WordTrace tailWord_6575128 prefixEnd_6575128 3376201028835656015161543 := by
  unfold tailWord_6575128
  simp only [CollatzResearch.WordTrace]
  refine ⟨119907309861720836652747019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159876413148961115536996025 119907309861720836652747019)
  ·
    refine ⟨179860964792581254979120529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119907309861720836652747019 179860964792581254979120529)
    ·
      refine ⟨134895723594435941234340397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 179860964792581254979120529 134895723594435941234340397)
      ·
        refine ⟨50585896347913477962877649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 134895723594435941234340397 50585896347913477962877649)
        ·
          refine ⟨37939422260935108472158237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50585896347913477962877649 37939422260935108472158237)
          ·
            refine ⟨14227283347850665677059339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37939422260935108472158237 14227283347850665677059339)
            ·
              refine ⟨21340925021775998515589009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14227283347850665677059339 21340925021775998515589009)
              ·
                refine ⟨16005693766331998886691757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21340925021775998515589009 16005693766331998886691757)
                ·
                  refine ⟨6002135162374499582509409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16005693766331998886691757 6002135162374499582509409)
                  ·
                    refine ⟨4501601371780874686882057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6002135162374499582509409 4501601371780874686882057)
                    ·
                      refine ⟨3376201028835656015161543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4501601371780874686882057 3376201028835656015161543)
                      ·
                        rfl

theorem cell23_6575128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 1, 2, 3, 2, 2].length) (baseStart_6575128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6575128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6575128 prefixEnd_6575128 := by exact prefixLift 6575128
  have htrace : WordTrace (prefixWord ++ tailWord_6575128) baseStart_6575128 baseEnd_6575128 := by
    simpa [prefixWord, tailWord_6575128, baseEnd_6575128] using wordTrace_append hprefix tailTrace_6575128
  have hstable : (prefixWord ++ tailWord_6575128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6575128).length < 2 ^ (prefixWord ++ tailWord_6575128).sum := by decide
  have hdescent : baseEnd_6575128 < baseStart_6575128 := by decide
  rcases family_descends (prefixWord ++ tailWord_6575128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6575177 : List Nat := [1, 2, 1, 1, 2, 2, 2, 3, 1, 8]
def baseStart_6575177 : Nat := 118140960795 + 6575177 * 2 ^ 59
def prefixEnd_6575177 : Nat := 4983230072969 + 3 ^ 40 * 6575177 * 2
def baseEnd_6575177 : Nat := 1125408729795908774482939

theorem tailTrace_6575177 : CollatzResearch.WordTrace tailWord_6575177 prefixEnd_6575177 1125408729795908774482939 := by
  unfold tailWord_6575177
  simp only [CollatzResearch.WordTrace]
  refine ⟨239816406900264154674027785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159877604600176103116018523 239816406900264154674027785)
  ·
    refine ⟨179862305175198116005520839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 239816406900264154674027785 179862305175198116005520839)
    ·
      refine ⟨269793457762797174008281259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179862305175198116005520839 269793457762797174008281259)
      ·
        refine ⟨404690186644195761012421889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 269793457762797174008281259 404690186644195761012421889)
        ·
          refine ⟨303517639983146820759316417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 404690186644195761012421889 303517639983146820759316417)
          ·
            refine ⟨227638229987360115569487313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 303517639983146820759316417 227638229987360115569487313)
            ·
              refine ⟨170728672490520086677115485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 227638229987360115569487313 170728672490520086677115485)
              ·
                refine ⟨64023252183945032503918307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 170728672490520086677115485 64023252183945032503918307)
                ·
                  refine ⟨96034878275917548755877461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 64023252183945032503918307 96034878275917548755877461)
                  ·
                    refine ⟨1125408729795908774482939, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 96034878275917548755877461 1125408729795908774482939)
                    ·
                      rfl

theorem cell23_6575177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 3, 1, 8].length) (baseStart_6575177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6575177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6575177 prefixEnd_6575177 := by exact prefixLift 6575177
  have htrace : WordTrace (prefixWord ++ tailWord_6575177) baseStart_6575177 baseEnd_6575177 := by
    simpa [prefixWord, tailWord_6575177, baseEnd_6575177] using wordTrace_append hprefix tailTrace_6575177
  have hstable : (prefixWord ++ tailWord_6575177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6575177).length < 2 ^ (prefixWord ++ tailWord_6575177).sum := by decide
  have hdescent : baseEnd_6575177 < baseStart_6575177 := by decide
  rcases family_descends (prefixWord ++ tailWord_6575177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6575188 : List Nat := [2, 4, 1, 1, 1, 1, 3, 4, 1, 3, 2]
def baseStart_6575188 : Nat := 118140960795 + 6575188 * 2 ^ 59
def prefixEnd_6575188 : Nat := 4983230072969 + 3 ^ 40 * 6575188 * 2
def baseEnd_6575188 : Nat := 3376231837674925780411267

theorem tailTrace_6575188 : CollatzResearch.WordTrace tailWord_6575188 prefixEnd_6575188 3376231837674925780411267 := by
  unfold tailWord_6575188
  simp only [CollatzResearch.WordTrace]
  refine ⟨119908404051612151776339109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159877872068816202368452145 119908404051612151776339109)
  ·
    refine ⟨22482825759677278458063583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 119908404051612151776339109 22482825759677278458063583)
    ·
      refine ⟨33724238639515917687095375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22482825759677278458063583 33724238639515917687095375)
      ·
        refine ⟨50586357959273876530643063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33724238639515917687095375 50586357959273876530643063)
        ·
          refine ⟨75879536938910814795964595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50586357959273876530643063 75879536938910814795964595)
          ·
            refine ⟨113819305408366222193946893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75879536938910814795964595 113819305408366222193946893)
            ·
              refine ⟨42682239528137333322730085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 113819305408366222193946893 42682239528137333322730085)
              ·
                refine ⟨8002919911525749998011891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 42682239528137333322730085 8002919911525749998011891)
                ·
                  refine ⟨12004379867288624997017837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8002919911525749998011891 12004379867288624997017837)
                  ·
                    refine ⟨4501642450233234373881689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12004379867288624997017837 4501642450233234373881689)
                    ·
                      refine ⟨3376231837674925780411267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4501642450233234373881689 3376231837674925780411267)
                      ·
                        rfl

theorem cell23_6575188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 3, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 3, 4, 1, 3, 2].length) (baseStart_6575188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6575188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6575188 prefixEnd_6575188 := by exact prefixLift 6575188
  have htrace : WordTrace (prefixWord ++ tailWord_6575188) baseStart_6575188 baseEnd_6575188 := by
    simpa [prefixWord, tailWord_6575188, baseEnd_6575188] using wordTrace_append hprefix tailTrace_6575188
  have hstable : (prefixWord ++ tailWord_6575188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6575188).length < 2 ^ (prefixWord ++ tailWord_6575188).sum := by decide
  have hdescent : baseEnd_6575188 < baseStart_6575188 := by decide
  rcases family_descends (prefixWord ++ tailWord_6575188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6575201 : List Nat := [1, 2, 3, 1, 1, 2, 2, 4, 1, 4, 2]
def baseStart_6575201 : Nat := 118140960795 + 6575201 * 2 ^ 59
def prefixEnd_6575201 : Nat := 4983230072969 + 3 ^ 40 * 6575201 * 2
def baseEnd_6575201 : Nat := 3376238512923434229548707

theorem tailTrace_6575201 : CollatzResearch.WordTrace tailWord_6575201 prefixEnd_6575201 3376238512923434229548707 := by
  unfold tailWord_6575201
  simp only [CollatzResearch.WordTrace]
  refine ⟨239817282252177206772901457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159878188168118137848600971 239817282252177206772901457)
  ·
    refine ⟨179862961689132905079676093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 239817282252177206772901457 179862961689132905079676093)
    ·
      refine ⟨67448610633424839404878535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 179862961689132905079676093 67448610633424839404878535)
      ·
        refine ⟨101172915950137259107317803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67448610633424839404878535 101172915950137259107317803)
        ·
          refine ⟨151759373925205888660976705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101172915950137259107317803 151759373925205888660976705)
          ·
            refine ⟨113819530443904416495732529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 151759373925205888660976705 113819530443904416495732529)
            ·
              refine ⟨85364647832928312371799397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 113819530443904416495732529 85364647832928312371799397)
              ·
                refine ⟨16005871468674058569712387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 85364647832928312371799397 16005871468674058569712387)
                ·
                  refine ⟨24008807203011087854568581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16005871468674058569712387 24008807203011087854568581)
                  ·
                    refine ⟨4501651350564578972731609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24008807203011087854568581 4501651350564578972731609)
                    ·
                      refine ⟨3376238512923434229548707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4501651350564578972731609 3376238512923434229548707)
                      ·
                        rfl

theorem cell23_6575201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 4, 1, 4, 2].length) (baseStart_6575201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6575201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6575201 prefixEnd_6575201 := by exact prefixLift 6575201
  have htrace : WordTrace (prefixWord ++ tailWord_6575201) baseStart_6575201 baseEnd_6575201 := by
    simpa [prefixWord, tailWord_6575201, baseEnd_6575201] using wordTrace_append hprefix tailTrace_6575201
  have hstable : (prefixWord ++ tailWord_6575201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6575201).length < 2 ^ (prefixWord ++ tailWord_6575201).sum := by decide
  have hdescent : baseEnd_6575201 < baseStart_6575201 := by decide
  rcases family_descends (prefixWord ++ tailWord_6575201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6575204 : List Nat := [2, 3, 1, 1, 2, 1, 1, 2, 1, 6, 3]
def baseStart_6575204 : Nat := 118140960795 + 6575204 * 2 ^ 59
def prefixEnd_6575204 : Nat := 4983230072969 + 3 ^ 40 * 6575204 * 2
def baseEnd_6575204 : Nat := 3376240053365397717811193

theorem tailTrace_6575204 : CollatzResearch.WordTrace tailWord_6575204 prefixEnd_6575204 3376240053365397717811193 := by
  unfold tailWord_6575204
  simp only [CollatzResearch.WordTrace]
  refine ⟨119908695835583169142630333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159878261114110892190173777 119908695835583169142630333)
  ·
    refine ⟨44965760938343688428486375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 119908695835583169142630333 44965760938343688428486375)
    ·
      refine ⟨67448641407515532642729563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44965760938343688428486375 67448641407515532642729563)
      ·
        refine ⟨101172962111273298964094345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67448641407515532642729563 101172962111273298964094345)
        ·
          refine ⟨75879721583454974223070759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101172962111273298964094345 75879721583454974223070759)
          ·
            refine ⟨113819582375182461334606139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75879721583454974223070759 113819582375182461334606139)
            ·
              refine ⟨170729373562773692001909209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 113819582375182461334606139 170729373562773692001909209)
              ·
                refine ⟨128047030172080269001431907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 170729373562773692001909209 128047030172080269001431907)
                ·
                  refine ⟨192070545258120403502147861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 128047030172080269001431907 192070545258120403502147861)
                  ·
                    refine ⟨9003306808974393914163181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 192070545258120403502147861 9003306808974393914163181)
                    ·
                      refine ⟨3376240053365397717811193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9003306808974393914163181 3376240053365397717811193)
                      ·
                        rfl

theorem cell23_6575204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 2, 1, 6, 3].length) (baseStart_6575204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6575204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6575204 prefixEnd_6575204 := by exact prefixLift 6575204
  have htrace : WordTrace (prefixWord ++ tailWord_6575204) baseStart_6575204 baseEnd_6575204 := by
    simpa [prefixWord, tailWord_6575204, baseEnd_6575204] using wordTrace_append hprefix tailTrace_6575204
  have hstable : (prefixWord ++ tailWord_6575204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6575204).length < 2 ^ (prefixWord ++ tailWord_6575204).sum := by decide
  have hdescent : baseEnd_6575204 < baseStart_6575204 := by decide
  rcases family_descends (prefixWord ++ tailWord_6575204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6575218 : List Nat := [3, 2, 1, 2, 2, 1, 1, 3, 4, 2, 2]
def baseStart_6575218 : Nat := 118140960795 + 6575218 * 2 ^ 59
def prefixEnd_6575218 : Nat := 4983230072969 + 3 ^ 40 * 6575218 * 2
def baseEnd_6575218 : Nat := 3376247242094560663036129

theorem tailTrace_6575218 : CollatzResearch.WordTrace tailWord_6575218 prefixEnd_6575218 3376247242094560663036129 := by
  unfold tailWord_6575218
  simp only [CollatzResearch.WordTrace]
  refine ⟨59954475573278904669067577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 159878601528743745784180205 59954475573278904669067577)
  ·
    refine ⟨44965856679959178501800683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59954475573278904669067577 44965856679959178501800683)
    ·
      refine ⟨67448785019938767752701025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44965856679959178501800683 67448785019938767752701025)
      ·
        refine ⟨50586588764954075814525769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67448785019938767752701025 50586588764954075814525769)
        ·
          refine ⟨37939941573715556860894327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50586588764954075814525769 37939941573715556860894327)
          ·
            refine ⟨56909912360573335291341491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37939941573715556860894327 56909912360573335291341491)
            ·
              refine ⟨85364868540860002937012237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56909912360573335291341491 85364868540860002937012237)
              ·
                refine ⟨32011825702822501101379589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 85364868540860002937012237 32011825702822501101379589)
                ·
                  refine ⟨6002217319279218956508673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32011825702822501101379589 6002217319279218956508673)
                  ·
                    refine ⟨4501662989459414217381505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6002217319279218956508673 4501662989459414217381505)
                    ·
                      refine ⟨3376247242094560663036129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4501662989459414217381505 3376247242094560663036129)
                      ·
                        rfl

theorem cell23_6575218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 3, 4, 2, 2].length) (baseStart_6575218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6575218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6575218 prefixEnd_6575218 := by exact prefixLift 6575218
  have htrace : WordTrace (prefixWord ++ tailWord_6575218) baseStart_6575218 baseEnd_6575218 := by
    simpa [prefixWord, tailWord_6575218, baseEnd_6575218] using wordTrace_append hprefix tailTrace_6575218
  have hstable : (prefixWord ++ tailWord_6575218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6575218).length < 2 ^ (prefixWord ++ tailWord_6575218).sum := by decide
  have hdescent : baseEnd_6575218 < baseStart_6575218 := by decide
  rcases family_descends (prefixWord ++ tailWord_6575218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6575224 : List Nat := [2, 1, 2, 1, 1, 1, 7, 1, 7]
def baseStart_6575224 : Nat := 118140960795 + 6575224 * 2 ^ 59
def prefixEnd_6575224 : Nat := 4983230072969 + 3 ^ 40 * 6575224 * 2
def baseEnd_6575224 : Nat := 375138924775387515506789

theorem tailTrace_6575224 : CollatzResearch.WordTrace tailWord_6575224 prefixEnd_6575224 375138924775387515506789 := by
  unfold tailWord_6575224
  simp only [CollatzResearch.WordTrace]
  refine ⟨119909060565546940850494363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159878747420729254467325817 119909060565546940850494363)
  ·
    refine ⟨179863590848320411275741545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119909060565546940850494363 179863590848320411275741545)
    ·
      refine ⟨134897693136240308456806159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 179863590848320411275741545 134897693136240308456806159)
      ·
        refine ⟨202346539704360462685209239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134897693136240308456806159 202346539704360462685209239)
        ·
          refine ⟨303519809556540694027813859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 202346539704360462685209239 303519809556540694027813859)
          ·
            refine ⟨455279714334811041041720789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 303519809556540694027813859 455279714334811041041720789)
            ·
              refine ⟨10670618304722133774415331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 455279714334811041041720789 10670618304722133774415331)
              ·
                refine ⟨16005927457083200661622997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10670618304722133774415331 16005927457083200661622997)
                ·
                  refine ⟨375138924775387515506789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16005927457083200661622997 375138924775387515506789)
                  ·
                    rfl

theorem cell23_6575224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 7, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 7, 1, 7].length) (baseStart_6575224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6575224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6575224 prefixEnd_6575224 := by exact prefixLift 6575224
  have htrace : WordTrace (prefixWord ++ tailWord_6575224) baseStart_6575224 baseEnd_6575224 := by
    simpa [prefixWord, tailWord_6575224, baseEnd_6575224] using wordTrace_append hprefix tailTrace_6575224
  have hstable : (prefixWord ++ tailWord_6575224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6575224).length < 2 ^ (prefixWord ++ tailWord_6575224).sum := by decide
  have hdescent : baseEnd_6575224 < baseStart_6575224 := by decide
  rcases family_descends (prefixWord ++ tailWord_6575224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6575264 : List Nat := [2, 1, 1, 4, 2, 1, 1, 1, 3, 2, 5]
def baseStart_6575264 : Nat := 118140960795 + 6575264 * 2 ^ 59
def prefixEnd_6575264 : Nat := 4983230072969 + 3 ^ 40 * 6575264 * 2
def baseEnd_6575264 : Nat := 3376270862204667483060917

theorem tailTrace_6575264 : CollatzResearch.WordTrace tailWord_6575264 prefixEnd_6575264 3376270862204667483060917 := by
  unfold tailWord_6575264
  simp only [CollatzResearch.WordTrace]
  refine ⟨119909790025474484266222423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159879720033965979021629897 119909790025474484266222423)
  ·
    refine ⟨179864685038211726399333635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119909790025474484266222423 179864685038211726399333635)
    ·
      refine ⟨269797027557317589599000453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179864685038211726399333635 269797027557317589599000453)
      ·
        refine ⟨50586942666997048049812585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 269797027557317589599000453 50586942666997048049812585)
        ·
          refine ⟨37940207000247786037359439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50586942666997048049812585 37940207000247786037359439)
          ·
            refine ⟨56910310500371679056039159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37940207000247786037359439 56910310500371679056039159)
            ·
              refine ⟨85365465750557518584058739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56910310500371679056039159 85365465750557518584058739)
              ·
                refine ⟨128048198625836277876088109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 85365465750557518584058739 128048198625836277876088109)
                ·
                  refine ⟨48018074484688604203533041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 128048198625836277876088109 48018074484688604203533041)
                  ·
                    refine ⟨36013555863516453152649781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 48018074484688604203533041 36013555863516453152649781)
                    ·
                      refine ⟨3376270862204667483060917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36013555863516453152649781 3376270862204667483060917)
                      ·
                        rfl

theorem cell23_6575264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 1, 3, 2, 5].length) (baseStart_6575264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6575264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6575264 prefixEnd_6575264 := by exact prefixLift 6575264
  have htrace : WordTrace (prefixWord ++ tailWord_6575264) baseStart_6575264 baseEnd_6575264 := by
    simpa [prefixWord, tailWord_6575264, baseEnd_6575264] using wordTrace_append hprefix tailTrace_6575264
  have hstable : (prefixWord ++ tailWord_6575264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6575264).length < 2 ^ (prefixWord ++ tailWord_6575264).sum := by decide
  have hdescent : baseEnd_6575264 < baseStart_6575264 := by decide
  rcases family_descends (prefixWord ++ tailWord_6575264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6575281 : List Nat := [1, 2, 2, 5, 1, 1, 2, 1, 1, 2, 5]
def baseStart_6575281 : Nat := 118140960795 + 6575281 * 2 ^ 59
def prefixEnd_6575281 : Nat := 4983230072969 + 3 ^ 40 * 6575281 * 2
def baseEnd_6575281 : Nat := 3376279591375793916548339

theorem tailTrace_6575281 : CollatzResearch.WordTrace tailWord_6575281 prefixEnd_6575281 3376279591375793916548339 := by
  unfold tailWord_6575281
  simp only [CollatzResearch.WordTrace]
  refine ⟨239820200091887380435813697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159880133394591586957209131 239820200091887380435813697)
  ·
    refine ⟨179865150068915535326860273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 239820200091887380435813697 179865150068915535326860273)
    ·
      refine ⟨134898862551686651495145205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 179865150068915535326860273 134898862551686651495145205)
      ·
        refine ⟨12646768364220623577669863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 134898862551686651495145205 12646768364220623577669863)
        ·
          refine ⟨18970152546330935366504795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12646768364220623577669863 18970152546330935366504795)
          ·
            refine ⟨28455228819496403049757193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18970152546330935366504795 28455228819496403049757193)
            ·
              refine ⟨21341421614622302287317895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28455228819496403049757193 21341421614622302287317895)
              ·
                refine ⟨32012132421933453430976843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21341421614622302287317895 32012132421933453430976843)
                ·
                  refine ⟨48018198632900180146465265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32012132421933453430976843 48018198632900180146465265)
                  ·
                    refine ⟨36013648974675135109848949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 48018198632900180146465265 36013648974675135109848949)
                    ·
                      refine ⟨3376279591375793916548339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36013648974675135109848949 3376279591375793916548339)
                      ·
                        rfl

theorem cell23_6575281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 2, 1, 1, 2, 5].length) (baseStart_6575281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6575281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6575281 prefixEnd_6575281 := by exact prefixLift 6575281
  have htrace : WordTrace (prefixWord ++ tailWord_6575281) baseStart_6575281 baseEnd_6575281 := by
    simpa [prefixWord, tailWord_6575281, baseEnd_6575281] using wordTrace_append hprefix tailTrace_6575281
  have hstable : (prefixWord ++ tailWord_6575281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6575281).length < 2 ^ (prefixWord ++ tailWord_6575281).sum := by decide
  have hdescent : baseEnd_6575281 < baseStart_6575281 := by decide
  rcases family_descends (prefixWord ++ tailWord_6575281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6575311 : List Nat := [1, 1, 2, 1, 1, 3, 2, 5, 2, 2, 3]
def baseStart_6575311 : Nat := 118140960795 + 6575311 * 2 ^ 59
def prefixEnd_6575311 : Nat := 4983230072969 + 3 ^ 40 * 6575311 * 2
def baseEnd_6575311 : Nat := 3376294995795428799173201

theorem tailTrace_6575311 : CollatzResearch.WordTrace tailWord_6575311 prefixEnd_6575311 3376294995795428799173201 := by
  unfold tailWord_6575311
  simp only [CollatzResearch.WordTrace]
  refine ⟨239821294281778695559405787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159880862854519130372937191 239821294281778695559405787)
  ·
    refine ⟨359731941422668043339108681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 239821294281778695559405787 359731941422668043339108681)
    ·
      refine ⟨269798956067001032504331511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 359731941422668043339108681 269798956067001032504331511)
      ·
        refine ⟨404698434100501548756497267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 269798956067001032504331511 404698434100501548756497267)
        ·
          refine ⟨607047651150752323134745901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 404698434100501548756497267 607047651150752323134745901)
          ·
            refine ⟨227642869181532121175529713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 607047651150752323134745901 227642869181532121175529713)
            ·
              refine ⟨170732151886149090881647285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 227642869181532121175529713 170732151886149090881647285)
              ·
                refine ⟨16006139239326477270154433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 170732151886149090881647285 16006139239326477270154433)
                ·
                  refine ⟨12004604429494857952615825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16006139239326477270154433 12004604429494857952615825)
                  ·
                    refine ⟨9003453322121143464461869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12004604429494857952615825 9003453322121143464461869)
                    ·
                      refine ⟨3376294995795428799173201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9003453322121143464461869 3376294995795428799173201)
                      ·
                        rfl

theorem cell23_6575311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 5, 2, 2, 3].length) (baseStart_6575311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6575311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6575311 prefixEnd_6575311 := by exact prefixLift 6575311
  have htrace : WordTrace (prefixWord ++ tailWord_6575311) baseStart_6575311 baseEnd_6575311 := by
    simpa [prefixWord, tailWord_6575311, baseEnd_6575311] using wordTrace_append hprefix tailTrace_6575311
  have hstable : (prefixWord ++ tailWord_6575311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6575311).length < 2 ^ (prefixWord ++ tailWord_6575311).sum := by decide
  have hdescent : baseEnd_6575311 < baseStart_6575311 := by decide
  rcases family_descends (prefixWord ++ tailWord_6575311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6575335 : List Nat := [1, 1, 5, 3, 2, 1, 2, 1, 3, 4]
def baseStart_6575335 : Nat := 118140960795 + 6575335 * 2 ^ 59
def prefixEnd_6575335 : Nat := 4983230072969 + 3 ^ 40 * 6575335 * 2
def baseEnd_6575335 : Nat := 1125435773110378901757697

theorem tailTrace_6575335 : CollatzResearch.WordTrace tailWord_6575335 prefixEnd_6575335 1125435773110378901757697 := by
  unfold tailWord_6575335
  simp only [CollatzResearch.WordTrace]
  refine ⟨239822169633691747658279459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159881446422461165105519639 239822169633691747658279459)
  ·
    refine ⟨359733254450537621487419189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 239822169633691747658279459 359733254450537621487419189)
    ·
      refine ⟨33724992604737902014445549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 359733254450537621487419189 33724992604737902014445549)
      ·
        refine ⟨12646872226776713255417081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33724992604737902014445549 12646872226776713255417081)
        ·
          refine ⟨9485154170082534941562811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12646872226776713255417081 9485154170082534941562811)
          ·
            refine ⟨14227731255123802412344217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9485154170082534941562811 14227731255123802412344217)
            ·
              refine ⟨10670798441342851809258163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14227731255123802412344217 10670798441342851809258163)
              ·
                refine ⟨16006197662014277713887245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10670798441342851809258163 16006197662014277713887245)
                ·
                  refine ⟨6002324123255354142707717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16006197662014277713887245 6002324123255354142707717)
                  ·
                    refine ⟨1125435773110378901757697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6002324123255354142707717 1125435773110378901757697)
                    ·
                      rfl

theorem cell23_6575335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 2, 1, 3, 4].length) (baseStart_6575335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6575335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6575335 prefixEnd_6575335 := by exact prefixLift 6575335
  have htrace : WordTrace (prefixWord ++ tailWord_6575335) baseStart_6575335 baseEnd_6575335 := by
    simpa [prefixWord, tailWord_6575335, baseEnd_6575335] using wordTrace_append hprefix tailTrace_6575335
  have hstable : (prefixWord ++ tailWord_6575335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6575335).length < 2 ^ (prefixWord ++ tailWord_6575335).sum := by decide
  have hdescent : baseEnd_6575335 < baseStart_6575335 := by decide
  rcases family_descends (prefixWord ++ tailWord_6575335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6575381 : List Nat := [1, 3, 2, 1, 2, 1, 1, 2, 5, 1, 4]
def baseStart_6575381 : Nat := 118140960795 + 6575381 * 2 ^ 59
def prefixEnd_6575381 : Nat := 4983230072969 + 3 ^ 40 * 6575381 * 2
def baseEnd_6575381 : Nat := 3376330939441243525297879

theorem tailTrace_6575381 : CollatzResearch.WordTrace tailWord_6575381 prefixEnd_6575381 3376330939441243525297879 := by
  unfold tailWord_6575381
  simp only [CollatzResearch.WordTrace]
  refine ⟨239823847391525097514453997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159882564927683398342969331 239823847391525097514453997)
  ·
    refine ⟨89933942771821911567920249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 239823847391525097514453997 89933942771821911567920249)
    ·
      refine ⟨67450457078866433675940187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89933942771821911567920249 67450457078866433675940187)
      ·
        refine ⟨101175685618299650513910281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67450457078866433675940187 101175685618299650513910281)
        ·
          refine ⟨75881764213724737885432711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101175685618299650513910281 75881764213724737885432711)
          ·
            refine ⟨113822646320587106828149067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75881764213724737885432711 113822646320587106828149067)
            ·
              refine ⟨170733969480880660242223601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 113822646320587106828149067 170733969480880660242223601)
              ·
                refine ⟨128050477110660495181667701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 170733969480880660242223601 128050477110660495181667701)
                ·
                  refine ⟨12004732229124421423281347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 128050477110660495181667701 12004732229124421423281347)
                  ·
                    refine ⟨18007098343686632134922021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12004732229124421423281347 18007098343686632134922021)
                    ·
                      refine ⟨3376330939441243525297879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18007098343686632134922021 3376330939441243525297879)
                      ·
                        rfl

theorem cell23_6575381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 2, 5, 1, 4].length) (baseStart_6575381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6575381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6575381 prefixEnd_6575381 := by exact prefixLift 6575381
  have htrace : WordTrace (prefixWord ++ tailWord_6575381) baseStart_6575381 baseEnd_6575381 := by
    simpa [prefixWord, tailWord_6575381, baseEnd_6575381] using wordTrace_append hprefix tailTrace_6575381
  have hstable : (prefixWord ++ tailWord_6575381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6575381).length < 2 ^ (prefixWord ++ tailWord_6575381).sum := by decide
  have hdescent : baseEnd_6575381 < baseStart_6575381 := by decide
  rcases family_descends (prefixWord ++ tailWord_6575381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6575392 : List Nat := [2, 1, 1, 5, 3, 2, 1, 1, 3, 1, 3]
def baseStart_6575392 : Nat := 118140960795 + 6575392 * 2 ^ 59
def prefixEnd_6575392 : Nat := 4983230072969 + 3 ^ 40 * 6575392 * 2
def baseEnd_6575392 : Nat := 3376336587728442982260329

theorem tailTrace_6575392 : CollatzResearch.WordTrace tailWord_6575392 prefixEnd_6575392 3376336587728442982260329 := by
  unfold tailWord_6575392
  simp only [CollatzResearch.WordTrace]
  refine ⟨119912124297242623196552215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159882832396323497595402953 119912124297242623196552215)
  ·
    refine ⟨179868186445863934794828323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119912124297242623196552215 179868186445863934794828323)
    ·
      refine ⟨269802279668795902192242485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179868186445863934794828323 269802279668795902192242485)
      ·
        refine ⟨25293963718949615830522733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 269802279668795902192242485 25293963718949615830522733)
        ·
          refine ⟨9485236394606105936446025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25293963718949615830522733 9485236394606105936446025)
          ·
            refine ⟨7113927295954579452334519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9485236394606105936446025 7113927295954579452334519)
            ·
              refine ⟨10670890943931869178501779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7113927295954579452334519 10670890943931869178501779)
              ·
                refine ⟨16006336415897803767752669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10670890943931869178501779 16006336415897803767752669)
                ·
                  refine ⟨6002376155961676412907251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16006336415897803767752669 6002376155961676412907251)
                  ·
                    refine ⟨9003564233942514619360877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6002376155961676412907251 9003564233942514619360877)
                    ·
                      refine ⟨3376336587728442982260329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9003564233942514619360877 3376336587728442982260329)
                      ·
                        rfl

theorem cell23_6575392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 2, 1, 1, 3, 1, 3].length) (baseStart_6575392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6575392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6575392 prefixEnd_6575392 := by exact prefixLift 6575392
  have htrace : WordTrace (prefixWord ++ tailWord_6575392) baseStart_6575392 baseEnd_6575392 := by
    simpa [prefixWord, tailWord_6575392, baseEnd_6575392] using wordTrace_append hprefix tailTrace_6575392
  have hstable : (prefixWord ++ tailWord_6575392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6575392).length < 2 ^ (prefixWord ++ tailWord_6575392).sum := by decide
  have hdescent : baseEnd_6575392 < baseStart_6575392 := by decide
  rcases family_descends (prefixWord ++ tailWord_6575392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6575408 : List Nat := [2, 1, 1, 1, 2, 2, 5, 3, 2, 4]
def baseStart_6575408 : Nat := 118140960795 + 6575408 * 2 ^ 59
def prefixEnd_6575408 : Nat := 4983230072969 + 3 ^ 40 * 6575408 * 2
def baseEnd_6575408 : Nat := 1125448267806304973220085

theorem tailTrace_6575408 : CollatzResearch.WordTrace tailWord_6575408 prefixEnd_6575408 1125448267806304973220085 := by
  unfold tailWord_6575408
  simp only [CollatzResearch.WordTrace]
  refine ⟨119912416081213640562843439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159883221441618187417124585 119912416081213640562843439)
  ·
    refine ⟨179868624121820460844265159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119912416081213640562843439 179868624121820460844265159)
    ·
      refine ⟨269802936182730691266397739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179868624121820460844265159 269802936182730691266397739)
      ·
        refine ⟨404704404274096036899596609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 269802936182730691266397739 404704404274096036899596609)
        ·
          refine ⟨303528303205572027674697457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 404704404274096036899596609 303528303205572027674697457)
          ·
            refine ⟨227646227404179020756023093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 303528303205572027674697457 227646227404179020756023093)
            ·
              refine ⟨21341833819141783195877165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 227646227404179020756023093 21341833819141783195877165)
              ·
                refine ⟨8003187682178168698453937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21341833819141783195877165 8003187682178168698453937)
                ·
                  refine ⟨6002390761633626523840453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8003187682178168698453937 6002390761633626523840453)
                  ·
                    refine ⟨1125448267806304973220085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6002390761633626523840453 1125448267806304973220085)
                    ·
                      rfl

theorem cell23_6575408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 5, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 5, 3, 2, 4].length) (baseStart_6575408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6575408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6575408 prefixEnd_6575408 := by exact prefixLift 6575408
  have htrace : WordTrace (prefixWord ++ tailWord_6575408) baseStart_6575408 baseEnd_6575408 := by
    simpa [prefixWord, tailWord_6575408, baseEnd_6575408] using wordTrace_append hprefix tailTrace_6575408
  have hstable : (prefixWord ++ tailWord_6575408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6575408).length < 2 ^ (prefixWord ++ tailWord_6575408).sum := by decide
  have hdescent : baseEnd_6575408 < baseStart_6575408 := by decide
  rcases family_descends (prefixWord ++ tailWord_6575408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6575411 : List Nat := [1, 1, 1, 2, 5, 2, 2, 1, 1, 1, 6]
def baseStart_6575411 : Nat := 118140960795 + 6575411 * 2 ^ 59
def prefixEnd_6575411 : Nat := 4983230072969 + 3 ^ 40 * 6575411 * 2
def baseEnd_6575411 : Nat := 3376346343860878407922741

theorem tailTrace_6575411 : CollatzResearch.WordTrace tailWord_6575411 prefixEnd_6575411 3376346343860878407922741 := by
  unfold tailWord_6575411
  simp only [CollatzResearch.WordTrace]
  refine ⟨239824941581416412638046087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159883294387610941758697391 239824941581416412638046087)
  ·
    refine ⟨359737412372124618957069131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 239824941581416412638046087 359737412372124618957069131)
    ·
      refine ⟨539606118558186928435603697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 359737412372124618957069131 539606118558186928435603697)
      ·
        refine ⟨404704588918640196326702773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 539606118558186928435603697 404704588918640196326702773)
        ·
          refine ⟨37941055211122518405628385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 404704588918640196326702773 37941055211122518405628385)
          ·
            refine ⟨28455791408341888804221289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37941055211122518405628385 28455791408341888804221289)
            ·
              refine ⟨21341843556256416603165967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28455791408341888804221289 21341843556256416603165967)
              ·
                refine ⟨32012765334384624904748951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21341843556256416603165967 32012765334384624904748951)
                ·
                  refine ⟨48019148001576937357123427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32012765334384624904748951 48019148001576937357123427)
                  ·
                    refine ⟨72028722002365406035685141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 48019148001576937357123427 72028722002365406035685141)
                    ·
                      refine ⟨3376346343860878407922741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 72028722002365406035685141 3376346343860878407922741)
                      ·
                        rfl

theorem cell23_6575411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 2, 1, 1, 1, 6].length) (baseStart_6575411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6575411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6575411 prefixEnd_6575411 := by exact prefixLift 6575411
  have htrace : WordTrace (prefixWord ++ tailWord_6575411) baseStart_6575411 baseEnd_6575411 := by
    simpa [prefixWord, tailWord_6575411, baseEnd_6575411] using wordTrace_append hprefix tailTrace_6575411
  have hstable : (prefixWord ++ tailWord_6575411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6575411).length < 2 ^ (prefixWord ++ tailWord_6575411).sum := by decide
  have hdescent : baseEnd_6575411 < baseStart_6575411 := by decide
  rcases family_descends (prefixWord ++ tailWord_6575411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6575418 : List Nat := [3, 1, 1, 1, 4, 1, 3, 1, 3, 2, 3]
def baseStart_6575418 : Nat := 118140960795 + 6575418 * 2 ^ 59
def prefixEnd_6575418 : Nat := 4983230072969 + 3 ^ 40 * 6575418 * 2
def baseEnd_6575418 : Nat := 3376349938225459880535209

theorem tailTrace_6575418 : CollatzResearch.WordTrace tailWord_6575418 prefixEnd_6575418 3376349938225459880535209 := by
  unfold tailWord_6575418
  simp only [CollatzResearch.WordTrace]
  refine ⟨59956299223097763208387727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 159883464594927368555700605 59956299223097763208387727)
  ·
    refine ⟨89934448834646644812581591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59956299223097763208387727 89934448834646644812581591)
    ·
      refine ⟨134901673251969967218872387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89934448834646644812581591 134901673251969967218872387)
      ·
        refine ⟨202352509877954950828308581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134901673251969967218872387 202352509877954950828308581)
        ·
          refine ⟨37941095602116553280307859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 202352509877954950828308581 37941095602116553280307859)
          ·
            refine ⟨56911643403174829920461789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37941095602116553280307859 56911643403174829920461789)
            ·
              refine ⟨21341866276190561220173171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56911643403174829920461789 21341866276190561220173171)
              ·
                refine ⟨32012799414285841830259757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21341866276190561220173171 32012799414285841830259757)
                ·
                  refine ⟨12004799780357190686347409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32012799414285841830259757 12004799780357190686347409)
                  ·
                    refine ⟨9003599835267893014760557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12004799780357190686347409 9003599835267893014760557)
                    ·
                      refine ⟨3376349938225459880535209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9003599835267893014760557 3376349938225459880535209)
                      ·
                        rfl

theorem cell23_6575418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 3, 1, 3, 2, 3].length) (baseStart_6575418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6575418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6575418 prefixEnd_6575418 := by exact prefixLift 6575418
  have htrace : WordTrace (prefixWord ++ tailWord_6575418) baseStart_6575418 baseEnd_6575418 := by
    simpa [prefixWord, tailWord_6575418, baseEnd_6575418] using wordTrace_append hprefix tailTrace_6575418
  have hstable : (prefixWord ++ tailWord_6575418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6575418).length < 2 ^ (prefixWord ++ tailWord_6575418).sum := by decide
  have hdescent : baseEnd_6575418 < baseStart_6575418 := by decide
  rcases family_descends (prefixWord ++ tailWord_6575418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6575432 : List Nat := [2, 1, 3, 1, 1, 2, 1, 7, 1, 2, 2]
def baseStart_6575432 : Nat := 118140960795 + 6575432 * 2 ^ 59
def prefixEnd_6575432 : Nat := 4983230072969 + 3 ^ 40 * 6575432 * 2
def baseEnd_6575432 : Nat := 3376357126954622825760145

theorem tailTrace_6575432 : CollatzResearch.WordTrace tailWord_6575432 prefixEnd_6575432 3376357126954622825760145 := by
  unfold tailWord_6575432
  simp only [CollatzResearch.WordTrace]
  refine ⟨119912853757170166612280275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159883805009560222149707033 119912853757170166612280275)
  ·
    refine ⟨179869280635755249918420413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119912853757170166612280275 179869280635755249918420413)
    ·
      refine ⟨67450980238408218719407655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 179869280635755249918420413 67450980238408218719407655)
      ·
        refine ⟨101176470357612328079111483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67450980238408218719407655 101176470357612328079111483)
        ·
          refine ⟨151764705536418492118667225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101176470357612328079111483 151764705536418492118667225)
          ·
            refine ⟨113823529152313869089000419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 151764705536418492118667225 113823529152313869089000419)
            ·
              refine ⟨170735293728470803633500629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 113823529152313869089000419 170735293728470803633500629)
              ·
                refine ⟨4001608446761034460160171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 170735293728470803633500629 4001608446761034460160171)
                ·
                  refine ⟨6002412670141551690240257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4001608446761034460160171 6002412670141551690240257)
                  ·
                    refine ⟨4501809502606163767680193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6002412670141551690240257 4501809502606163767680193)
                    ·
                      refine ⟨3376357126954622825760145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4501809502606163767680193 3376357126954622825760145)
                      ·
                        rfl

theorem cell23_6575432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 7, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 7, 1, 2, 2].length) (baseStart_6575432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6575432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6575432 prefixEnd_6575432 := by exact prefixLift 6575432
  have htrace : WordTrace (prefixWord ++ tailWord_6575432) baseStart_6575432 baseEnd_6575432 := by
    simpa [prefixWord, tailWord_6575432, baseEnd_6575432] using wordTrace_append hprefix tailTrace_6575432
  have hstable : (prefixWord ++ tailWord_6575432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6575432).length < 2 ^ (prefixWord ++ tailWord_6575432).sum := by decide
  have hdescent : baseEnd_6575432 < baseStart_6575432 := by decide
  rcases family_descends (prefixWord ++ tailWord_6575432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6575449 : List Nat := [1, 2, 1, 2, 2, 2, 6, 2, 1, 2, 2]
def baseStart_6575449 : Nat := 118140960795 + 6575449 * 2 ^ 59
def prefixEnd_6575449 : Nat := 4983230072969 + 3 ^ 40 * 6575449 * 2
def baseEnd_6575449 : Nat := 3376365856125749259247567

theorem tailTrace_6575449 : CollatzResearch.WordTrace tailWord_6575449 prefixEnd_6575449 3376365856125749259247567 := by
  unfold tailWord_6575449
  simp only [CollatzResearch.WordTrace]
  refine ⟨239826327555278745127929401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159884218370185830085286267 239826327555278745127929401)
  ·
    refine ⟨179869745666459058845947051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 239826327555278745127929401 179869745666459058845947051)
    ·
      refine ⟨269804618499688588268920577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179869745666459058845947051 269804618499688588268920577)
      ·
        refine ⟨202353463874766441201690433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 269804618499688588268920577 202353463874766441201690433)
        ·
          refine ⟨151765097906074830901267825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 202353463874766441201690433 151765097906074830901267825)
          ·
            refine ⟨113823823429556123175950869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 151765097906074830901267825 113823823429556123175950869)
            ·
              refine ⟨5335491723260443273872697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 113823823429556123175950869 5335491723260443273872697)
              ·
                refine ⟨4001618792445332455404523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5335491723260443273872697 4001618792445332455404523)
                ·
                  refine ⟨6002428188667998683106785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4001618792445332455404523 6002428188667998683106785)
                  ·
                    refine ⟨4501821141500999012330089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6002428188667998683106785 4501821141500999012330089)
                    ·
                      refine ⟨3376365856125749259247567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4501821141500999012330089 3376365856125749259247567)
                      ·
                        rfl

theorem cell23_6575449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 6, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 6, 2, 1, 2, 2].length) (baseStart_6575449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6575449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6575449 prefixEnd_6575449 := by exact prefixLift 6575449
  have htrace : WordTrace (prefixWord ++ tailWord_6575449) baseStart_6575449 baseEnd_6575449 := by
    simpa [prefixWord, tailWord_6575449, baseEnd_6575449] using wordTrace_append hprefix tailTrace_6575449
  have hstable : (prefixWord ++ tailWord_6575449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6575449).length < 2 ^ (prefixWord ++ tailWord_6575449).sum := by decide
  have hdescent : baseEnd_6575449 < baseStart_6575449 := by decide
  rcases family_descends (prefixWord ++ tailWord_6575449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6575471 : List Nat := [1, 1, 2, 1, 3, 1, 3, 2, 2, 3, 4]
def baseStart_6575471 : Nat := 118140960795 + 6575471 * 2 ^ 59
def prefixEnd_6575471 : Nat := 4983230072969 + 3 ^ 40 * 6575471 * 2
def baseEnd_6575471 : Nat := 3376377152700148173172465

theorem tailTrace_6575471 : CollatzResearch.WordTrace tailWord_6575471 prefixEnd_6575471 3376377152700148173172465 := by
  unfold tailWord_6575471
  simp only [CollatzResearch.WordTrace]
  refine ⟨239827129961199042885230267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159884753307466028590153511 239827129961199042885230267)
  ·
    refine ⟨359740694941798564327845401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 239827129961199042885230267 359740694941798564327845401)
    ·
      refine ⟨269805521206348923245884051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 359740694941798564327845401 269805521206348923245884051)
      ·
        refine ⟨404708281809523384868826077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 269805521206348923245884051 404708281809523384868826077)
        ·
          refine ⟨151765605678571269325809779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 404708281809523384868826077 151765605678571269325809779)
          ·
            refine ⟨227648408517856903988714669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 151765605678571269325809779 227648408517856903988714669)
            ·
              refine ⟨85368153194196338995768001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 227648408517856903988714669 85368153194196338995768001)
              ·
                refine ⟨64026114895647254246826001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 85368153194196338995768001 64026114895647254246826001)
                ·
                  refine ⟨48019586171735440685119501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 64026114895647254246826001 48019586171735440685119501)
                  ·
                    refine ⟨18007344814400790256919813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 48019586171735440685119501 18007344814400790256919813)
                    ·
                      refine ⟨3376377152700148173172465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18007344814400790256919813 3376377152700148173172465)
                      ·
                        rfl

theorem cell23_6575471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 2, 2, 3, 4].length) (baseStart_6575471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6575471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6575471 prefixEnd_6575471 := by exact prefixLift 6575471
  have htrace : WordTrace (prefixWord ++ tailWord_6575471) baseStart_6575471 baseEnd_6575471 := by
    simpa [prefixWord, tailWord_6575471, baseEnd_6575471] using wordTrace_append hprefix tailTrace_6575471
  have hstable : (prefixWord ++ tailWord_6575471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6575471).length < 2 ^ (prefixWord ++ tailWord_6575471).sum := by decide
  have hdescent : baseEnd_6575471 < baseStart_6575471 := by decide
  rcases family_descends (prefixWord ++ tailWord_6575471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6575492 : List Nat := [2, 3, 2, 1, 1, 4, 1, 3, 1, 3, 2]
def baseStart_6575492 : Nat := 118140960795 + 6575492 * 2 ^ 59
def prefixEnd_6575492 : Nat := 4983230072969 + 3 ^ 40 * 6575492 * 2
def baseEnd_6575492 : Nat := 3376387935793892591009869

theorem tailTrace_6575492 : CollatzResearch.WordTrace tailWord_6575492 prefixEnd_6575492 3376387935793892591009869 := by
  unfold tailWord_6575492
  simp only [CollatzResearch.WordTrace]
  refine ⟨119913947947061481735872365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159885263929415308981163153 119913947947061481735872365)
  ·
    refine ⟨44967730480148055650952137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 119913947947061481735872365 44967730480148055650952137)
    ·
      refine ⟨33725797860111041738214103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44967730480148055650952137 33725797860111041738214103)
      ·
        refine ⟨50588696790166562607321155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33725797860111041738214103 50588696790166562607321155)
        ·
          refine ⟨75883045185249843910981733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50588696790166562607321155 75883045185249843910981733)
          ·
            refine ⟨14228070972234345733309075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 75883045185249843910981733 14228070972234345733309075)
            ·
              refine ⟨21342106458351518599963613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14228070972234345733309075 21342106458351518599963613)
              ·
                refine ⟨8003289921881819474986355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21342106458351518599963613 8003289921881819474986355)
                ·
                  refine ⟨12004934882822729212479533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8003289921881819474986355 12004934882822729212479533)
                  ·
                    refine ⟨4501850581058523454679825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12004934882822729212479533 4501850581058523454679825)
                    ·
                      refine ⟨3376387935793892591009869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4501850581058523454679825 3376387935793892591009869)
                      ·
                        rfl

theorem cell23_6575492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 1, 3, 1, 3, 2].length) (baseStart_6575492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6575492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6575492 prefixEnd_6575492 := by exact prefixLift 6575492
  have htrace : WordTrace (prefixWord ++ tailWord_6575492) baseStart_6575492 baseEnd_6575492 := by
    simpa [prefixWord, tailWord_6575492, baseEnd_6575492] using wordTrace_append hprefix tailTrace_6575492
  have hstable : (prefixWord ++ tailWord_6575492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6575492).length < 2 ^ (prefixWord ++ tailWord_6575492).sum := by decide
  have hdescent : baseEnd_6575492 < baseStart_6575492 := by decide
  rcases family_descends (prefixWord ++ tailWord_6575492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6575505 : List Nat := [1, 2, 2, 1, 1, 1, 2, 5, 4, 2, 2]
def baseStart_6575505 : Nat := 118140960795 + 6575505 * 2 ^ 59
def prefixEnd_6575505 : Nat := 4983230072969 + 3 ^ 40 * 6575505 * 2
def baseEnd_6575505 : Nat := 3376394611042401040147309

theorem tailTrace_6575505 : CollatzResearch.WordTrace tailWord_6575505 prefixEnd_6575505 3376394611042401040147309 := by
  unfold tailWord_6575505
  simp only [CollatzResearch.WordTrace]
  refine ⟨239828370043075866691967969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159885580028717244461311979 239828370043075866691967969)
  ·
    refine ⟨179871277532306900018975977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 239828370043075866691967969 179871277532306900018975977)
    ·
      refine ⟨134903458149230175014231983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 179871277532306900018975977 134903458149230175014231983)
      ·
        refine ⟨202355187223845262521347975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134903458149230175014231983 202355187223845262521347975)
        ·
          refine ⟨303532780835767893782021963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 202355187223845262521347975 303532780835767893782021963)
          ·
            refine ⟨455299171253651840673032945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 303532780835767893782021963 455299171253651840673032945)
            ·
              refine ⟨341474378440238880504774709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 455299171253651840673032945 341474378440238880504774709)
              ·
                refine ⟨32013222978772395047322629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 341474378440238880504774709 32013222978772395047322629)
                ·
                  refine ⟨6002479308519824071372993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32013222978772395047322629 6002479308519824071372993)
                  ·
                    refine ⟨4501859481389868053529745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6002479308519824071372993 4501859481389868053529745)
                    ·
                      refine ⟨3376394611042401040147309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4501859481389868053529745 3376394611042401040147309)
                      ·
                        rfl

theorem cell23_6575505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 5, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 5, 4, 2, 2].length) (baseStart_6575505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6575505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6575505 prefixEnd_6575505 := by exact prefixLift 6575505
  have htrace : WordTrace (prefixWord ++ tailWord_6575505) baseStart_6575505 baseEnd_6575505 := by
    simpa [prefixWord, tailWord_6575505, baseEnd_6575505] using wordTrace_append hprefix tailTrace_6575505
  have hstable : (prefixWord ++ tailWord_6575505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6575505).length < 2 ^ (prefixWord ++ tailWord_6575505).sum := by decide
  have hdescent : baseEnd_6575505 < baseStart_6575505 := by decide
  rcases family_descends (prefixWord ++ tailWord_6575505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6575516 : List Nat := [2, 2, 3, 4, 1, 1, 3, 1, 2, 1, 3]
def baseStart_6575516 : Nat := 118140960795 + 6575516 * 2 ^ 59
def prefixEnd_6575516 : Nat := 4983230072969 + 3 ^ 40 * 6575516 * 2
def baseEnd_6575516 : Nat := 3376400259329600497109759

theorem tailTrace_6575516 : CollatzResearch.WordTrace tailWord_6575516 prefixEnd_6575516 3376400259329600497109759 := by
  unfold tailWord_6575516
  simp only [CollatzResearch.WordTrace]
  refine ⟨119914385623018007785309201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159885847497357343713745601 119914385623018007785309201)
  ·
    refine ⟨89935789217263505838981901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119914385623018007785309201 89935789217263505838981901)
    ·
      refine ⟨33725920956473814689618213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 89935789217263505838981901 33725920956473814689618213)
      ·
        refine ⟨6323610179338840254303415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33725920956473814689618213 6323610179338840254303415)
        ·
          refine ⟨9485415269008260381455123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6323610179338840254303415 9485415269008260381455123)
          ·
            refine ⟨14228122903512390572182685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9485415269008260381455123 14228122903512390572182685)
            ·
              refine ⟨5335546088817146464568507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14228122903512390572182685 5335546088817146464568507)
              ·
                refine ⟨8003319133225719696852761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5335546088817146464568507 8003319133225719696852761)
                ·
                  refine ⟨6002489349919289772639571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8003319133225719696852761 6002489349919289772639571)
                  ·
                    refine ⟨9003734024878934658959357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6002489349919289772639571 9003734024878934658959357)
                    ·
                      refine ⟨3376400259329600497109759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9003734024878934658959357 3376400259329600497109759)
                      ·
                        rfl

theorem cell23_6575516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 3, 1, 2, 1, 3].length) (baseStart_6575516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6575516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6575516 prefixEnd_6575516 := by exact prefixLift 6575516
  have htrace : WordTrace (prefixWord ++ tailWord_6575516) baseStart_6575516 baseEnd_6575516 := by
    simpa [prefixWord, tailWord_6575516, baseEnd_6575516] using wordTrace_append hprefix tailTrace_6575516
  have hstable : (prefixWord ++ tailWord_6575516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6575516).length < 2 ^ (prefixWord ++ tailWord_6575516).sum := by decide
  have hdescent : baseEnd_6575516 < baseStart_6575516 := by decide
  rcases family_descends (prefixWord ++ tailWord_6575516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6575522 : List Nat := [3, 3, 1, 2, 1, 2, 3, 1, 1, 4, 2]
def baseStart_6575522 : Nat := 118140960795 + 6575522 * 2 ^ 59
def prefixEnd_6575522 : Nat := 4983230072969 + 3 ^ 40 * 6575522 * 2
def baseEnd_6575522 : Nat := 3376403340213527473634731

theorem tailTrace_6575522 : CollatzResearch.WordTrace tailWord_6575522 prefixEnd_6575522 3376403340213527473634731 := by
  unfold tailWord_6575522
  simp only [CollatzResearch.WordTrace]
  refine ⟨59957247521003569648834205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 159885993389342852396891213 59957247521003569648834205)
  ·
    refine ⟨22483967820376338618312827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59957247521003569648834205 22483967820376338618312827)
    ·
      refine ⟨33725951730564507927469241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22483967820376338618312827 33725951730564507927469241)
      ·
        refine ⟨25294463797923380945601931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33725951730564507927469241 25294463797923380945601931)
        ·
          refine ⟨37941695696885071418402897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25294463797923380945601931 37941695696885071418402897)
          ·
            refine ⟨28456271772663803563802173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37941695696885071418402897 28456271772663803563802173)
            ·
              refine ⟨10671101914748926336425815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28456271772663803563802173 10671101914748926336425815)
              ·
                refine ⟨16006652872123389504638723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10671101914748926336425815 16006652872123389504638723)
                ·
                  refine ⟨24009979308185084256958085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16006652872123389504638723 24009979308185084256958085)
                  ·
                    refine ⟨4501871120284703298179641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24009979308185084256958085 4501871120284703298179641)
                    ·
                      refine ⟨3376403340213527473634731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4501871120284703298179641 3376403340213527473634731)
                      ·
                        rfl

theorem cell23_6575522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 3, 1, 1, 4, 2].length) (baseStart_6575522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6575522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6575522 prefixEnd_6575522 := by exact prefixLift 6575522
  have htrace : WordTrace (prefixWord ++ tailWord_6575522) baseStart_6575522 baseEnd_6575522 := by
    simpa [prefixWord, tailWord_6575522, baseEnd_6575522] using wordTrace_append hprefix tailTrace_6575522
  have hstable : (prefixWord ++ tailWord_6575522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6575522).length < 2 ^ (prefixWord ++ tailWord_6575522).sum := by decide
  have hdescent : baseEnd_6575522 < baseStart_6575522 := by decide
  rcases family_descends (prefixWord ++ tailWord_6575522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6575538 : List Nat := [3, 2, 1, 1, 1, 1, 2, 2, 4, 3, 3]
def baseStart_6575538 : Nat := 118140960795 + 6575538 * 2 ^ 59
def prefixEnd_6575538 : Nat := 4983230072969 + 3 ^ 40 * 6575538 * 2
def baseEnd_6575538 : Nat := 3376411555903999411034657

theorem tailTrace_6575538 : CollatzResearch.WordTrace tailWord_6575538 prefixEnd_6575538 3376411555903999411034657 := by
  unfold tailWord_6575538
  simp only [CollatzResearch.WordTrace]
  refine ⟨59957393412989078331979817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 159886382434637542218612845 59957393412989078331979817)
  ·
    refine ⟨44968045059741808748984863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59957393412989078331979817 44968045059741808748984863)
    ·
      refine ⟨67452067589612713123477295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44968045059741808748984863 67452067589612713123477295)
      ·
        refine ⟨101178101384419069685215943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67452067589612713123477295 101178101384419069685215943)
        ·
          refine ⟨151767152076628604527823915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101178101384419069685215943 151767152076628604527823915)
          ·
            refine ⟨227650728114942906791735873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 151767152076628604527823915 227650728114942906791735873)
            ·
              refine ⟨170738046086207180093801905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 227650728114942906791735873 170738046086207180093801905)
              ·
                refine ⟨128053534564655385070351429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 170738046086207180093801905 128053534564655385070351429)
                ·
                  refine ⟨24010037730872884700690893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 128053534564655385070351429 24010037730872884700690893)
                  ·
                    refine ⟨9003764149077331762759085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24010037730872884700690893 9003764149077331762759085)
                    ·
                      refine ⟨3376411555903999411034657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9003764149077331762759085 3376411555903999411034657)
                      ·
                        rfl

theorem cell23_6575538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 2, 4, 3, 3].length) (baseStart_6575538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6575538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6575538 prefixEnd_6575538 := by exact prefixLift 6575538
  have htrace : WordTrace (prefixWord ++ tailWord_6575538) baseStart_6575538 baseEnd_6575538 := by
    simpa [prefixWord, tailWord_6575538, baseEnd_6575538] using wordTrace_append hprefix tailTrace_6575538
  have hstable : (prefixWord ++ tailWord_6575538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6575538).length < 2 ^ (prefixWord ++ tailWord_6575538).sum := by decide
  have hdescent : baseEnd_6575538 < baseStart_6575538 := by decide
  rcases family_descends (prefixWord ++ tailWord_6575538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6575551 : List Nat := [1, 1, 2, 2, 2, 1, 1, 2, 3, 1, 7]
def baseStart_6575551 : Nat := 118140960795 + 6575551 * 2 ^ 59
def prefixEnd_6575551 : Nat := 4983230072969 + 3 ^ 40 * 6575551 * 2
def baseEnd_6575551 : Nat := 3376418231152507860172097

theorem tailTrace_6575551 : CollatzResearch.WordTrace tailWord_6575551 prefixEnd_6575551 3376418231152507860172097 := by
  unfold tailWord_6575551
  simp only [CollatzResearch.WordTrace]
  refine ⟨239830047800909216548142507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159886698533939477698761671 239830047800909216548142507)
  ·
    refine ⟨359745071701363824822213761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 239830047800909216548142507 359745071701363824822213761)
    ·
      refine ⟨269808803776022868616660321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 359745071701363824822213761 269808803776022868616660321)
      ·
        refine ⟨202356602832017151462495241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 269808803776022868616660321 202356602832017151462495241)
        ·
          refine ⟨151767452124012863596871431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 202356602832017151462495241 151767452124012863596871431)
          ·
            refine ⟨227651178186019295395307147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 151767452124012863596871431 227651178186019295395307147)
            ·
              refine ⟨341476767279028943092960721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 227651178186019295395307147 341476767279028943092960721)
              ·
                refine ⟨256107575459271707319720541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 341476767279028943092960721 256107575459271707319720541)
                ·
                  refine ⟨96040340797226890244895203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 256107575459271707319720541 96040340797226890244895203)
                  ·
                    refine ⟨144060511195840335367342805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 96040340797226890244895203 144060511195840335367342805)
                    ·
                      refine ⟨3376418231152507860172097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 144060511195840335367342805 3376418231152507860172097)
                      ·
                        rfl

theorem cell23_6575551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 2, 3, 1, 7].length) (baseStart_6575551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6575551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6575551 prefixEnd_6575551 := by exact prefixLift 6575551
  have htrace : WordTrace (prefixWord ++ tailWord_6575551) baseStart_6575551 baseEnd_6575551 := by
    simpa [prefixWord, tailWord_6575551, baseEnd_6575551] using wordTrace_append hprefix tailTrace_6575551
  have hstable : (prefixWord ++ tailWord_6575551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6575551).length < 2 ^ (prefixWord ++ tailWord_6575551).sum := by decide
  have hdescent : baseEnd_6575551 < baseStart_6575551 := by decide
  rcases family_descends (prefixWord ++ tailWord_6575551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6575562 : List Nat := [3, 1, 2, 1, 2, 4, 3, 2, 5]
def baseStart_6575562 : Nat := 118140960795 + 6575562 * 2 ^ 59
def prefixEnd_6575562 : Nat := 4983230072969 + 3 ^ 40 * 6575562 * 2
def baseEnd_6575562 : Nat := 375158208826634146348283

theorem tailTrace_6575562 : CollatzResearch.WordTrace tailWord_6575562 prefixEnd_6575562 375158208826634146348283 := by
  unfold tailWord_6575562
  simp only [CollatzResearch.WordTrace]
  refine ⟨59957612250967341356698235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 159886966002579576951195293 59957612250967341356698235)
  ·
    refine ⟨89936418376451012035047353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59957612250967341356698235 89936418376451012035047353)
    ·
      refine ⟨67452313782338259026285515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89936418376451012035047353 67452313782338259026285515)
      ·
        refine ⟨101178470673507388539428273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67452313782338259026285515 101178470673507388539428273)
        ·
          refine ⟨75883853005130541404571205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101178470673507388539428273 75883853005130541404571205)
          ·
            refine ⟨14228222438461976513357101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 75883853005130541404571205 14228222438461976513357101)
            ·
              refine ⟨5335583414423241192508913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14228222438461976513357101 5335583414423241192508913)
              ·
                refine ⟨4001687560817430894381685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5335583414423241192508913 4001687560817430894381685)
                ·
                  refine ⟨375158208826634146348283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4001687560817430894381685 375158208826634146348283)
                  ·
                    rfl

theorem cell23_6575562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 3, 2, 5].length) (baseStart_6575562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6575562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6575562 prefixEnd_6575562 := by exact prefixLift 6575562
  have htrace : WordTrace (prefixWord ++ tailWord_6575562) baseStart_6575562 baseEnd_6575562 := by
    simpa [prefixWord, tailWord_6575562, baseEnd_6575562] using wordTrace_append hprefix tailTrace_6575562
  have hstable : (prefixWord ++ tailWord_6575562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6575562).length < 2 ^ (prefixWord ++ tailWord_6575562).sum := by decide
  have hdescent : baseEnd_6575562 < baseStart_6575562 := by decide
  rcases family_descends (prefixWord ++ tailWord_6575562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6575646 : List Nat := [4, 3, 3, 1, 1, 1, 1, 1, 1, 3, 4]
def baseStart_6575646 : Nat := 118140960795 + 6575646 * 2 ^ 59
def prefixEnd_6575646 : Nat := 4983230072969 + 3 ^ 40 * 6575646 * 2
def baseEnd_6575646 : Nat := 3376467011814684988484161

theorem tailTrace_6575646 : CollatzResearch.WordTrace tailWord_6575646 prefixEnd_6575646 3376467011814684988484161 := by
  unfold tailWord_6575646
  simp only [CollatzResearch.WordTrace]
  refine ⟨29979189091945630971606349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 159889008490376698515233861 29979189091945630971606349)
  ·
    refine ⟨11242195909479611614352381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29979189091945630971606349 11242195909479611614352381)
    ·
      refine ⟨4215823466054854355382143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11242195909479611614352381 4215823466054854355382143)
      ·
        refine ⟨6323735199082281533073215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4215823466054854355382143 6323735199082281533073215)
        ·
          refine ⟨9485602798623422299609823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6323735199082281533073215 9485602798623422299609823)
          ·
            refine ⟨14228404197935133449414735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9485602798623422299609823 14228404197935133449414735)
            ·
              refine ⟨21342606296902700174122103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14228404197935133449414735 21342606296902700174122103)
              ·
                refine ⟨32013909445354050261183155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21342606296902700174122103 32013909445354050261183155)
                ·
                  refine ⟨48020864168031075391774733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32013909445354050261183155 48020864168031075391774733)
                  ·
                    refine ⟨18007824063011653271915525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 48020864168031075391774733 18007824063011653271915525)
                    ·
                      refine ⟨3376467011814684988484161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18007824063011653271915525 3376467011814684988484161)
                      ·
                        rfl

theorem cell23_6575646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 1, 1, 1, 3, 4].length) (baseStart_6575646 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6575646 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6575646 prefixEnd_6575646 := by exact prefixLift 6575646
  have htrace : WordTrace (prefixWord ++ tailWord_6575646) baseStart_6575646 baseEnd_6575646 := by
    simpa [prefixWord, tailWord_6575646, baseEnd_6575646] using wordTrace_append hprefix tailTrace_6575646
  have hstable : (prefixWord ++ tailWord_6575646).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6575646).length < 2 ^ (prefixWord ++ tailWord_6575646).sum := by decide
  have hdescent : baseEnd_6575646 < baseStart_6575646 := by decide
  rcases family_descends (prefixWord ++ tailWord_6575646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6575656 : List Nat := [2, 1, 5, 2, 2, 1, 2, 3, 1, 4]
def baseStart_6575656 : Nat := 118140960795 + 6575656 * 2 ^ 59
def prefixEnd_6575656 : Nat := 4983230072969 + 3 ^ 40 * 6575656 * 2
def baseEnd_6575656 : Nat := 1125490715540409983119705

theorem tailTrace_6575656 : CollatzResearch.WordTrace tailWord_6575656 prefixEnd_6575656 1125490715540409983119705 := by
  unfold tailWord_6575656
  simp only [CollatzResearch.WordTrace]
  refine ⟨119916938732764409740357411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159889251643685879653809881 119916938732764409740357411)
  ·
    refine ⟨179875408099146614610536117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119916938732764409740357411 179875408099146614610536117)
    ·
      refine ⟨16863319509294995119737761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 179875408099146614610536117 16863319509294995119737761)
      ·
        refine ⟨12647489631971246339803321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16863319509294995119737761 12647489631971246339803321)
        ·
          refine ⟨9485617223978434754852491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12647489631971246339803321 9485617223978434754852491)
          ·
            refine ⟨14228425835967652132278737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9485617223978434754852491 14228425835967652132278737)
            ·
              refine ⟨10671319376975739099209053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14228425835967652132278737 10671319376975739099209053)
              ·
                refine ⟨4001744766365902162203395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10671319376975739099209053 4001744766365902162203395)
                ·
                  refine ⟨6002617149548853243305093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4001744766365902162203395 6002617149548853243305093)
                  ·
                    refine ⟨1125490715540409983119705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6002617149548853243305093 1125490715540409983119705)
                    ·
                      rfl

theorem cell23_6575656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 2, 3, 1, 4].length) (baseStart_6575656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6575656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6575656 prefixEnd_6575656 := by exact prefixLift 6575656
  have htrace : WordTrace (prefixWord ++ tailWord_6575656) baseStart_6575656 baseEnd_6575656 := by
    simpa [prefixWord, tailWord_6575656, baseEnd_6575656] using wordTrace_append hprefix tailTrace_6575656
  have hstable : (prefixWord ++ tailWord_6575656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6575656).length < 2 ^ (prefixWord ++ tailWord_6575656).sum := by decide
  have hdescent : baseEnd_6575656 < baseStart_6575656 := by decide
  rcases family_descends (prefixWord ++ tailWord_6575656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6575679 : List Nat := [1, 1, 2, 2, 3, 3, 2, 4, 1, 1, 3]
def baseStart_6575679 : Nat := 118140960795 + 6575679 * 2 ^ 59
def prefixEnd_6575679 : Nat := 4983230072969 + 3 ^ 40 * 6575679 * 2
def baseEnd_6575679 : Nat := 3376483956676283359371509

theorem tailTrace_6575679 : CollatzResearch.WordTrace tailWord_6575679 prefixEnd_6575679 3376483956676283359371509 := by
  unfold tailWord_6575679
  simp only [CollatzResearch.WordTrace]
  refine ⟨239834716344445494408802091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159889810896296996272534727 239834716344445494408802091)
  ·
    refine ⟨359752074516668241613203137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 239834716344445494408802091 359752074516668241613203137)
    ·
      refine ⟨269814055887501181209902353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 359752074516668241613203137 269814055887501181209902353)
      ·
        refine ⟨202360541915625885907426765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 269814055887501181209902353 202360541915625885907426765)
        ·
          refine ⟨75885203218359707215285037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 202360541915625885907426765 75885203218359707215285037)
          ·
            refine ⟨28456951206884890205731889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 75885203218359707215285037 28456951206884890205731889)
            ·
              refine ⟨21342713405163667654298917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28456951206884890205731889 21342713405163667654298917)
              ·
                refine ⟨4001758763468187685181047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21342713405163667654298917 4001758763468187685181047)
                ·
                  refine ⟨6002638145202281527771571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4001758763468187685181047 6002638145202281527771571)
                  ·
                    refine ⟨9003957217803422291657357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6002638145202281527771571 9003957217803422291657357)
                    ·
                      refine ⟨3376483956676283359371509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9003957217803422291657357 3376483956676283359371509)
                      ·
                        rfl

theorem cell23_6575679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 2, 4, 1, 1, 3].length) (baseStart_6575679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6575679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6575679 prefixEnd_6575679 := by exact prefixLift 6575679
  have htrace : WordTrace (prefixWord ++ tailWord_6575679) baseStart_6575679 baseEnd_6575679 := by
    simpa [prefixWord, tailWord_6575679, baseEnd_6575679] using wordTrace_append hprefix tailTrace_6575679
  have hstable : (prefixWord ++ tailWord_6575679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6575679).length < 2 ^ (prefixWord ++ tailWord_6575679).sum := by decide
  have hdescent : baseEnd_6575679 < baseStart_6575679 := by decide
  rcases family_descends (prefixWord ++ tailWord_6575679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6575686 : List Nat := [6, 1, 1, 1, 3, 1, 3, 1, 6]
def baseStart_6575686 : Nat := 118140960795 + 6575686 * 2 ^ 59
def prefixEnd_6575686 : Nat := 4983230072969 + 3 ^ 40 * 6575686 * 2
def baseEnd_6575686 : Nat := 375165283448984981331553

theorem tailTrace_6575686 : CollatzResearch.WordTrace tailWord_6575686 prefixEnd_6575686 375165283448984981331553 := by
  unfold tailWord_6575686
  simp only [CollatzResearch.WordTrace]
  refine ⟨7494842864231879206384591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 159889981103613423069537941 7494842864231879206384591)
  ·
    refine ⟨11242264296347818809576887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7494842864231879206384591 11242264296347818809576887)
    ·
      refine ⟨16863396444521728214365331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11242264296347818809576887 16863396444521728214365331)
      ·
        refine ⟨25295094666782592321547997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16863396444521728214365331 25295094666782592321547997)
        ·
          refine ⟨9485660500043472120580499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25295094666782592321547997 9485660500043472120580499)
          ·
            refine ⟨14228490750065208180870749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9485660500043472120580499 14228490750065208180870749)
            ·
              refine ⟨5335684031274453067826531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14228490750065208180870749 5335684031274453067826531)
              ·
                refine ⟨8003526046911679601739797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5335684031274453067826531 8003526046911679601739797)
                ·
                  refine ⟨375165283448984981331553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8003526046911679601739797 375165283448984981331553)
                  ·
                    rfl

theorem cell23_6575686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 3, 1, 6].length) (baseStart_6575686 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6575686 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6575686 prefixEnd_6575686 := by exact prefixLift 6575686
  have htrace : WordTrace (prefixWord ++ tailWord_6575686) baseStart_6575686 baseEnd_6575686 := by
    simpa [prefixWord, tailWord_6575686, baseEnd_6575686] using wordTrace_append hprefix tailTrace_6575686
  have hstable : (prefixWord ++ tailWord_6575686).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6575686).length < 2 ^ (prefixWord ++ tailWord_6575686).sum := by decide
  have hdescent : baseEnd_6575686 < baseStart_6575686 := by decide
  rcases family_descends (prefixWord ++ tailWord_6575686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6575705 : List Nat := [1, 2, 1, 2, 2, 1, 1, 5, 3, 2, 3]
def baseStart_6575705 : Nat := 118140960795 + 6575705 * 2 ^ 59
def prefixEnd_6575705 : Nat := 4983230072969 + 3 ^ 40 * 6575705 * 2
def baseEnd_6575705 : Nat := 3376497307173300257646389

theorem tailTrace_6575705 : CollatzResearch.WordTrace tailWord_6575705 prefixEnd_6575705 3376497307173300257646389 := by
  unfold tailWord_6575705
  simp only [CollatzResearch.WordTrace]
  refine ⟨239835664642351300849248569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159890443094900867232832379 239835664642351300849248569)
  ·
    refine ⟨179876748481763475636936427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 239835664642351300849248569 179876748481763475636936427)
    ·
      refine ⟨269815122722645213455404641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179876748481763475636936427 269815122722645213455404641)
      ·
        refine ⟨202361342041983910091553481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 269815122722645213455404641 202361342041983910091553481)
        ·
          refine ⟨151771006531487932568665111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 202361342041983910091553481 151771006531487932568665111)
          ·
            refine ⟨227656509797231898852997667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 151771006531487932568665111 227656509797231898852997667)
            ·
              refine ⟨341484764695847848279496501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 227656509797231898852997667 341484764695847848279496501)
              ·
                refine ⟨32014196690235735776202797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 341484764695847848279496501 32014196690235735776202797)
                ·
                  refine ⟨12005323758838400916076049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32014196690235735776202797 12005323758838400916076049)
                  ·
                    refine ⟨9003992819128800687057037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12005323758838400916076049 9003992819128800687057037)
                    ·
                      refine ⟨3376497307173300257646389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9003992819128800687057037 3376497307173300257646389)
                      ·
                        rfl

theorem cell23_6575705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 5, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 5, 3, 2, 3].length) (baseStart_6575705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6575705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6575705 prefixEnd_6575705 := by exact prefixLift 6575705
  have htrace : WordTrace (prefixWord ++ tailWord_6575705) baseStart_6575705 baseEnd_6575705 := by
    simpa [prefixWord, tailWord_6575705, baseEnd_6575705] using wordTrace_append hprefix tailTrace_6575705
  have hstable : (prefixWord ++ tailWord_6575705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6575705).length < 2 ^ (prefixWord ++ tailWord_6575705).sum := by decide
  have hdescent : baseEnd_6575705 < baseStart_6575705 := by decide
  rcases family_descends (prefixWord ++ tailWord_6575705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6575722 : List Nat := [3, 1, 3, 2, 1, 3, 2, 1, 1, 1, 5]
def baseStart_6575722 : Nat := 118140960795 + 6575722 * 2 ^ 59
def prefixEnd_6575722 : Nat := 4983230072969 + 3 ^ 40 * 6575722 * 2
def baseEnd_6575722 : Nat := 3376506036344426691133811

theorem tailTrace_6575722 : CollatzResearch.WordTrace tailWord_6575722 prefixEnd_6575722 3376506036344426691133811 := by
  unfold tailWord_6575722
  simp only [CollatzResearch.WordTrace]
  refine ⟨59959071170822428188154355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 159890856455526475168411613 59959071170822428188154355)
  ·
    refine ⟨89938606756233642282231533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59959071170822428188154355 89938606756233642282231533)
    ·
      refine ⟨33726977533587615855836825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 89938606756233642282231533 33726977533587615855836825)
      ·
        refine ⟨25295233150190711891877619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33726977533587615855836825 25295233150190711891877619)
        ·
          refine ⟨37942849725286067837816429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25295233150190711891877619 37942849725286067837816429)
          ·
            refine ⟨14228568646982275439181161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37942849725286067837816429 14228568646982275439181161)
            ·
              refine ⟨10671426485236706579385871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14228568646982275439181161 10671426485236706579385871)
              ·
                refine ⟨16007139727855059869078807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10671426485236706579385871 16007139727855059869078807)
                ·
                  refine ⟨24010709591782589803618211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16007139727855059869078807 24010709591782589803618211)
                  ·
                    refine ⟨36016064387673884705427317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24010709591782589803618211 36016064387673884705427317)
                    ·
                      refine ⟨3376506036344426691133811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36016064387673884705427317 3376506036344426691133811)
                      ·
                        rfl

theorem cell23_6575722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 2, 1, 1, 1, 5].length) (baseStart_6575722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6575722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6575722 prefixEnd_6575722 := by exact prefixLift 6575722
  have htrace : WordTrace (prefixWord ++ tailWord_6575722) baseStart_6575722 baseEnd_6575722 := by
    simpa [prefixWord, tailWord_6575722, baseEnd_6575722] using wordTrace_append hprefix tailTrace_6575722
  have hstable : (prefixWord ++ tailWord_6575722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6575722).length < 2 ^ (prefixWord ++ tailWord_6575722).sum := by decide
  have hdescent : baseEnd_6575722 < baseStart_6575722 := by decide
  rcases family_descends (prefixWord ++ tailWord_6575722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6575795 : List Nat := [1, 1, 1, 2, 3, 3, 1, 1, 1, 6, 3]
def baseStart_6575795 : Nat := 118140960795 + 6575795 * 2 ^ 59
def prefixEnd_6575795 : Nat := 4983230072969 + 3 ^ 40 * 6575795 * 2
def baseEnd_6575795 : Nat := 3376543520432204905520975

theorem tailTrace_6575795 : CollatzResearch.WordTrace tailWord_6575795 prefixEnd_6575795 3376543520432204905520975 := by
  unfold tailWord_6575795
  simp only [CollatzResearch.WordTrace]
  refine ⟨239838947212025246220024839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159892631474683497480016559 239838947212025246220024839)
  ·
    refine ⟨359758420818037869330037259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 239838947212025246220024839 359758420818037869330037259)
    ·
      refine ⟨539637631227056803995055889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 359758420818037869330037259 539637631227056803995055889)
      ·
        refine ⟨404728223420292602996291917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 539637631227056803995055889 404728223420292602996291917)
        ·
          refine ⟨151773083782609726123609469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 404728223420292602996291917 151773083782609726123609469)
          ·
            refine ⟨56914906418478647296353551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 151773083782609726123609469 56914906418478647296353551)
            ·
              refine ⟨85372359627717970944530327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56914906418478647296353551 85372359627717970944530327)
              ·
                refine ⟨128058539441576956416795491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 85372359627717970944530327 128058539441576956416795491)
                ·
                  refine ⟨192087809162365434625193237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 128058539441576956416795491 192087809162365434625193237)
                  ·
                    refine ⟨9004116054485879748055933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 192087809162365434625193237 9004116054485879748055933)
                    ·
                      refine ⟨3376543520432204905520975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9004116054485879748055933 3376543520432204905520975)
                      ·
                        rfl

theorem cell23_6575795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 1, 1, 6, 3].length) (baseStart_6575795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6575795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6575795 prefixEnd_6575795 := by exact prefixLift 6575795
  have htrace : WordTrace (prefixWord ++ tailWord_6575795) baseStart_6575795 baseEnd_6575795 := by
    simpa [prefixWord, tailWord_6575795, baseEnd_6575795] using wordTrace_append hprefix tailTrace_6575795
  have hstable : (prefixWord ++ tailWord_6575795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6575795).length < 2 ^ (prefixWord ++ tailWord_6575795).sum := by decide
  have hdescent : baseEnd_6575795 < baseStart_6575795 := by decide
  rcases family_descends (prefixWord ++ tailWord_6575795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6575812 : List Nat := [2, 3, 3, 1, 1, 1, 1, 2, 2, 4, 3]
def baseStart_6575812 : Nat := 118140960795 + 6575812 * 2 ^ 59
def prefixEnd_6575812 : Nat := 4983230072969 + 3 ^ 40 * 6575812 * 2
def baseEnd_6575812 : Nat := 3376552249603331339008397

theorem tailTrace_6575812 : CollatzResearch.WordTrace tailWord_6575812 prefixEnd_6575812 3376552249603331339008397 := by
  unfold tailWord_6575812
  simp only [CollatzResearch.WordTrace]
  refine ⟨119919783626481829061696845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159893044835309105415595793 119919783626481829061696845)
  ·
    refine ⟨44969918859930685898136317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 119919783626481829061696845 44969918859930685898136317)
    ·
      refine ⟨16863719572474007211801119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44969918859930685898136317 16863719572474007211801119)
      ·
        refine ⟨25295579358711010817701679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16863719572474007211801119 25295579358711010817701679)
        ·
          refine ⟨37943369038066516226552519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25295579358711010817701679 37943369038066516226552519)
          ·
            refine ⟨56915053557099774339828779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37943369038066516226552519 56915053557099774339828779)
            ·
              refine ⟨85372580335649661509743169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56915053557099774339828779 85372580335649661509743169)
              ·
                refine ⟨64029435251737246132307377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 85372580335649661509743169 64029435251737246132307377)
                ·
                  refine ⟨48022076438802934599230533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 64029435251737246132307377 48022076438802934599230533)
                  ·
                    refine ⟨9004139332275550237355725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 48022076438802934599230533 9004139332275550237355725)
                    ·
                      refine ⟨3376552249603331339008397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9004139332275550237355725 3376552249603331339008397)
                      ·
                        rfl

theorem cell23_6575812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 2, 2, 4, 3].length) (baseStart_6575812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6575812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6575812 prefixEnd_6575812 := by exact prefixLift 6575812
  have htrace : WordTrace (prefixWord ++ tailWord_6575812) baseStart_6575812 baseEnd_6575812 := by
    simpa [prefixWord, tailWord_6575812, baseEnd_6575812] using wordTrace_append hprefix tailTrace_6575812
  have hstable : (prefixWord ++ tailWord_6575812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6575812).length < 2 ^ (prefixWord ++ tailWord_6575812).sum := by decide
  have hdescent : baseEnd_6575812 < baseStart_6575812 := by decide
  rcases family_descends (prefixWord ++ tailWord_6575812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6575815 : List Nat := [1, 1, 4, 1, 1, 1, 5, 2, 7]
def baseStart_6575815 : Nat := 118140960795 + 6575815 * 2 ^ 59
def prefixEnd_6575815 : Nat := 4983230072969 + 3 ^ 40 * 6575815 * 2
def baseEnd_6575815 : Nat := 375172643338366091918987

theorem tailTrace_6575815 : CollatzResearch.WordTrace tailWord_6575815 prefixEnd_6575815 375172643338366091918987 := by
  unfold tailWord_6575815
  simp only [CollatzResearch.WordTrace]
  refine ⟨239839676671952789635752899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159893117781301859757168599 239839676671952789635752899)
  ·
    refine ⟨359759515007929184453629349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 239839676671952789635752899 359759515007929184453629349)
    ·
      refine ⟨67454909063986722085055503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 359759515007929184453629349 67454909063986722085055503)
      ·
        refine ⟨101182363595980083127583255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67454909063986722085055503 101182363595980083127583255)
        ·
          refine ⟨151773545393970124691374883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101182363595980083127583255 151773545393970124691374883)
          ·
            refine ⟨227660318090955187037062325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 151773545393970124691374883 227660318090955187037062325)
            ·
              refine ⟨21343154821027048784724593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 227660318090955187037062325 21343154821027048784724593)
              ·
                refine ⟨16007366115770286588543445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21343154821027048784724593 16007366115770286588543445)
                ·
                  refine ⟨375172643338366091918987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16007366115770286588543445 375172643338366091918987)
                  ·
                    rfl

theorem cell23_6575815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 5, 2, 7].length) (baseStart_6575815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6575815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6575815 prefixEnd_6575815 := by exact prefixLift 6575815
  have htrace : WordTrace (prefixWord ++ tailWord_6575815) baseStart_6575815 baseEnd_6575815 := by
    simpa [prefixWord, tailWord_6575815, baseEnd_6575815] using wordTrace_append hprefix tailTrace_6575815
  have hstable : (prefixWord ++ tailWord_6575815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6575815).length < 2 ^ (prefixWord ++ tailWord_6575815).sum := by decide
  have hdescent : baseEnd_6575815 < baseStart_6575815 := by decide
  rcases family_descends (prefixWord ++ tailWord_6575815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6575830 : List Nat := [5, 2, 1, 3, 1, 1, 1, 3, 1, 3, 2]
def baseStart_6575830 : Nat := 118140960795 + 6575830 * 2 ^ 59
def prefixEnd_6575830 : Nat := 4983230072969 + 3 ^ 40 * 6575830 * 2
def baseEnd_6575830 : Nat := 3376561492255112268583315

theorem tailTrace_6575830 : CollatzResearch.WordTrace tailWord_6575830 prefixEnd_6575830 3376561492255112268583315 := by
  unfold tailWord_6575830
  simp only [CollatzResearch.WordTrace]
  refine ⟨14990013985431152949846809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 159893482511265631465032629 14990013985431152949846809)
  ·
    refine ⟨11242510489073364712385107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14990013985431152949846809 11242510489073364712385107)
    ·
      refine ⟨16863765733610047068577661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11242510489073364712385107 16863765733610047068577661)
      ·
        refine ⟨6323912150103767650716623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16863765733610047068577661 6323912150103767650716623)
        ·
          refine ⟨9485868225155651476074935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6323912150103767650716623 9485868225155651476074935)
          ·
            refine ⟨14228802337733477214112403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9485868225155651476074935 14228802337733477214112403)
            ·
              refine ⟨21343203506600215821168605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14228802337733477214112403 21343203506600215821168605)
              ·
                refine ⟨8003701314975080932938227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21343203506600215821168605 8003701314975080932938227)
                ·
                  refine ⟨12005551972462621399407341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8003701314975080932938227 12005551972462621399407341)
                  ·
                    refine ⟨4502081989673483024777753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12005551972462621399407341 4502081989673483024777753)
                    ·
                      refine ⟨3376561492255112268583315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4502081989673483024777753 3376561492255112268583315)
                      ·
                        rfl

theorem cell23_6575830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 1, 3, 1, 3, 2].length) (baseStart_6575830 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6575830 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6575830 prefixEnd_6575830 := by exact prefixLift 6575830
  have htrace : WordTrace (prefixWord ++ tailWord_6575830) baseStart_6575830 baseEnd_6575830 := by
    simpa [prefixWord, tailWord_6575830, baseEnd_6575830] using wordTrace_append hprefix tailTrace_6575830
  have hstable : (prefixWord ++ tailWord_6575830).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6575830).length < 2 ^ (prefixWord ++ tailWord_6575830).sum := by decide
  have hdescent : baseEnd_6575830 < baseStart_6575830 := by decide
  rcases family_descends (prefixWord ++ tailWord_6575830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6575852 : List Nat := [2, 2, 1, 1, 2, 2, 2, 1, 1, 7, 2]
def baseStart_6575852 : Nat := 118140960795 + 6575852 * 2 ^ 59
def prefixEnd_6575852 : Nat := 4983230072969 + 3 ^ 40 * 6575852 * 2
def baseEnd_6575852 : Nat := 3376572788829511182508213

theorem tailTrace_6575852 : CollatzResearch.WordTrace tailWord_6575852 prefixEnd_6575852 3376572788829511182508213 := by
  unfold tailWord_6575852
  simp only [CollatzResearch.WordTrace]
  refine ⟨119920513086409372477424905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159894017448545829969899873 119920513086409372477424905)
  ·
    refine ⟨89940384814807029358068679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119920513086409372477424905 89940384814807029358068679)
    ·
      refine ⟨134910577222210544037103019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89940384814807029358068679 134910577222210544037103019)
      ·
        refine ⟨202365865833315816055654529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134910577222210544037103019 202365865833315816055654529)
        ·
          refine ⟨151774399374986862041740897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 202365865833315816055654529 151774399374986862041740897)
          ·
            refine ⟨113830799531240146531305673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 151774399374986862041740897 113830799531240146531305673)
            ·
              refine ⟨85373099648430109898479255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 113830799531240146531305673 85373099648430109898479255)
              ·
                refine ⟨128059649472645164847718883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 85373099648430109898479255 128059649472645164847718883)
                ·
                  refine ⟨192089474208967747271578325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 128059649472645164847718883 192089474208967747271578325)
                  ·
                    refine ⟨4502097051772681576677617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 192089474208967747271578325 4502097051772681576677617)
                    ·
                      refine ⟨3376572788829511182508213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4502097051772681576677617 3376572788829511182508213)
                      ·
                        rfl

theorem cell23_6575852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 7, 2].length) (baseStart_6575852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6575852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6575852 prefixEnd_6575852 := by exact prefixLift 6575852
  have htrace : WordTrace (prefixWord ++ tailWord_6575852) baseStart_6575852 baseEnd_6575852 := by
    simpa [prefixWord, tailWord_6575852, baseEnd_6575852] using wordTrace_append hprefix tailTrace_6575852
  have hstable : (prefixWord ++ tailWord_6575852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6575852).length < 2 ^ (prefixWord ++ tailWord_6575852).sum := by decide
  have hdescent : baseEnd_6575852 < baseStart_6575852 := by decide
  rcases family_descends (prefixWord ++ tailWord_6575852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6575855 : List Nat := [1, 1, 2, 1, 5, 1, 2, 1, 1, 1, 7]
def baseStart_6575855 : Nat := 118140960795 + 6575855 * 2 ^ 59
def prefixEnd_6575855 : Nat := 4983230072969 + 3 ^ 40 * 6575855 * 2
def baseEnd_6575855 : Nat := 3376574329271474670770699

theorem tailTrace_6575855 : CollatzResearch.WordTrace tailWord_6575855 prefixEnd_6575855 3376574329271474670770699 := by
  unfold tailWord_6575855
  simp only [CollatzResearch.WordTrace]
  refine ⟨239841135591807876467209019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159894090394538584311472679 239841135591807876467209019)
  ·
    refine ⟨359761703387711814700813529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 239841135591807876467209019 359761703387711814700813529)
    ·
      refine ⟨269821277540783861025610147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 359761703387711814700813529 269821277540783861025610147)
      ·
        refine ⟨404731916311175791538415221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 269821277540783861025610147 404731916311175791538415221)
        ·
          refine ⟨37943617154172730456726427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 404731916311175791538415221 37943617154172730456726427)
          ·
            refine ⟨56915425731259095685089641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37943617154172730456726427 56915425731259095685089641)
            ·
              refine ⟨42686569298444321763817231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56915425731259095685089641 42686569298444321763817231)
              ·
                refine ⟨64029853947666482645725847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42686569298444321763817231 64029853947666482645725847)
                ·
                  refine ⟨96044780921499723968588771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 64029853947666482645725847 96044780921499723968588771)
                  ·
                    refine ⟨144067171382249585952883157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 96044780921499723968588771 144067171382249585952883157)
                    ·
                      refine ⟨3376574329271474670770699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 144067171382249585952883157 3376574329271474670770699)
                      ·
                        rfl

theorem cell23_6575855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 2, 1, 1, 1, 7].length) (baseStart_6575855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6575855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6575855 prefixEnd_6575855 := by exact prefixLift 6575855
  have htrace : WordTrace (prefixWord ++ tailWord_6575855) baseStart_6575855 baseEnd_6575855 := by
    simpa [prefixWord, tailWord_6575855, baseEnd_6575855] using wordTrace_append hprefix tailTrace_6575855
  have hstable : (prefixWord ++ tailWord_6575855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6575855).length < 2 ^ (prefixWord ++ tailWord_6575855).sum := by decide
  have hdescent : baseEnd_6575855 < baseStart_6575855 := by decide
  rcases family_descends (prefixWord ++ tailWord_6575855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6575860 : List Nat := [2, 6, 1, 1, 1, 3, 1, 1, 1, 4, 2]
def baseStart_6575860 : Nat := 118140960795 + 6575860 * 2 ^ 59
def prefixEnd_6575860 : Nat := 4983230072969 + 3 ^ 40 * 6575860 * 2
def baseEnd_6575860 : Nat := 3376576896674747151208177

theorem tailTrace_6575860 : CollatzResearch.WordTrace tailWord_6575860 prefixEnd_6575860 3376576896674747151208177 := by
  unfold tailWord_6575860
  simp only [CollatzResearch.WordTrace]
  refine ⟨119920658978394881160570517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159894211971193174880760689 119920658978394881160570517)
  ·
    refine ⟨5621280889612260054401743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 119920658978394881160570517 5621280889612260054401743)
    ·
      refine ⟨8431921334418390081602615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5621280889612260054401743 8431921334418390081602615)
      ·
        refine ⟨12647882001627585122403923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8431921334418390081602615 12647882001627585122403923)
        ·
          refine ⟨18971823002441377683605885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12647882001627585122403923 18971823002441377683605885)
          ·
            refine ⟨7114433625915516631352207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18971823002441377683605885 7114433625915516631352207)
            ·
              refine ⟨10671650438873274947028311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7114433625915516631352207 10671650438873274947028311)
              ·
                refine ⟨16007475658309912420542467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10671650438873274947028311 16007475658309912420542467)
                ·
                  refine ⟨24011213487464868630813701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16007475658309912420542467 24011213487464868630813701)
                  ·
                    refine ⟨4502102528899662868277569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24011213487464868630813701 4502102528899662868277569)
                    ·
                      refine ⟨3376576896674747151208177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4502102528899662868277569 3376576896674747151208177)
                      ·
                        rfl

theorem cell23_6575860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 3, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 3, 1, 1, 1, 4, 2].length) (baseStart_6575860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6575860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6575860 prefixEnd_6575860 := by exact prefixLift 6575860
  have htrace : WordTrace (prefixWord ++ tailWord_6575860) baseStart_6575860 baseEnd_6575860 := by
    simpa [prefixWord, tailWord_6575860, baseEnd_6575860] using wordTrace_append hprefix tailTrace_6575860
  have hstable : (prefixWord ++ tailWord_6575860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6575860).length < 2 ^ (prefixWord ++ tailWord_6575860).sum := by decide
  have hdescent : baseEnd_6575860 < baseStart_6575860 := by decide
  rcases family_descends (prefixWord ++ tailWord_6575860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6575862 : List Nat := [5, 1, 1, 1, 1, 3, 1, 2, 1, 7]
def baseStart_6575862 : Nat := 118140960795 + 6575862 * 2 ^ 59
def prefixEnd_6575862 : Nat := 4983230072969 + 3 ^ 40 * 6575862 * 2
def baseEnd_6575862 : Nat := 1125525974545352047794389

theorem tailTrace_6575862 : CollatzResearch.WordTrace tailWord_6575862 prefixEnd_6575862 1125525974545352047794389 := by
  unfold tailWord_6575862
  simp only [CollatzResearch.WordTrace]
  refine ⟨14990086931423907291419615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 159894260601855011108475893 14990086931423907291419615)
  ·
    refine ⟨22485130397135860937129423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14990086931423907291419615 22485130397135860937129423)
    ·
      refine ⟨33727695595703791405694135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22485130397135860937129423 33727695595703791405694135)
      ·
        refine ⟨50591543393555687108541203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33727695595703791405694135 50591543393555687108541203)
        ·
          refine ⟨75887315090333530662811805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50591543393555687108541203 75887315090333530662811805)
          ·
            refine ⟨28457743158875073998554427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 75887315090333530662811805 28457743158875073998554427)
            ·
              refine ⟨42686614738312610997831641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28457743158875073998554427 42686614738312610997831641)
              ·
                refine ⟨32014961053734458248373731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42686614738312610997831641 32014961053734458248373731)
                ·
                  refine ⟨48022441580601687372560597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32014961053734458248373731 48022441580601687372560597)
                  ·
                    refine ⟨1125525974545352047794389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 48022441580601687372560597 1125525974545352047794389)
                    ·
                      rfl

theorem cell23_6575862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 1, 2, 1, 7].length) (baseStart_6575862 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6575862 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6575862 prefixEnd_6575862 := by exact prefixLift 6575862
  have htrace : WordTrace (prefixWord ++ tailWord_6575862) baseStart_6575862 baseEnd_6575862 := by
    simpa [prefixWord, tailWord_6575862, baseEnd_6575862] using wordTrace_append hprefix tailTrace_6575862
  have hstable : (prefixWord ++ tailWord_6575862).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6575862).length < 2 ^ (prefixWord ++ tailWord_6575862).sum := by decide
  have hdescent : baseEnd_6575862 < baseStart_6575862 := by decide
  rcases family_descends (prefixWord ++ tailWord_6575862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6575882 : List Nat := [3, 1, 2, 2, 1, 3, 2, 1, 1, 3, 4]
def baseStart_6575882 : Nat := 118140960795 + 6575882 * 2 ^ 59
def prefixEnd_6575882 : Nat := 4983230072969 + 3 ^ 40 * 6575882 * 2
def baseEnd_6575882 : Nat := 3376588193249146065133075

theorem tailTrace_6575882 : CollatzResearch.WordTrace tailWord_6575882 prefixEnd_6575882 3376588193249146065133075 := by
  unfold tailWord_6575882
  simp only [CollatzResearch.WordTrace]
  refine ⟨59960530090677515019610475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 159894746908473373385627933 59960530090677515019610475)
  ·
    refine ⟨89940795136016272529415713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59960530090677515019610475 89940795136016272529415713)
    ·
      refine ⟨67455596352012204397061785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89940795136016272529415713 67455596352012204397061785)
      ·
        refine ⟨50591697264009153297796339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67455596352012204397061785 50591697264009153297796339)
        ·
          refine ⟨75887545896013729946694509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50591697264009153297796339 75887545896013729946694509)
          ·
            refine ⟨28457829711005148730010441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 75887545896013729946694509 28457829711005148730010441)
            ·
              refine ⟨21343372283253861547507831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28457829711005148730010441 21343372283253861547507831)
              ·
                refine ⟨32015058424880792321261747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21343372283253861547507831 32015058424880792321261747)
                ·
                  refine ⟨48022587637321188481892621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32015058424880792321261747 48022587637321188481892621)
                  ·
                    refine ⟨18008470363995445680709733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 48022587637321188481892621 18008470363995445680709733)
                    ·
                      refine ⟨3376588193249146065133075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18008470363995445680709733 3376588193249146065133075)
                      ·
                        rfl

theorem cell23_6575882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 2, 1, 1, 3, 4].length) (baseStart_6575882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6575882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6575882 prefixEnd_6575882 := by exact prefixLift 6575882
  have htrace : WordTrace (prefixWord ++ tailWord_6575882) baseStart_6575882 baseEnd_6575882 := by
    simpa [prefixWord, tailWord_6575882, baseEnd_6575882] using wordTrace_append hprefix tailTrace_6575882
  have hstable : (prefixWord ++ tailWord_6575882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6575882).length < 2 ^ (prefixWord ++ tailWord_6575882).sum := by decide
  have hdescent : baseEnd_6575882 < baseStart_6575882 := by decide
  rcases family_descends (prefixWord ++ tailWord_6575882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6575909 : List Nat := [1, 3, 1, 2, 3, 2, 3, 1, 3, 4]
def baseStart_6575909 : Nat := 118140960795 + 6575909 * 2 ^ 59
def prefixEnd_6575909 : Nat := 4983230072969 + 3 ^ 40 * 6575909 * 2
def baseEnd_6575909 : Nat := 1125534019075605819831817

theorem tailTrace_6575909 : CollatzResearch.WordTrace tailWord_6575909 prefixEnd_6575909 1125534019075605819831817 := by
  unfold tailWord_6575909
  simp only [CollatzResearch.WordTrace]
  refine ⟨239843105133612243689674781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159895403422408162459783187 239843105133612243689674781)
  ·
    refine ⟨89941164425104591383628043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 239843105133612243689674781 89941164425104591383628043)
    ·
      refine ⟨134911746637656887075442065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89941164425104591383628043 134911746637656887075442065)
      ·
        refine ⟨101183809978242665306581549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 134911746637656887075442065 101183809978242665306581549)
        ·
          refine ⟨37943928741840999489968081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 101183809978242665306581549 37943928741840999489968081)
          ·
            refine ⟨28457946556380749617476061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37943928741840999489968081 28457946556380749617476061)
            ·
              refine ⟨10671729958642781106553523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28457946556380749617476061 10671729958642781106553523)
              ·
                refine ⟨16007594937964171659830285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10671729958642781106553523 16007594937964171659830285)
                ·
                  refine ⟨6002848101736564372436357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16007594937964171659830285 6002848101736564372436357)
                  ·
                    refine ⟨1125534019075605819831817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6002848101736564372436357 1125534019075605819831817)
                    ·
                      rfl

theorem cell23_6575909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 3, 1, 3, 4].length) (baseStart_6575909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6575909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6575909 prefixEnd_6575909 := by exact prefixLift 6575909
  have htrace : WordTrace (prefixWord ++ tailWord_6575909) baseStart_6575909 baseEnd_6575909 := by
    simpa [prefixWord, tailWord_6575909, baseEnd_6575909] using wordTrace_append hprefix tailTrace_6575909
  have hstable : (prefixWord ++ tailWord_6575909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6575909).length < 2 ^ (prefixWord ++ tailWord_6575909).sum := by decide
  have hdescent : baseEnd_6575909 < baseStart_6575909 := by decide
  rcases family_descends (prefixWord ++ tailWord_6575909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6575932 : List Nat := [2, 2, 2, 2, 1, 1, 2, 1, 2, 5, 3]
def baseStart_6575932 : Nat := 118140960795 + 6575932 * 2 ^ 59
def prefixEnd_6575932 : Nat := 4983230072969 + 3 ^ 40 * 6575932 * 2
def baseEnd_6575932 : Nat := 3376613867281870869507845

theorem tailTrace_6575932 : CollatzResearch.WordTrace tailWord_6575932 prefixEnd_6575932 3376613867281870869507845 := by
  unfold tailWord_6575932
  simp only [CollatzResearch.WordTrace]
  refine ⟨119921972006264459308881025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159895962675019279078508033 119921972006264459308881025)
  ·
    refine ⟨89941479004698344481660769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119921972006264459308881025 89941479004698344481660769)
    ·
      refine ⟨67456109253523758361245577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89941479004698344481660769 67456109253523758361245577)
      ·
        refine ⟨50592081940142818770934183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67456109253523758361245577 50592081940142818770934183)
        ·
          refine ⟨75888122910214228156401275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50592081940142818770934183 75888122910214228156401275)
          ·
            refine ⟨113832184365321342234601913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75888122910214228156401275 113832184365321342234601913)
            ·
              refine ⟨85374138273991006675951435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 113832184365321342234601913 85374138273991006675951435)
              ·
                refine ⟨128061207410986510013927153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 85374138273991006675951435 128061207410986510013927153)
                ·
                  refine ⟨96045905558239882510445365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 128061207410986510013927153 96045905558239882510445365)
                  ·
                    refine ⟨9004303646084988985354253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 96045905558239882510445365 9004303646084988985354253)
                    ·
                      refine ⟨3376613867281870869507845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9004303646084988985354253 3376613867281870869507845)
                      ·
                        rfl

theorem cell23_6575932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 1, 2, 5, 3].length) (baseStart_6575932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6575932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6575932 prefixEnd_6575932 := by exact prefixLift 6575932
  have htrace : WordTrace (prefixWord ++ tailWord_6575932) baseStart_6575932 baseEnd_6575932 := by
    simpa [prefixWord, tailWord_6575932, baseEnd_6575932] using wordTrace_append hprefix tailTrace_6575932
  have hstable : (prefixWord ++ tailWord_6575932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6575932).length < 2 ^ (prefixWord ++ tailWord_6575932).sum := by decide
  have hdescent : baseEnd_6575932 < baseStart_6575932 := by decide
  rcases family_descends (prefixWord ++ tailWord_6575932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6575989 : List Nat := [1, 3, 4, 1, 1, 1, 1, 3, 3, 1, 4]
def baseStart_6575989 : Nat := 118140960795 + 6575989 * 2 ^ 59
def prefixEnd_6575989 : Nat := 4983230072969 + 3 ^ 40 * 6575989 * 2
def baseEnd_6575989 : Nat := 3376643135679177146495083

theorem tailTrace_6575989 : CollatzResearch.WordTrace tailWord_6575989 prefixEnd_6575989 3376643135679177146495083 := by
  unfold tailWord_6575989
  simp only [CollatzResearch.WordTrace]
  refine ⟨239846022973322417352587021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159897348648881611568391347 239846022973322417352587021)
  ·
    refine ⟨89942258614995906507220133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 239846022973322417352587021 89942258614995906507220133)
    ·
      refine ⟨16864173490311732470103775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 89942258614995906507220133 16864173490311732470103775)
      ·
        refine ⟨25296260235467598705155663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16864173490311732470103775 25296260235467598705155663)
        ·
          refine ⟨37944390353201398057733495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25296260235467598705155663 37944390353201398057733495)
          ·
            refine ⟨56916585529802097086600243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37944390353201398057733495 56916585529802097086600243)
            ·
              refine ⟨85374878294703145629900365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56916585529802097086600243 85374878294703145629900365)
              ·
                refine ⟨32015579360513679611212637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 85374878294703145629900365 32015579360513679611212637)
                ·
                  refine ⟨12005842260192629854204739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32015579360513679611212637 12005842260192629854204739)
                  ·
                    refine ⟨18008763390288944781307109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12005842260192629854204739 18008763390288944781307109)
                    ·
                      refine ⟨3376643135679177146495083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18008763390288944781307109 3376643135679177146495083)
                      ·
                        rfl

theorem cell23_6575989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 3, 3, 1, 4].length) (baseStart_6575989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6575989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6575989 prefixEnd_6575989 := by exact prefixLift 6575989
  have htrace : WordTrace (prefixWord ++ tailWord_6575989) baseStart_6575989 baseEnd_6575989 := by
    simpa [prefixWord, tailWord_6575989, baseEnd_6575989] using wordTrace_append hprefix tailTrace_6575989
  have hstable : (prefixWord ++ tailWord_6575989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6575989).length < 2 ^ (prefixWord ++ tailWord_6575989).sum := by decide
  have hdescent : baseEnd_6575989 < baseStart_6575989 := by decide
  rcases family_descends (prefixWord ++ tailWord_6575989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6576023 : List Nat := [1, 1, 3, 3, 1, 4, 2, 1, 3, 2, 2]
def baseStart_6576023 : Nat := 118140960795 + 6576023 * 2 ^ 59
def prefixEnd_6576023 : Nat := 4983230072969 + 3 ^ 40 * 6576023 * 2
def baseEnd_6576023 : Nat := 3376660594021430013469927

theorem tailTrace_6576023 : CollatzResearch.WordTrace tailWord_6576023 prefixEnd_6576023 3376660594021430013469927 := by
  unfold tailWord_6576023
  simp only [CollatzResearch.WordTrace]
  refine ⟨239847263055199241159324723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159898175370132827439549815 239847263055199241159324723)
  ·
    refine ⟨359770894582798861738987085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 239847263055199241159324723 359770894582798861738987085)
    ·
      refine ⟨134914085468549573152120157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 359770894582798861738987085 134914085468549573152120157)
      ·
        refine ⟨50592782050706089932045059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 134914085468549573152120157 50592782050706089932045059)
        ·
          refine ⟨75889173076059134898067589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50592782050706089932045059 75889173076059134898067589)
          ·
            refine ⟨14229219951761087793387673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 75889173076059134898067589 14229219951761087793387673)
            ·
              refine ⟨10671914963820815845040755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14229219951761087793387673 10671914963820815845040755)
              ·
                refine ⟨16007872445731223767561133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10671914963820815845040755 16007872445731223767561133)
                ·
                  refine ⟨6002952167149208912835425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16007872445731223767561133 6002952167149208912835425)
                  ·
                    refine ⟨4502214125361906684626569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6002952167149208912835425 4502214125361906684626569)
                    ·
                      refine ⟨3376660594021430013469927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4502214125361906684626569 3376660594021430013469927)
                      ·
                        rfl

theorem cell23_6576023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 2, 1, 3, 2, 2].length) (baseStart_6576023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6576023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6576023 prefixEnd_6576023 := by exact prefixLift 6576023
  have htrace : WordTrace (prefixWord ++ tailWord_6576023) baseStart_6576023 baseEnd_6576023 := by
    simpa [prefixWord, tailWord_6576023, baseEnd_6576023] using wordTrace_append hprefix tailTrace_6576023
  have hstable : (prefixWord ++ tailWord_6576023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6576023).length < 2 ^ (prefixWord ++ tailWord_6576023).sum := by decide
  have hdescent : baseEnd_6576023 < baseStart_6576023 := by decide
  rcases family_descends (prefixWord ++ tailWord_6576023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6576033 : List Nat := [1, 2, 3, 4, 3, 1, 1, 1, 1, 6]
def baseStart_6576033 : Nat := 118140960795 + 6576033 * 2 ^ 59
def prefixEnd_6576033 : Nat := 4983230072969 + 3 ^ 40 * 6576033 * 2
def baseEnd_6576033 : Nat := 1125555242942658324781627

theorem tailTrace_6576033 : CollatzResearch.WordTrace tailWord_6576033 prefixEnd_6576033 1125555242942658324781627 := by
  unfold tailWord_6576033
  simp only [CollatzResearch.WordTrace]
  refine ⟨239847627785163012867188753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159898418523442008578125835 239847627785163012867188753)
  ·
    refine ⟨179885720838872259650391565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 239847627785163012867188753 179885720838872259650391565)
    ·
      refine ⟨67457145314577097368896837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 179885720838872259650391565 67457145314577097368896837)
      ·
        refine ⟨12648214746483205756668157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 67457145314577097368896837 12648214746483205756668157)
        ·
          refine ⟨4743080529931202158750559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12648214746483205756668157 4743080529931202158750559)
          ·
            refine ⟨7114620794896803238125839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4743080529931202158750559 7114620794896803238125839)
            ·
              refine ⟨10671931192345204857188759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7114620794896803238125839 10671931192345204857188759)
              ·
                refine ⟨16007896788517807285783139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10671931192345204857188759 16007896788517807285783139)
                ·
                  refine ⟨24011845182776710928674709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16007896788517807285783139 24011845182776710928674709)
                  ·
                    refine ⟨1125555242942658324781627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24011845182776710928674709 1125555242942658324781627)
                    ·
                      rfl

theorem cell23_6576033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 3, 1, 1, 1, 1, 6].length) (baseStart_6576033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6576033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6576033 prefixEnd_6576033 := by exact prefixLift 6576033
  have htrace : WordTrace (prefixWord ++ tailWord_6576033) baseStart_6576033 baseEnd_6576033 := by
    simpa [prefixWord, tailWord_6576033, baseEnd_6576033] using wordTrace_append hprefix tailTrace_6576033
  have hstable : (prefixWord ++ tailWord_6576033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6576033).length < 2 ^ (prefixWord ++ tailWord_6576033).sum := by decide
  have hdescent : baseEnd_6576033 < baseStart_6576033 := by decide
  rcases family_descends (prefixWord ++ tailWord_6576033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6576036 : List Nat := [2, 3, 1, 2, 1, 5, 1, 1, 1, 2, 4]
def baseStart_6576036 : Nat := 118140960795 + 6576036 * 2 ^ 59
def prefixEnd_6576036 : Nat := 4983230072969 + 3 ^ 40 * 6576036 * 2
def baseEnd_6576036 : Nat := 3376667269269938462607367

theorem tailTrace_6576036 : CollatzResearch.WordTrace tailWord_6576036 prefixEnd_6576036 3376667269269938462607367 := by
  unfold tailWord_6576036
  simp only [CollatzResearch.WordTrace]
  refine ⟨119923868602076072189773981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159898491469434762919698641 119923868602076072189773981)
  ·
    refine ⟨44971450725778527071165243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 119923868602076072189773981 44971450725778527071165243)
    ·
      refine ⟨67457176088667790606747865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44971450725778527071165243 67457176088667790606747865)
      ·
        refine ⟨50592882066500842955060899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67457176088667790606747865 50592882066500842955060899)
        ·
          refine ⟨75889323099751264432591349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50592882066500842955060899 75889323099751264432591349)
          ·
            refine ⟨7114624040601681040555439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 75889323099751264432591349 7114624040601681040555439)
            ·
              refine ⟨10671936060902521560833159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7114624040601681040555439 10671936060902521560833159)
              ·
                refine ⟨16007904091353782341249739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10671936060902521560833159 16007904091353782341249739)
                ·
                  refine ⟨24011856137030673511874609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16007904091353782341249739 24011856137030673511874609)
                  ·
                    refine ⟨18008892102773005133905957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24011856137030673511874609 18008892102773005133905957)
                    ·
                      refine ⟨3376667269269938462607367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18008892102773005133905957 3376667269269938462607367)
                      ·
                        rfl

theorem cell23_6576036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 5, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 5, 1, 1, 1, 2, 4].length) (baseStart_6576036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6576036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6576036 prefixEnd_6576036 := by exact prefixLift 6576036
  have htrace : WordTrace (prefixWord ++ tailWord_6576036) baseStart_6576036 baseEnd_6576036 := by
    simpa [prefixWord, tailWord_6576036, baseEnd_6576036] using wordTrace_append hprefix tailTrace_6576036
  have hstable : (prefixWord ++ tailWord_6576036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6576036).length < 2 ^ (prefixWord ++ tailWord_6576036).sum := by decide
  have hdescent : baseEnd_6576036 < baseStart_6576036 := by decide
  rcases family_descends (prefixWord ++ tailWord_6576036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6576040 : List Nat := [2, 1, 6, 2, 1, 1, 2, 2, 1, 1, 4]
def baseStart_6576040 : Nat := 118140960795 + 6576040 * 2 ^ 59
def prefixEnd_6576040 : Nat := 4983230072969 + 3 ^ 40 * 6576040 * 2
def baseEnd_6576040 : Nat := 3376669323192556446957349

theorem tailTrace_6576040 : CollatzResearch.WordTrace tailWord_6576040 prefixEnd_6576040 3376669323192556446957349 := by
  unfold tailWord_6576040
  simp only [CollatzResearch.WordTrace]
  refine ⟨119923941548068826531346787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159898588730758435375129049 119923941548068826531346787)
  ·
    refine ⟨179885912322103239797020181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119923941548068826531346787 179885912322103239797020181)
    ·
      refine ⟨8432152140098589365485321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 179885912322103239797020181 8432152140098589365485321)
      ·
        refine ⟨6324114105073942024113991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8432152140098589365485321 6324114105073942024113991)
        ·
          refine ⟨9486171157610913036170987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6324114105073942024113991 9486171157610913036170987)
          ·
            refine ⟨14229256736416369554256481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9486171157610913036170987 14229256736416369554256481)
            ·
              refine ⟨10671942552312277165692361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14229256736416369554256481 10671942552312277165692361)
              ·
                refine ⟨8003956914234207874269271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10671942552312277165692361 8003956914234207874269271)
                ·
                  refine ⟨12005935371351311811403907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8003956914234207874269271 12005935371351311811403907)
                  ·
                    refine ⟨18008903057026967717105861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12005935371351311811403907 18008903057026967717105861)
                    ·
                      refine ⟨3376669323192556446957349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18008903057026967717105861 3376669323192556446957349)
                      ·
                        rfl

theorem cell23_6576040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 2, 2, 1, 1, 4].length) (baseStart_6576040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6576040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6576040 prefixEnd_6576040 := by exact prefixLift 6576040
  have htrace : WordTrace (prefixWord ++ tailWord_6576040) baseStart_6576040 baseEnd_6576040 := by
    simpa [prefixWord, tailWord_6576040, baseEnd_6576040] using wordTrace_append hprefix tailTrace_6576040
  have hstable : (prefixWord ++ tailWord_6576040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6576040).length < 2 ^ (prefixWord ++ tailWord_6576040).sum := by decide
  have hdescent : baseEnd_6576040 < baseStart_6576040 := by decide
  rcases family_descends (prefixWord ++ tailWord_6576040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6576099 : List Nat := [1, 1, 1, 6, 1, 2, 1, 2, 2, 1, 5]
def baseStart_6576099 : Nat := 118140960795 + 6576099 * 2 ^ 59
def prefixEnd_6576099 : Nat := 4983230072969 + 3 ^ 40 * 6576099 * 2
def baseEnd_6576099 : Nat := 3376699618551171716119577

theorem tailTrace_6576099 : CollatzResearch.WordTrace tailWord_6576099 prefixEnd_6576099 3376699618551171716119577 := by
  unfold tailWord_6576099
  simp only [CollatzResearch.WordTrace]
  refine ⟨239850035002923906139091351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159900023335282604092727567 239850035002923906139091351)
  ·
    refine ⟨359775052504385859208637027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 239850035002923906139091351 359775052504385859208637027)
    ·
      refine ⟨539662578756578788812955541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 359775052504385859208637027 539662578756578788812955541)
      ·
        refine ⟨25296683379214630725607291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 539662578756578788812955541 25296683379214630725607291)
        ·
          refine ⟨37945025068821946088410937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25296683379214630725607291 37945025068821946088410937)
          ·
            refine ⟨28458768801616459566308203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37945025068821946088410937 28458768801616459566308203)
            ·
              refine ⟨42688153202424689349462305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28458768801616459566308203 42688153202424689349462305)
              ·
                refine ⟨32016114901818517012096729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42688153202424689349462305 32016114901818517012096729)
                ·
                  refine ⟨24012086176363887759072547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32016114901818517012096729 24012086176363887759072547)
                  ·
                    refine ⟨36018129264545831638608821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24012086176363887759072547 36018129264545831638608821)
                    ·
                      refine ⟨3376699618551171716119577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36018129264545831638608821 3376699618551171716119577)
                      ·
                        rfl

theorem cell23_6576099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 1, 2, 2, 1, 5].length) (baseStart_6576099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6576099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6576099 prefixEnd_6576099 := by exact prefixLift 6576099
  have htrace : WordTrace (prefixWord ++ tailWord_6576099) baseStart_6576099 baseEnd_6576099 := by
    simpa [prefixWord, tailWord_6576099, baseEnd_6576099] using wordTrace_append hprefix tailTrace_6576099
  have hstable : (prefixWord ++ tailWord_6576099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6576099).length < 2 ^ (prefixWord ++ tailWord_6576099).sum := by decide
  have hdescent : baseEnd_6576099 < baseStart_6576099 := by decide
  rcases family_descends (prefixWord ++ tailWord_6576099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6576113 : List Nat := [1, 2, 2, 2, 5, 1, 1, 2, 1, 4, 2]
def baseStart_6576113 : Nat := 118140960795 + 6576113 * 2 ^ 59
def prefixEnd_6576113 : Nat := 4983230072969 + 3 ^ 40 * 6576113 * 2
def baseEnd_6576113 : Nat := 3376706807280334661344513

theorem tailTrace_6576113 : CollatzResearch.WordTrace tailWord_6576113 prefixEnd_6576113 3376706807280334661344513 := by
  unfold tailWord_6576113
  simp only [CollatzResearch.WordTrace]
  refine ⟨239850545624873186530100993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159900363749915457686733995 239850545624873186530100993)
  ·
    refine ⟨179887909218654889897575745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 239850545624873186530100993 179887909218654889897575745)
    ·
      refine ⟨134915931913991167423181809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 179887909218654889897575745 134915931913991167423181809)
      ·
        refine ⟨101186948935493375567386357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 134915931913991167423181809 101186948935493375567386357)
        ·
          refine ⟨9486276462702503959442471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 101186948935493375567386357 9486276462702503959442471)
          ·
            refine ⟨14229414694053755939163707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9486276462702503959442471 14229414694053755939163707)
            ·
              refine ⟨21344122041080633908745561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14229414694053755939163707 21344122041080633908745561)
              ·
                refine ⟨16008091530810475431559171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21344122041080633908745561 16008091530810475431559171)
                ·
                  refine ⟨24012137296215713147338757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16008091530810475431559171 24012137296215713147338757)
                  ·
                    refine ⟨4502275743040446215126017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24012137296215713147338757 4502275743040446215126017)
                    ·
                      refine ⟨3376706807280334661344513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4502275743040446215126017 3376706807280334661344513)
                      ·
                        rfl

theorem cell23_6576113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 1, 2, 1, 4, 2].length) (baseStart_6576113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6576113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6576113 prefixEnd_6576113 := by exact prefixLift 6576113
  have htrace : WordTrace (prefixWord ++ tailWord_6576113) baseStart_6576113 baseEnd_6576113 := by
    simpa [prefixWord, tailWord_6576113, baseEnd_6576113] using wordTrace_append hprefix tailTrace_6576113
  have hstable : (prefixWord ++ tailWord_6576113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6576113).length < 2 ^ (prefixWord ++ tailWord_6576113).sum := by decide
  have hdescent : baseEnd_6576113 < baseStart_6576113 := by decide
  rcases family_descends (prefixWord ++ tailWord_6576113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6576136 : List Nat := [2, 1, 3, 2, 1, 2, 3, 4, 5]
def baseStart_6576136 : Nat := 118140960795 + 6576136 * 2 ^ 59
def prefixEnd_6576136 : Nat := 4983230072969 + 3 ^ 40 * 6576136 * 2
def baseEnd_6576136 : Nat := 375190957481709785706323

theorem tailTrace_6576136 : CollatzResearch.WordTrace tailWord_6576136 prefixEnd_6576136 375190957481709785706323 := by
  unfold tailWord_6576136
  simp only [CollatzResearch.WordTrace]
  refine ⟨119925692251894930729094131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159900923002526574305458841 119925692251894930729094131)
  ·
    refine ⟨179888538377842396093641197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119925692251894930729094131 179888538377842396093641197)
    ·
      refine ⟨67458201891690898535115449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 179888538377842396093641197 67458201891690898535115449)
      ·
        refine ⟨50593651418768173901336587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67458201891690898535115449 50593651418768173901336587)
        ·
          refine ⟨75890477128152260852004881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50593651418768173901336587 75890477128152260852004881)
          ·
            refine ⟨56917857846114195639003661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75890477128152260852004881 56917857846114195639003661)
            ·
              refine ⟨21344196692292823364626373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56917857846114195639003661 21344196692292823364626373)
              ·
                refine ⟨4002036879804904380867445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21344196692292823364626373 4002036879804904380867445)
                ·
                  refine ⟨375190957481709785706323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4002036879804904380867445 375190957481709785706323)
                  ·
                    rfl

theorem cell23_6576136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 3, 4, 5].length) (baseStart_6576136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6576136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6576136 prefixEnd_6576136 := by exact prefixLift 6576136
  have htrace : WordTrace (prefixWord ++ tailWord_6576136) baseStart_6576136 baseEnd_6576136 := by
    simpa [prefixWord, tailWord_6576136, baseEnd_6576136] using wordTrace_append hprefix tailTrace_6576136
  have hstable : (prefixWord ++ tailWord_6576136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6576136).length < 2 ^ (prefixWord ++ tailWord_6576136).sum := by decide
  have hdescent : baseEnd_6576136 < baseStart_6576136 := by decide
  rcases family_descends (prefixWord ++ tailWord_6576136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6576199 : List Nat := [1, 1, 4, 1, 3, 1, 1, 2, 2, 1, 6]
def baseStart_6576199 : Nat := 118140960795 + 6576199 * 2 ^ 59
def prefixEnd_6576199 : Nat := 4983230072969 + 3 ^ 40 * 6576199 * 2
def baseEnd_6576199 : Nat := 3376750966616621324869117

theorem tailTrace_6576199 : CollatzResearch.WordTrace tailWord_6576199 prefixEnd_6576199 3376750966616621324869117 := by
  unfold tailWord_6576199
  simp only [CollatzResearch.WordTrace]
  refine ⟨239853682302561623217731651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159902454868374415478487767 239853682302561623217731651)
  ·
    refine ⟨359780523453842434826597477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 239853682302561623217731651 359780523453842434826597477)
    ·
      refine ⟨67458848147595456529987027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 359780523453842434826597477 67458848147595456529987027)
      ·
        refine ⟨101188272221393184794980541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67458848147595456529987027 101188272221393184794980541)
        ·
          refine ⟨37945602083022444298117703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 101188272221393184794980541 37945602083022444298117703)
          ·
            refine ⟨56918403124533666447176555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37945602083022444298117703 56918403124533666447176555)
            ·
              refine ⟨85377604686800499670764833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56918403124533666447176555 85377604686800499670764833)
              ·
                refine ⟨64033203515100374753073625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 85377604686800499670764833 64033203515100374753073625)
                ·
                  refine ⟨48024902636325281064805219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 64033203515100374753073625 48024902636325281064805219)
                  ·
                    refine ⟨72037353954487921597207829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 48024902636325281064805219 72037353954487921597207829)
                    ·
                      refine ⟨3376750966616621324869117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 72037353954487921597207829 3376750966616621324869117)
                      ·
                        rfl

theorem cell23_6576199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 2, 2, 1, 6].length) (baseStart_6576199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6576199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6576199 prefixEnd_6576199 := by exact prefixLift 6576199
  have htrace : WordTrace (prefixWord ++ tailWord_6576199) baseStart_6576199 baseEnd_6576199 := by
    simpa [prefixWord, tailWord_6576199, baseEnd_6576199] using wordTrace_append hprefix tailTrace_6576199
  have hstable : (prefixWord ++ tailWord_6576199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6576199).length < 2 ^ (prefixWord ++ tailWord_6576199).sum := by decide
  have hdescent : baseEnd_6576199 < baseStart_6576199 := by decide
  rcases family_descends (prefixWord ++ tailWord_6576199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6576206 : List Nat := [4, 1, 1, 1, 1, 4, 1, 2, 1, 4, 3]
def baseStart_6576206 : Nat := 118140960795 + 6576206 * 2 ^ 59
def prefixEnd_6576206 : Nat := 4983230072969 + 3 ^ 40 * 6576206 * 2
def baseEnd_6576206 : Nat := 3376754560981202797481585

theorem tailTrace_6576206 : CollatzResearch.WordTrace tailWord_6576206 prefixEnd_6576206 3376754560981202797481585 := by
  unfold tailWord_6576206
  simp only [CollatzResearch.WordTrace]
  refine ⟨29981742201692032926654559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 159902625075690842275490981 29981742201692032926654559)
  ·
    refine ⟨44972613302538049389981839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29981742201692032926654559 44972613302538049389981839)
    ·
      refine ⟨67458919953807074084972759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44972613302538049389981839 67458919953807074084972759)
      ·
        refine ⟨101188379930710611127459139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67458919953807074084972759 101188379930710611127459139)
        ·
          refine ⟨151782569896065916691188709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101188379930710611127459139 151782569896065916691188709)
          ·
            refine ⟨28459231855512359379597883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 151782569896065916691188709 28459231855512359379597883)
            ·
              refine ⟨42688847783268539069396825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28459231855512359379597883 42688847783268539069396825)
              ·
                refine ⟨32016635837451404302047619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42688847783268539069396825 32016635837451404302047619)
                ·
                  refine ⟨48024953756177106453071429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32016635837451404302047619 48024953756177106453071429)
                  ·
                    refine ⟨9004678829283207459950893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 48024953756177106453071429 9004678829283207459950893)
                    ·
                      refine ⟨3376754560981202797481585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9004678829283207459950893 3376754560981202797481585)
                      ·
                        rfl

theorem cell23_6576206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 1, 2, 1, 4, 3].length) (baseStart_6576206 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6576206 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6576206 prefixEnd_6576206 := by exact prefixLift 6576206
  have htrace : WordTrace (prefixWord ++ tailWord_6576206) baseStart_6576206 baseEnd_6576206 := by
    simpa [prefixWord, tailWord_6576206, baseEnd_6576206] using wordTrace_append hprefix tailTrace_6576206
  have hstable : (prefixWord ++ tailWord_6576206).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6576206).length < 2 ^ (prefixWord ++ tailWord_6576206).sum := by decide
  have hdescent : baseEnd_6576206 < baseStart_6576206 := by decide
  rcases family_descends (prefixWord ++ tailWord_6576206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6576306 : List Nat := [3, 2, 1, 1, 1, 3, 1, 2, 3, 2, 4]
def baseStart_6576306 : Nat := 118140960795 + 6576306 * 2 ^ 59
def prefixEnd_6576306 : Nat := 4983230072969 + 3 ^ 40 * 6576306 * 2
def baseEnd_6576306 : Nat := 3376805909046652406231125

theorem tailTrace_6576306 : CollatzResearch.WordTrace tailWord_6576306 prefixEnd_6576306 3376805909046652406231125 := by
  unfold tailWord_6576306
  simp only [CollatzResearch.WordTrace]
  refine ⟨59964396228293495122969193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 159905056608782653661251181 59964396228293495122969193)
  ·
    refine ⟨44973297171220121342226895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59964396228293495122969193 44973297171220121342226895)
    ·
      refine ⟨67459945756830182013340343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44973297171220121342226895 67459945756830182013340343)
      ·
        refine ⟨101189918635245273020010515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67459945756830182013340343 101189918635245273020010515)
        ·
          refine ⟨151784877952867909530015773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101189918635245273020010515 151784877952867909530015773)
          ·
            refine ⟨56919329232325466073755915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 151784877952867909530015773 56919329232325466073755915)
            ·
              refine ⟨85378993848488199110633873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56919329232325466073755915 85378993848488199110633873)
              ·
                refine ⟨64034245386366149332975405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 85378993848488199110633873 64034245386366149332975405)
                ·
                  refine ⟨24012842019887305999865777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 64034245386366149332975405 24012842019887305999865777)
                  ·
                    refine ⟨18009631514915479499899333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24012842019887305999865777 18009631514915479499899333)
                    ·
                      refine ⟨3376805909046652406231125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18009631514915479499899333 3376805909046652406231125)
                      ·
                        rfl

theorem cell23_6576306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 2, 3, 2, 4].length) (baseStart_6576306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6576306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6576306 prefixEnd_6576306 := by exact prefixLift 6576306
  have htrace : WordTrace (prefixWord ++ tailWord_6576306) baseStart_6576306 baseEnd_6576306 := by
    simpa [prefixWord, tailWord_6576306, baseEnd_6576306] using wordTrace_append hprefix tailTrace_6576306
  have hstable : (prefixWord ++ tailWord_6576306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6576306).length < 2 ^ (prefixWord ++ tailWord_6576306).sum := by decide
  have hdescent : baseEnd_6576306 < baseStart_6576306 := by decide
  rcases family_descends (prefixWord ++ tailWord_6576306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6576343 : List Nat := [1, 1, 3, 2, 1, 2, 1, 4, 4, 1, 3]
def baseStart_6576343 : Nat := 118140960795 + 6576343 * 2 ^ 59
def prefixEnd_6576343 : Nat := 4983230072969 + 3 ^ 40 * 6576343 * 2
def baseEnd_6576343 : Nat := 3376824907830868761468455

theorem tailTrace_6576343 : CollatzResearch.WordTrace tailWord_6576343 prefixEnd_6576343 3376824907830868761468455 := by
  unfold tailWord_6576343
  simp only [CollatzResearch.WordTrace]
  refine ⟨239858934414039935810973683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159905956276026623873982455 239858934414039935810973683)
  ·
    refine ⟨359788401621059903716460525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 239858934414039935810973683 359788401621059903716460525)
    ·
      refine ⟨134920650607897463893672697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 359788401621059903716460525 134920650607897463893672697)
      ·
        refine ⟨101190487955923097920254523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 134920650607897463893672697 101190487955923097920254523)
        ·
          refine ⟨151785731933884646880381785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101190487955923097920254523 151785731933884646880381785)
          ·
            refine ⟨113839298950413485160286339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 151785731933884646880381785 113839298950413485160286339)
            ·
              refine ⟨170758948425620227740429509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 113839298950413485160286339 170758948425620227740429509)
              ·
                refine ⟨32017302829803792701330533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 170758948425620227740429509 32017302829803792701330533)
                ·
                  refine ⟨6003244280588211131499475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32017302829803792701330533 6003244280588211131499475)
                  ·
                    refine ⟨9004866420882316697249213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6003244280588211131499475 9004866420882316697249213)
                    ·
                      refine ⟨3376824907830868761468455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9004866420882316697249213 3376824907830868761468455)
                      ·
                        rfl

theorem cell23_6576343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 4, 4, 1, 3].length) (baseStart_6576343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6576343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6576343 prefixEnd_6576343 := by exact prefixLift 6576343
  have htrace : WordTrace (prefixWord ++ tailWord_6576343) baseStart_6576343 baseEnd_6576343 := by
    simpa [prefixWord, tailWord_6576343, baseEnd_6576343] using wordTrace_append hprefix tailTrace_6576343
  have hstable : (prefixWord ++ tailWord_6576343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6576343).length < 2 ^ (prefixWord ++ tailWord_6576343).sum := by decide
  have hdescent : baseEnd_6576343 < baseStart_6576343 := by decide
  rcases family_descends (prefixWord ++ tailWord_6576343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6576344 : List Nat := [2, 1, 2, 2, 4, 2, 2, 3, 1, 2, 2]
def baseStart_6576344 : Nat := 118140960795 + 6576344 * 2 ^ 59
def prefixEnd_6576344 : Nat := 4983230072969 + 3 ^ 40 * 6576344 * 2
def baseEnd_6576344 : Nat := 3376825421311523257555951

theorem tailTrace_6576344 : CollatzResearch.WordTrace tailWord_6576344 prefixEnd_6576344 3376825421311523257555951 := by
  unfold tailWord_6576344
  simp only [CollatzResearch.WordTrace]
  refine ⟨119929485443518156490880043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159905980591357541987840057 119929485443518156490880043)
  ·
    refine ⟨179894228165277234736320065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119929485443518156490880043 179894228165277234736320065)
    ·
      refine ⟨134920671123957926052240049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 179894228165277234736320065 134920671123957926052240049)
      ·
        refine ⟨101190503342968444539180037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 134920671123957926052240049 101190503342968444539180037)
        ·
          refine ⟨18973219376806583351096257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 101190503342968444539180037 18973219376806583351096257)
          ·
            refine ⟨14229914532604937513322193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18973219376806583351096257 14229914532604937513322193)
            ·
              refine ⟨10672435899453703134991645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14229914532604937513322193 10672435899453703134991645)
              ·
                refine ⟨4002163462295138675621867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10672435899453703134991645 4002163462295138675621867)
                ·
                  refine ⟨6003245193442708013432801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4002163462295138675621867 6003245193442708013432801)
                  ·
                    refine ⟨4502433895082031010074601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6003245193442708013432801 4502433895082031010074601)
                    ·
                      refine ⟨3376825421311523257555951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4502433895082031010074601 3376825421311523257555951)
                      ·
                        rfl

theorem cell23_6576344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 2, 3, 1, 2, 2].length) (baseStart_6576344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6576344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6576344 prefixEnd_6576344 := by exact prefixLift 6576344
  have htrace : WordTrace (prefixWord ++ tailWord_6576344) baseStart_6576344 baseEnd_6576344 := by
    simpa [prefixWord, tailWord_6576344, baseEnd_6576344] using wordTrace_append hprefix tailTrace_6576344
  have hstable : (prefixWord ++ tailWord_6576344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6576344).length < 2 ^ (prefixWord ++ tailWord_6576344).sum := by decide
  have hdescent : baseEnd_6576344 < baseStart_6576344 := by decide
  rcases family_descends (prefixWord ++ tailWord_6576344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6576354 : List Nat := [3, 3, 4, 1, 1, 1, 1, 1, 4, 4]
def baseStart_6576354 : Nat := 118140960795 + 6576354 * 2 ^ 59
def prefixEnd_6576354 : Nat := 4983230072969 + 3 ^ 40 * 6576354 * 2
def baseEnd_6576354 : Nat := 1125610185372689406143635

theorem tailTrace_6576354 : CollatzResearch.WordTrace tailWord_6576354 prefixEnd_6576354 1125610185372689406143635 := by
  unfold tailWord_6576354
  simp only [CollatzResearch.WordTrace]
  refine ⟨59964833904250021172406029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 159906223744666723126416077 59964833904250021172406029)
  ·
    refine ⟨22486812714093757939652261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59964833904250021172406029 22486812714093757939652261)
    ·
      refine ⟨4216277383892579613684799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22486812714093757939652261 4216277383892579613684799)
      ·
        refine ⟨6324416075838869420527199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4216277383892579613684799 6324416075838869420527199)
        ·
          refine ⟨9486624113758304130790799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6324416075838869420527199 9486624113758304130790799)
          ·
            refine ⟨14229936170637456196186199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9486624113758304130790799 14229936170637456196186199)
            ·
              refine ⟨21344904255956184294279299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14229936170637456196186199 21344904255956184294279299)
              ·
                refine ⟨32017356383934276441418949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21344904255956184294279299 32017356383934276441418949)
                ·
                  refine ⟨6003254321987676832766053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32017356383934276441418949 6003254321987676832766053)
                  ·
                    refine ⟨1125610185372689406143635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6003254321987676832766053 1125610185372689406143635)
                    ·
                      rfl

theorem cell23_6576354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 1, 1, 4, 4].length) (baseStart_6576354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6576354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6576354 prefixEnd_6576354 := by exact prefixLift 6576354
  have htrace : WordTrace (prefixWord ++ tailWord_6576354) baseStart_6576354 baseEnd_6576354 := by
    simpa [prefixWord, tailWord_6576354, baseEnd_6576354] using wordTrace_append hprefix tailTrace_6576354
  have hstable : (prefixWord ++ tailWord_6576354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6576354).length < 2 ^ (prefixWord ++ tailWord_6576354).sum := by decide
  have hdescent : baseEnd_6576354 < baseStart_6576354 := by decide
  rcases family_descends (prefixWord ++ tailWord_6576354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6576360 : List Nat := [2, 1, 4, 1, 2, 3, 1, 1, 4, 1, 3]
def baseStart_6576360 : Nat := 118140960795 + 6576360 * 2 ^ 59
def prefixEnd_6576360 : Nat := 4983230072969 + 3 ^ 40 * 6576360 * 2
def baseEnd_6576360 : Nat := 3376833637001995194955877

theorem tailTrace_6576360 : CollatzResearch.WordTrace tailWord_6576360 prefixEnd_6576360 3376833637001995194955877 := by
  unfold tailWord_6576360
  simp only [CollatzResearch.WordTrace]
  refine ⟨119929777227489173857171267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159906369636652231809561689 119929777227489173857171267)
  ·
    refine ⟨179894665841233760785756901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119929777227489173857171267 179894665841233760785756901)
    ·
      refine ⟨33730249845231330147329419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 179894665841233760785756901 33730249845231330147329419)
      ·
        refine ⟨50595374767846995220994129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33730249845231330147329419 50595374767846995220994129)
        ·
          refine ⟨37946531075885246415745597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50595374767846995220994129 37946531075885246415745597)
          ·
            refine ⟨14229949153456967405904599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37946531075885246415745597 14229949153456967405904599)
            ·
              refine ⟨21344923730185451108856899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14229949153456967405904599 21344923730185451108856899)
              ·
                refine ⟨32017385595278176663285349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21344923730185451108856899 32017385595278176663285349)
                ·
                  refine ⟨6003259799114658124366003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32017385595278176663285349 6003259799114658124366003)
                  ·
                    refine ⟨9004889698671987186549005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6003259799114658124366003 9004889698671987186549005)
                    ·
                      refine ⟨3376833637001995194955877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9004889698671987186549005 3376833637001995194955877)
                      ·
                        rfl

theorem cell23_6576360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 1, 1, 4, 1, 3].length) (baseStart_6576360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6576360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6576360 prefixEnd_6576360 := by exact prefixLift 6576360
  have htrace : WordTrace (prefixWord ++ tailWord_6576360) baseStart_6576360 baseEnd_6576360 := by
    simpa [prefixWord, tailWord_6576360, baseEnd_6576360] using wordTrace_append hprefix tailTrace_6576360
  have hstable : (prefixWord ++ tailWord_6576360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6576360).length < 2 ^ (prefixWord ++ tailWord_6576360).sum := by decide
  have hdescent : baseEnd_6576360 < baseStart_6576360 := by decide
  rcases family_descends (prefixWord ++ tailWord_6576360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6576434 : List Nat := [3, 2, 1, 1, 5, 1, 1, 3, 2, 2, 2]
def baseStart_6576434 : Nat := 118140960795 + 6576434 * 2 ^ 59
def prefixEnd_6576434 : Nat := 4983230072969 + 3 ^ 40 * 6576434 * 2
def baseEnd_6576434 : Nat := 3376871634570427905430537

theorem tailTrace_6576434 : CollatzResearch.WordTrace tailWord_6576434 prefixEnd_6576434 3376871634570427905430537 := by
  unfold tailWord_6576434
  simp only [CollatzResearch.WordTrace]
  refine ⟨59965563364177564588134089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 159908168971140172235024237 59965563364177564588134089)
  ·
    refine ⟨44974172523133173441100567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59965563364177564588134089 44974172523133173441100567)
    ·
      refine ⟨67461258784699760161650851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44974172523133173441100567 67461258784699760161650851)
      ·
        refine ⟨101191888177049640242476277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67461258784699760161650851 101191888177049640242476277)
        ·
          refine ⟨9486739516598403772732151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 101191888177049640242476277 9486739516598403772732151)
          ·
            refine ⟨14230109274897605659098227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9486739516598403772732151 14230109274897605659098227)
            ·
              refine ⟨21345163912346408488647341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14230109274897605659098227 21345163912346408488647341)
              ·
                refine ⟨8004436467129903183242753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21345163912346408488647341 8004436467129903183242753)
                ·
                  refine ⟨6003327350347427387432065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8004436467129903183242753 6003327350347427387432065)
                  ·
                    refine ⟨4502495512760570540574049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6003327350347427387432065 4502495512760570540574049)
                    ·
                      refine ⟨3376871634570427905430537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4502495512760570540574049 3376871634570427905430537)
                      ·
                        rfl

theorem cell23_6576434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 1, 3, 2, 2, 2].length) (baseStart_6576434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6576434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6576434 prefixEnd_6576434 := by exact prefixLift 6576434
  have htrace : WordTrace (prefixWord ++ tailWord_6576434) baseStart_6576434 baseEnd_6576434 := by
    simpa [prefixWord, tailWord_6576434, baseEnd_6576434] using wordTrace_append hprefix tailTrace_6576434
  have hstable : (prefixWord ++ tailWord_6576434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6576434).length < 2 ^ (prefixWord ++ tailWord_6576434).sum := by decide
  have hdescent : baseEnd_6576434 < baseStart_6576434 := by decide
  rcases family_descends (prefixWord ++ tailWord_6576434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6576600 : List Nat := [2, 1, 2, 2, 2, 1, 1, 4, 3, 2, 3]
def baseStart_6576600 : Nat := 118140960795 + 6576600 * 2 ^ 59
def prefixEnd_6576600 : Nat := 4983230072969 + 3 ^ 40 * 6576600 * 2
def baseEnd_6576600 : Nat := 3376956872359074255954773

theorem tailTrace_6576600 : CollatzResearch.WordTrace tailWord_6576600 prefixEnd_6576600 3376956872359074255954773 := by
  unfold tailWord_6576600
  simp only [CollatzResearch.WordTrace]
  refine ⟨119934153987054434351539627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159912205316072579135386169 119934153987054434351539627)
  ·
    refine ⟨179901230980581651527309441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119934153987054434351539627 179901230980581651527309441)
    ·
      refine ⟨134925923235436238645482081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 179901230980581651527309441 134925923235436238645482081)
      ·
        refine ⟨101194442426577178984111561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 134925923235436238645482081 101194442426577178984111561)
        ·
          refine ⟨75895831819932884238083671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101194442426577178984111561 75895831819932884238083671)
          ·
            refine ⟨113843747729899326357125507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75895831819932884238083671 113843747729899326357125507)
            ·
              refine ⟨170765621594848989535688261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 113843747729899326357125507 170765621594848989535688261)
              ·
                refine ⟨32018554049034185537941549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 170765621594848989535688261 32018554049034185537941549)
                ·
                  refine ⟨12006957768387819576728081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32018554049034185537941549 12006957768387819576728081)
                  ·
                    refine ⟨9005218326290864682546061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12006957768387819576728081 9005218326290864682546061)
                    ·
                      refine ⟨3376956872359074255954773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9005218326290864682546061 3376956872359074255954773)
                      ·
                        rfl

theorem cell23_6576600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 4, 3, 2, 3].length) (baseStart_6576600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6576600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6576600 prefixEnd_6576600 := by exact prefixLift 6576600
  have htrace : WordTrace (prefixWord ++ tailWord_6576600) baseStart_6576600 baseEnd_6576600 := by
    simpa [prefixWord, tailWord_6576600, baseEnd_6576600] using wordTrace_append hprefix tailTrace_6576600
  have hstable : (prefixWord ++ tailWord_6576600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6576600).length < 2 ^ (prefixWord ++ tailWord_6576600).sum := by decide
  have hdescent : baseEnd_6576600 < baseStart_6576600 := by decide
  rcases family_descends (prefixWord ++ tailWord_6576600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6576607 : List Nat := [1, 1, 2, 3, 3, 3, 1, 3, 2, 4]
def baseStart_6576607 : Nat := 118140960795 + 6576607 * 2 ^ 59
def prefixEnd_6576607 : Nat := 4983230072969 + 3 ^ 40 * 6576607 * 2
def baseEnd_6576607 : Nat := 1125653488907885242855747

theorem tailTrace_6576607 : CollatzResearch.WordTrace tailWord_6576607 prefixEnd_6576607 1125653488907885242855747 := by
  unfold tailWord_6576607
  simp only [CollatzResearch.WordTrace]
  refine ⟨239868563285083508898584075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159912375523389005932389383 239868563285083508898584075)
  ·
    refine ⟨359802844927625263347876113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 239868563285083508898584075 359802844927625263347876113)
    ·
      refine ⟨269852133695718947510907085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 359802844927625263347876113 269852133695718947510907085)
      ·
        refine ⟨101194550135894605316590157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 269852133695718947510907085 101194550135894605316590157)
        ·
          refine ⟨37947956300960476993721309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 101194550135894605316590157 37947956300960476993721309)
          ·
            refine ⟨14230483612860178872645491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37947956300960476993721309 14230483612860178872645491)
            ·
              refine ⟨21345725419290268308968237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14230483612860178872645491 21345725419290268308968237)
              ·
                refine ⟨8004647032233850615863089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21345725419290268308968237 8004647032233850615863089)
                ·
                  refine ⟨6003485274175387961897317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8004647032233850615863089 6003485274175387961897317)
                  ·
                    refine ⟨1125653488907885242855747, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6003485274175387961897317 1125653488907885242855747)
                    ·
                      rfl

theorem cell23_6576607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 1, 3, 2, 4].length) (baseStart_6576607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6576607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6576607 prefixEnd_6576607 := by exact prefixLift 6576607
  have htrace : WordTrace (prefixWord ++ tailWord_6576607) baseStart_6576607 baseEnd_6576607 := by
    simpa [prefixWord, tailWord_6576607, baseEnd_6576607] using wordTrace_append hprefix tailTrace_6576607
  have hstable : (prefixWord ++ tailWord_6576607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6576607).length < 2 ^ (prefixWord ++ tailWord_6576607).sum := by decide
  have hdescent : baseEnd_6576607 < baseStart_6576607 := by decide
  rcases family_descends (prefixWord ++ tailWord_6576607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6576642 : List Nat := [3, 4, 1, 2, 3, 1, 2, 2, 1, 1, 3]
def baseStart_6576642 : Nat := 118140960795 + 6576642 * 2 ^ 59
def prefixEnd_6576642 : Nat := 4983230072969 + 3 ^ 40 * 6576642 * 2
def baseEnd_6576642 : Nat := 3376978438546563091629581

theorem tailTrace_6576642 : CollatzResearch.WordTrace tailWord_6576642 prefixEnd_6576642 3376978438546563091629581 := by
  unfold tailWord_6576642
  simp only [CollatzResearch.WordTrace]
  refine ⟨59967459959989177469027045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 159913226559971139917405453 59967459959989177469027045)
  ·
    refine ⟨11243898742497970775442571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 59967459959989177469027045 11243898742497970775442571)
    ·
      refine ⟨16865848113746956163163857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11243898742497970775442571 16865848113746956163163857)
      ·
        refine ⟨12649386085310217122372893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16865848113746956163163857 12649386085310217122372893)
        ·
          refine ⟨4743519781991331420889835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12649386085310217122372893 4743519781991331420889835)
          ·
            refine ⟨7115279672986997131334753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4743519781991331420889835 7115279672986997131334753)
            ·
              refine ⟨5336459754740247848501065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7115279672986997131334753 5336459754740247848501065)
              ·
                refine ⟨4002344816055185886375799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5336459754740247848501065 4002344816055185886375799)
                ·
                  refine ⟨6003517224082778829563699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4002344816055185886375799 6003517224082778829563699)
                  ·
                    refine ⟨9005275836124168244345549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6003517224082778829563699 9005275836124168244345549)
                    ·
                      refine ⟨3376978438546563091629581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9005275836124168244345549 3376978438546563091629581)
                      ·
                        rfl

theorem cell23_6576642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 3, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 3, 1, 2, 2, 1, 1, 3].length) (baseStart_6576642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6576642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6576642 prefixEnd_6576642 := by exact prefixLift 6576642
  have htrace : WordTrace (prefixWord ++ tailWord_6576642) baseStart_6576642 baseEnd_6576642 := by
    simpa [prefixWord, tailWord_6576642, baseEnd_6576642] using wordTrace_append hprefix tailTrace_6576642
  have hstable : (prefixWord ++ tailWord_6576642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6576642).length < 2 ^ (prefixWord ++ tailWord_6576642).sum := by decide
  have hdescent : baseEnd_6576642 < baseStart_6576642 := by decide
  rcases family_descends (prefixWord ++ tailWord_6576642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6576664 : List Nat := [2, 1, 2, 3, 3, 1, 2, 3, 2, 1, 3]
def baseStart_6576664 : Nat := 118140960795 + 6576664 * 2 ^ 59
def prefixEnd_6576664 : Nat := 4983230072969 + 3 ^ 40 * 6576664 * 2
def baseEnd_6576664 : Nat := 3376989735120962005554479

theorem tailTrace_6576664 : CollatzResearch.WordTrace tailWord_6576664 prefixEnd_6576664 3376989735120962005554479 := by
  unfold tailWord_6576664
  simp only [CollatzResearch.WordTrace]
  refine ⟨119935321122938503816704523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159913761497251338422272697 119935321122938503816704523)
  ·
    refine ⟨179902981684407755725056785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119935321122938503816704523 179902981684407755725056785)
    ·
      refine ⟨134927236263305816793792589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 179902981684407755725056785 134927236263305816793792589)
      ·
        refine ⟨50597713598739681297672221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 134927236263305816793792589 50597713598739681297672221)
        ·
          refine ⟨18974142599527380486627083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50597713598739681297672221 18974142599527380486627083)
          ·
            refine ⟨28461213899291070729940625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18974142599527380486627083 28461213899291070729940625)
            ·
              refine ⟨21345910424468303047455469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28461213899291070729940625 21345910424468303047455469)
              ·
                refine ⟨8004716409175613642795801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21345910424468303047455469 8004716409175613642795801)
                ·
                  refine ⟨6003537306881710232096851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8004716409175613642795801 6003537306881710232096851)
                  ·
                    refine ⟨9005305960322565348145277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6003537306881710232096851 9005305960322565348145277)
                    ·
                      refine ⟨3376989735120962005554479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9005305960322565348145277 3376989735120962005554479)
                      ·
                        rfl

theorem cell23_6576664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 2, 3, 2, 1, 3].length) (baseStart_6576664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6576664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6576664 prefixEnd_6576664 := by exact prefixLift 6576664
  have htrace : WordTrace (prefixWord ++ tailWord_6576664) baseStart_6576664 baseEnd_6576664 := by
    simpa [prefixWord, tailWord_6576664, baseEnd_6576664] using wordTrace_append hprefix tailTrace_6576664
  have hstable : (prefixWord ++ tailWord_6576664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6576664).length < 2 ^ (prefixWord ++ tailWord_6576664).sum := by decide
  have hdescent : baseEnd_6576664 < baseStart_6576664 := by decide
  rcases family_descends (prefixWord ++ tailWord_6576664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6576674 : List Nat := [3, 3, 1, 1, 1, 1, 1, 6, 1, 3, 2]
def baseStart_6576674 : Nat := 118140960795 + 6576674 * 2 ^ 59
def prefixEnd_6576674 : Nat := 4983230072969 + 3 ^ 40 * 6576674 * 2
def baseEnd_6576674 : Nat := 3376994869927506966429433

theorem tailTrace_6576674 : CollatzResearch.WordTrace tailWord_6576674 prefixEnd_6576674 3376994869927506966429433 := by
  unfold tailWord_6576674
  simp only [CollatzResearch.WordTrace]
  refine ⟨59967751743960194835318269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 159914004650560519560848717 59967751743960194835318269)
  ·
    refine ⟨22487906903985073063244351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59967751743960194835318269 22487906903985073063244351)
    ·
      refine ⟨33731860355977609594866527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22487906903985073063244351 33731860355977609594866527)
      ·
        refine ⟨50597790533966414392299791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33731860355977609594866527 50597790533966414392299791)
        ·
          refine ⟨75896685800949621588449687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50597790533966414392299791 75896685800949621588449687)
          ·
            refine ⟨113845028701424432382674531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75896685800949621588449687 113845028701424432382674531)
            ·
              refine ⟨170767543052136648574011797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 113845028701424432382674531 170767543052136648574011797)
              ·
                refine ⟨8004728580568905401906803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 170767543052136648574011797 8004728580568905401906803)
                ·
                  refine ⟨12007092870853358102860205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8004728580568905401906803 12007092870853358102860205)
                  ·
                    refine ⟨4502659826570009288572577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12007092870853358102860205 4502659826570009288572577)
                    ·
                      refine ⟨3376994869927506966429433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4502659826570009288572577 3376994869927506966429433)
                      ·
                        rfl

theorem cell23_6576674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 6, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 6, 1, 3, 2].length) (baseStart_6576674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6576674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6576674 prefixEnd_6576674 := by exact prefixLift 6576674
  have htrace : WordTrace (prefixWord ++ tailWord_6576674) baseStart_6576674 baseEnd_6576674 := by
    simpa [prefixWord, tailWord_6576674, baseEnd_6576674] using wordTrace_append hprefix tailTrace_6576674
  have hstable : (prefixWord ++ tailWord_6576674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6576674).length < 2 ^ (prefixWord ++ tailWord_6576674).sum := by decide
  have hdescent : baseEnd_6576674 < baseStart_6576674 := by decide
  rcases family_descends (prefixWord ++ tailWord_6576674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6576690 : List Nat := [3, 2, 1, 1, 2, 1, 2, 3, 2, 1, 5]
def baseStart_6576690 : Nat := 118140960795 + 6576690 * 2 ^ 59
def prefixEnd_6576690 : Nat := 4983230072969 + 3 ^ 40 * 6576690 * 2
def baseEnd_6576690 : Nat := 3377003085617978903829359

theorem tailTrace_6576690 : CollatzResearch.WordTrace tailWord_6576690 prefixEnd_6576690 3377003085617978903829359 := by
  unfold tailWord_6576690
  simp only [CollatzResearch.WordTrace]
  refine ⟨59967897635945703518463881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 159914393695855209382570349 59967897635945703518463881)
  ·
    refine ⟨44975923226959277638847911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59967897635945703518463881 44975923226959277638847911)
    ·
      refine ⟨67463884840438916458271867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44975923226959277638847911 67463884840438916458271867)
      ·
        refine ⟨101195827260658374687407801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67463884840438916458271867 101195827260658374687407801)
        ·
          refine ⟨75896870445493781015555851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101195827260658374687407801 75896870445493781015555851)
          ·
            refine ⟨113845305668240671523333777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75896870445493781015555851 113845305668240671523333777)
            ·
              refine ⟨85383979251180503642500333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 113845305668240671523333777 85383979251180503642500333)
              ·
                refine ⟨32018992219192688865937625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 85383979251180503642500333 32018992219192688865937625)
                ·
                  refine ⟨24014244164394516649453219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32018992219192688865937625 24014244164394516649453219)
                  ·
                    refine ⟨36021366246591774974179829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24014244164394516649453219 36021366246591774974179829)
                    ·
                      refine ⟨3377003085617978903829359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36021366246591774974179829 3377003085617978903829359)
                      ·
                        rfl

theorem cell23_6576690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 3, 2, 1, 5].length) (baseStart_6576690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6576690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6576690 prefixEnd_6576690 := by exact prefixLift 6576690
  have htrace : WordTrace (prefixWord ++ tailWord_6576690) baseStart_6576690 baseEnd_6576690 := by
    simpa [prefixWord, tailWord_6576690, baseEnd_6576690] using wordTrace_append hprefix tailTrace_6576690
  have hstable : (prefixWord ++ tailWord_6576690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6576690).length < 2 ^ (prefixWord ++ tailWord_6576690).sum := by decide
  have hdescent : baseEnd_6576690 < baseStart_6576690 := by decide
  rcases family_descends (prefixWord ++ tailWord_6576690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6576720 : List Nat := [2, 1, 1, 1, 1, 3, 2, 3, 1, 5, 3]
def baseStart_6576720 : Nat := 118140960795 + 6576720 * 2 ^ 59
def prefixEnd_6576720 : Nat := 4983230072969 + 3 ^ 40 * 6576720 * 2
def baseEnd_6576720 : Nat := 3377018490037613786454221

theorem tailTrace_6576720 : CollatzResearch.WordTrace tailWord_6576720 prefixEnd_6576720 3377018490037613786454221 := by
  unfold tailWord_6576720
  simp only [CollatzResearch.WordTrace]
  refine ⟨119936342366837064598723807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159915123155782752798298409 119936342366837064598723807)
  ·
    refine ⟨179904513550255596898085711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119936342366837064598723807 179904513550255596898085711)
    ·
      refine ⟨269856770325383395347128567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179904513550255596898085711 269856770325383395347128567)
      ·
        refine ⟨404785155488075093020692851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 269856770325383395347128567 404785155488075093020692851)
        ·
          refine ⟨607177733232112639531039277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 404785155488075093020692851 607177733232112639531039277)
          ·
            refine ⟨227691649962042239824139729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 607177733232112639531039277 227691649962042239824139729)
            ·
              refine ⟨170768737471531679868104797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 227691649962042239824139729 170768737471531679868104797)
              ·
                refine ⟨64038276551824379950539299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 170768737471531679868104797 64038276551824379950539299)
                ·
                  refine ⟨96057414827736569925808949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 64038276551824379950539299 96057414827736569925808949)
                  ·
                    refine ⟨9005382640100303430544589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 96057414827736569925808949 9005382640100303430544589)
                    ·
                      refine ⟨3377018490037613786454221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9005382640100303430544589 3377018490037613786454221)
                      ·
                        rfl

theorem cell23_6576720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 3, 1, 5, 3].length) (baseStart_6576720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6576720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6576720 prefixEnd_6576720 := by exact prefixLift 6576720
  have htrace : WordTrace (prefixWord ++ tailWord_6576720) baseStart_6576720 baseEnd_6576720 := by
    simpa [prefixWord, tailWord_6576720, baseEnd_6576720] using wordTrace_append hprefix tailTrace_6576720
  have hstable : (prefixWord ++ tailWord_6576720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6576720).length < 2 ^ (prefixWord ++ tailWord_6576720).sum := by decide
  have hdescent : baseEnd_6576720 < baseStart_6576720 := by decide
  rcases family_descends (prefixWord ++ tailWord_6576720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6576740 : List Nat := [2, 3, 1, 1, 2, 2, 1, 3, 1, 7]
def baseStart_6576740 : Nat := 118140960795 + 6576740 * 2 ^ 59
def prefixEnd_6576740 : Nat := 4983230072969 + 3 ^ 40 * 6576740 * 2
def baseEnd_6576740 : Nat := 1125676253216901236068043

theorem tailTrace_6576740 : CollatzResearch.WordTrace tailWord_6576740 prefixEnd_6576740 1125676253216901236068043 := by
  unfold tailWord_6576740
  simp only [CollatzResearch.WordTrace]
  refine ⟨119936707096800836306587837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159915609462401115075450449 119936707096800836306587837)
  ·
    refine ⟨44976265161300313614970439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 119936707096800836306587837 44976265161300313614970439)
    ·
      refine ⟨67464397741950470422455659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44976265161300313614970439 67464397741950470422455659)
      ·
        refine ⟨101196596612925705633683489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67464397741950470422455659 101196596612925705633683489)
        ·
          refine ⟨75897447459694279225262617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101196596612925705633683489 75897447459694279225262617)
          ·
            refine ⟨56923085594770709418946963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75897447459694279225262617 56923085594770709418946963)
            ·
              refine ⟨85384628392156064128420445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56923085594770709418946963 85384628392156064128420445)
              ·
                refine ⟨32019235647058524048157667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 85384628392156064128420445 32019235647058524048157667)
                ·
                  refine ⟨48028853470587786072236501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32019235647058524048157667 48028853470587786072236501)
                  ·
                    refine ⟨1125676253216901236068043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 48028853470587786072236501 1125676253216901236068043)
                    ·
                      rfl

theorem cell23_6576740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 3, 1, 7].length) (baseStart_6576740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6576740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6576740 prefixEnd_6576740 := by exact prefixLift 6576740
  have htrace : WordTrace (prefixWord ++ tailWord_6576740) baseStart_6576740 baseEnd_6576740 := by
    simpa [prefixWord, tailWord_6576740, baseEnd_6576740] using wordTrace_append hprefix tailTrace_6576740
  have hstable : (prefixWord ++ tailWord_6576740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6576740).length < 2 ^ (prefixWord ++ tailWord_6576740).sum := by decide
  have hdescent : baseEnd_6576740 < baseStart_6576740 := by decide
  rcases family_descends (prefixWord ++ tailWord_6576740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6576777 : List Nat := [1, 2, 1, 1, 4, 1, 1, 3, 1, 6, 2]
def baseStart_6576777 : Nat := 118140960795 + 6576777 * 2 ^ 59
def prefixEnd_6576777 : Nat := 4983230072969 + 3 ^ 40 * 6576777 * 2
def baseEnd_6576777 : Nat := 3377047758434920063441459

theorem tailTrace_6576777 : CollatzResearch.WordTrace tailWord_6576777 prefixEnd_6576777 3377047758434920063441459 := by
  unfold tailWord_6576777
  simp only [CollatzResearch.WordTrace]
  refine ⟨239874763694467627932272585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159916509129645085288181723 239874763694467627932272585)
  ·
    refine ⟨179906072770850720949204439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 239874763694467627932272585 179906072770850720949204439)
    ·
      refine ⟨269859109156276081423806659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179906072770850720949204439 269859109156276081423806659)
      ·
        refine ⟨404788663734414122135709989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 269859109156276081423806659 404788663734414122135709989)
        ·
          refine ⟨75897874450202647900445623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 404788663734414122135709989 75897874450202647900445623)
          ·
            refine ⟨113846811675303971850668435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75897874450202647900445623 113846811675303971850668435)
            ·
              refine ⟨170770217512955957776002653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 113846811675303971850668435 170770217512955957776002653)
              ·
                refine ⟨64038831567358484166000995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 170770217512955957776002653 64038831567358484166000995)
                ·
                  refine ⟨96058247351037726249001493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 64038831567358484166000995 96058247351037726249001493)
                  ·
                    refine ⟨4502730344579893417921945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 96058247351037726249001493 4502730344579893417921945)
                    ·
                      refine ⟨3377047758434920063441459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4502730344579893417921945 3377047758434920063441459)
                      ·
                        rfl

theorem cell23_6576777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 3, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 3, 1, 6, 2].length) (baseStart_6576777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6576777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6576777 prefixEnd_6576777 := by exact prefixLift 6576777
  have htrace : WordTrace (prefixWord ++ tailWord_6576777) baseStart_6576777 baseEnd_6576777 := by
    simpa [prefixWord, tailWord_6576777, baseEnd_6576777] using wordTrace_append hprefix tailTrace_6576777
  have hstable : (prefixWord ++ tailWord_6576777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6576777).length < 2 ^ (prefixWord ++ tailWord_6576777).sum := by decide
  have hdescent : baseEnd_6576777 < baseStart_6576777 := by decide
  rcases family_descends (prefixWord ++ tailWord_6576777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6576797 : List Nat := [1, 4, 2, 1, 1, 1, 2, 3, 1, 4, 3]
def baseStart_6576797 : Nat := 118140960795 + 6576797 * 2 ^ 59
def prefixEnd_6576797 : Nat := 4983230072969 + 3 ^ 40 * 6576797 * 2
def baseEnd_6576797 : Nat := 3377058028048009985191367

theorem tailTrace_6576797 : CollatzResearch.WordTrace tailWord_6576797 prefixEnd_6576797 3377058028048009985191367 := by
  unfold tailWord_6576797
  simp only [CollatzResearch.WordTrace]
  refine ⟨239875493154395171348000645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159916995436263447565333763 239875493154395171348000645)
  ·
    refine ⟨44976654966449094627750121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 239875493154395171348000645 44976654966449094627750121)
    ·
      refine ⟨33732491224836820970812591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44976654966449094627750121 33732491224836820970812591)
      ·
        refine ⟨50598736837255231456218887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33732491224836820970812591 50598736837255231456218887)
        ·
          refine ⟨75898105255882847184328331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50598736837255231456218887 75898105255882847184328331)
          ·
            refine ⟨113847157883824270776492497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75898105255882847184328331 113847157883824270776492497)
            ·
              refine ⟨85385368412868203082369373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 113847157883824270776492497 85385368412868203082369373)
              ·
                refine ⟨32019513154825576155888515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 85385368412868203082369373 32019513154825576155888515)
                ·
                  refine ⟨48029269732238364233832773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32019513154825576155888515 48029269732238364233832773)
                  ·
                    refine ⟨9005488074794693293843645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 48029269732238364233832773 9005488074794693293843645)
                    ·
                      refine ⟨3377058028048009985191367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9005488074794693293843645 3377058028048009985191367)
                      ·
                        rfl

theorem cell23_6576797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 3, 1, 4, 3].length) (baseStart_6576797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6576797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6576797 prefixEnd_6576797 := by exact prefixLift 6576797
  have htrace : WordTrace (prefixWord ++ tailWord_6576797) baseStart_6576797 baseEnd_6576797 := by
    simpa [prefixWord, tailWord_6576797, baseEnd_6576797] using wordTrace_append hprefix tailTrace_6576797
  have hstable : (prefixWord ++ tailWord_6576797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6576797).length < 2 ^ (prefixWord ++ tailWord_6576797).sum := by decide
  have hdescent : baseEnd_6576797 < baseStart_6576797 := by decide
  rcases family_descends (prefixWord ++ tailWord_6576797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6576845 : List Nat := [1, 6, 2, 1, 3, 1, 1, 1, 2, 1, 4]
def baseStart_6576845 : Nat := 118140960795 + 6576845 * 2 ^ 59
def prefixEnd_6576845 : Nat := 4983230072969 + 3 ^ 40 * 6576845 * 2
def baseEnd_6576845 : Nat := 3377082675119425797391147

theorem tailTrace_6576845 : CollatzResearch.WordTrace tailWord_6576845 prefixEnd_6576845 3377082675119425797391147 := by
  unfold tailWord_6576845
  simp only [CollatzResearch.WordTrace]
  refine ⟨239877243858221275545747989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159918162572147517030498659 239877243858221275545747989)
  ·
    refine ⟨11244245805854122291206937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 239877243858221275545747989 11244245805854122291206937)
    ·
      refine ⟨8433184354390591718405203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11244245805854122291206937 8433184354390591718405203)
      ·
        refine ⟨12649776531585887577607805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8433184354390591718405203 12649776531585887577607805)
        ·
          refine ⟨4743666199344707841602927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12649776531585887577607805 4743666199344707841602927)
          ·
            refine ⟨7115499299017061762404391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4743666199344707841602927 7115499299017061762404391)
            ·
              refine ⟨10673248948525592643606587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7115499299017061762404391 10673248948525592643606587)
              ·
                refine ⟨16009873422788388965409881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10673248948525592643606587 16009873422788388965409881)
                ·
                  refine ⟨12007405067091291724057411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16009873422788388965409881 12007405067091291724057411)
                  ·
                    refine ⟨18011107600636937586086117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12007405067091291724057411 18011107600636937586086117)
                    ·
                      refine ⟨3377082675119425797391147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18011107600636937586086117 3377082675119425797391147)
                      ·
                        rfl

theorem cell23_6576845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 3, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 3, 1, 1, 1, 2, 1, 4].length) (baseStart_6576845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6576845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6576845 prefixEnd_6576845 := by exact prefixLift 6576845
  have htrace : WordTrace (prefixWord ++ tailWord_6576845) baseStart_6576845 baseEnd_6576845 := by
    simpa [prefixWord, tailWord_6576845, baseEnd_6576845] using wordTrace_append hprefix tailTrace_6576845
  have hstable : (prefixWord ++ tailWord_6576845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6576845).length < 2 ^ (prefixWord ++ tailWord_6576845).sum := by decide
  have hdescent : baseEnd_6576845 < baseStart_6576845 := by decide
  rcases family_descends (prefixWord ++ tailWord_6576845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6576878 : List Nat := [4, 1, 2, 1, 1, 3, 2, 4, 1, 1, 3]
def baseStart_6576878 : Nat := 118140960795 + 6576878 * 2 ^ 59
def prefixEnd_6576878 : Nat := 4983230072969 + 3 ^ 40 * 6576878 * 2
def baseEnd_6576878 : Nat := 3377099619981024168278495

theorem tailTrace_6576878 : CollatzResearch.WordTrace tailWord_6576878 prefixEnd_6576878 3377099619981024168278495 := by
  unfold tailWord_6576878
  simp only [CollatzResearch.WordTrace]
  refine ⟨29984805933387715272712411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 159918964978067814787799525 29984805933387715272712411)
  ·
    refine ⟨44977208900081572909068617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29984805933387715272712411 44977208900081572909068617)
    ·
      refine ⟨33732906675061179681801463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44977208900081572909068617 33732906675061179681801463)
      ·
        refine ⟨50599360012591769522702195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33732906675061179681801463 50599360012591769522702195)
        ·
          refine ⟨75899040018887654284053293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50599360012591769522702195 75899040018887654284053293)
          ·
            refine ⟨28462140007082870356519985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 75899040018887654284053293 28462140007082870356519985)
            ·
              refine ⟨21346605005312152767389989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28462140007082870356519985 21346605005312152767389989)
              ·
                refine ⟨4002488438496028643885623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21346605005312152767389989 4002488438496028643885623)
                ·
                  refine ⟨6003732657744042965828435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4002488438496028643885623 6003732657744042965828435)
                  ·
                    refine ⟨9005598986616064448742653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6003732657744042965828435 9005598986616064448742653)
                    ·
                      refine ⟨3377099619981024168278495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9005598986616064448742653 3377099619981024168278495)
                      ·
                        rfl

theorem cell23_6576878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 2, 4, 1, 1, 3].length) (baseStart_6576878 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6576878 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6576878 prefixEnd_6576878 := by exact prefixLift 6576878
  have htrace : WordTrace (prefixWord ++ tailWord_6576878) baseStart_6576878 baseEnd_6576878 := by
    simpa [prefixWord, tailWord_6576878, baseEnd_6576878] using wordTrace_append hprefix tailTrace_6576878
  have hstable : (prefixWord ++ tailWord_6576878).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6576878).length < 2 ^ (prefixWord ++ tailWord_6576878).sum := by decide
  have hdescent : baseEnd_6576878 < baseStart_6576878 := by decide
  rcases family_descends (prefixWord ++ tailWord_6576878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6576885 : List Nat := [1, 3, 6, 1, 1, 1, 3, 1, 6]
def baseStart_6576885 : Nat := 118140960795 + 6576885 * 2 ^ 59
def prefixEnd_6576885 : Nat := 4983230072969 + 3 ^ 40 * 6576885 * 2
def baseEnd_6576885 : Nat := 375233690482845071210107

theorem tailTrace_6576885 : CollatzResearch.WordTrace tailWord_6576885 prefixEnd_6576885 375233690482845071210107 := by
  unfold tailWord_6576885
  simp only [CollatzResearch.WordTrace]
  refine ⟨239878702778076362377204109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159919135185384241584802739 239878702778076362377204109)
  ·
    refine ⟨89954513541778635891451541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 239878702778076362377204109 89954513541778635891451541)
    ·
      refine ⟨4216617822270873557411791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 89954513541778635891451541 4216617822270873557411791)
      ·
        refine ⟨6324926733406310336117687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4216617822270873557411791 6324926733406310336117687)
        ·
          refine ⟨9487390100109465504176531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6324926733406310336117687 9487390100109465504176531)
          ·
            refine ⟨14231085150164198256264797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9487390100109465504176531 14231085150164198256264797)
            ·
              refine ⟨5336656931311574346099299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14231085150164198256264797 5336656931311574346099299)
              ·
                refine ⟨8004985396967361519148949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5336656931311574346099299 8004985396967361519148949)
                ·
                  refine ⟨375233690482845071210107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8004985396967361519148949 375233690482845071210107)
                  ·
                    rfl

theorem cell23_6576885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 3, 1, 6].length) (baseStart_6576885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6576885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6576885 prefixEnd_6576885 := by exact prefixLift 6576885
  have htrace : WordTrace (prefixWord ++ tailWord_6576885) baseStart_6576885 baseEnd_6576885 := by
    simpa [prefixWord, tailWord_6576885, baseEnd_6576885] using wordTrace_append hprefix tailTrace_6576885
  have hstable : (prefixWord ++ tailWord_6576885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6576885).length < 2 ^ (prefixWord ++ tailWord_6576885).sum := by decide
  have hdescent : baseEnd_6576885 < baseStart_6576885 := by decide
  rcases family_descends (prefixWord ++ tailWord_6576885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6576951 : List Nat := [1, 1, 3, 1, 2, 1, 5, 3, 2, 1, 3]
def baseStart_6576951 : Nat := 118140960795 + 6576951 * 2 ^ 59
def prefixEnd_6576951 : Nat := 4983230072969 + 3 ^ 40 * 6576951 * 2
def baseEnd_6576951 : Nat := 3377137104068802382665659

theorem tailTrace_6576951 : CollatzResearch.WordTrace tailWord_6576951 prefixEnd_6576951 3377137104068802382665659 := by
  unfold tailWord_6576951
  simp only [CollatzResearch.WordTrace]
  refine ⟨239881109995837255649106707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159920739997224837099404471 239881109995837255649106707)
  ·
    refine ⟨359821664993755883473660061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 239881109995837255649106707 359821664993755883473660061)
    ·
      refine ⟨134933124372658456302622523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 359821664993755883473660061 134933124372658456302622523)
      ·
        refine ⟨202399686558987684453933785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134933124372658456302622523 202399686558987684453933785)
        ·
          refine ⟨151799764919240763340450339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 202399686558987684453933785 151799764919240763340450339)
          ·
            refine ⟨227699647378861145010675509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 151799764919240763340450339 227699647378861145010675509)
            ·
              refine ⟨21346841941768232344750829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 227699647378861145010675509 21346841941768232344750829)
              ·
                refine ⟨8005065728163087129281561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21346841941768232344750829 8005065728163087129281561)
                ·
                  refine ⟨6003799296122315346961171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8005065728163087129281561 6003799296122315346961171)
                  ·
                    refine ⟨9005698944183473020441757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6003799296122315346961171 9005698944183473020441757)
                    ·
                      refine ⟨3377137104068802382665659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9005698944183473020441757 3377137104068802382665659)
                      ·
                        rfl

theorem cell23_6576951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 5, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 5, 3, 2, 1, 3].length) (baseStart_6576951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6576951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6576951 prefixEnd_6576951 := by exact prefixLift 6576951
  have htrace : WordTrace (prefixWord ++ tailWord_6576951) baseStart_6576951 baseEnd_6576951 := by
    simpa [prefixWord, tailWord_6576951, baseEnd_6576951] using wordTrace_append hprefix tailTrace_6576951
  have hstable : (prefixWord ++ tailWord_6576951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6576951).length < 2 ^ (prefixWord ++ tailWord_6576951).sum := by decide
  have hdescent : baseEnd_6576951 < baseStart_6576951 := by decide
  rcases family_descends (prefixWord ++ tailWord_6576951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6576967 : List Nat := [1, 1, 4, 1, 2, 1, 1, 2, 4, 6]
def baseStart_6576967 : Nat := 118140960795 + 6576967 * 2 ^ 59
def prefixEnd_6576967 : Nat := 4983230072969 + 3 ^ 40 * 6576967 * 2
def baseEnd_6576967 : Nat := 1125715106586424773355195

theorem tailTrace_6576967 : CollatzResearch.WordTrace tailWord_6576967 prefixEnd_6576967 1125715106586424773355195 := by
  unfold tailWord_6576967
  simp only [CollatzResearch.WordTrace]
  refine ⟨239881693563779290381689155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159921129042519526921126103 239881693563779290381689155)
  ·
    refine ⟨359822540345668935572533733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 239881693563779290381689155 359822540345668935572533733)
    ·
      refine ⟨67466726314812925419850075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 359822540345668935572533733 67466726314812925419850075)
      ·
        refine ⟨101200089472219388129775113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67466726314812925419850075 101200089472219388129775113)
        ·
          refine ⟨75900067104164541097331335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101200089472219388129775113 75900067104164541097331335)
          ·
            refine ⟨113850100656246811645997003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75900067104164541097331335 113850100656246811645997003)
            ·
              refine ⟨170775150984370217468995505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 113850100656246811645997003 170775150984370217468995505)
              ·
                refine ⟨128081363238277663101746629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 170775150984370217468995505 128081363238277663101746629)
                ·
                  refine ⟨24015255607177061831577493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 128081363238277663101746629 24015255607177061831577493)
                  ·
                    refine ⟨1125715106586424773355195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24015255607177061831577493 1125715106586424773355195)
                    ·
                      rfl

theorem cell23_6576967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 2, 4, 6].length) (baseStart_6576967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6576967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6576967 prefixEnd_6576967 := by exact prefixLift 6576967
  have htrace : WordTrace (prefixWord ++ tailWord_6576967) baseStart_6576967 baseEnd_6576967 := by
    simpa [prefixWord, tailWord_6576967, baseEnd_6576967] using wordTrace_append hprefix tailTrace_6576967
  have hstable : (prefixWord ++ tailWord_6576967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6576967).length < 2 ^ (prefixWord ++ tailWord_6576967).sum := by decide
  have hdescent : baseEnd_6576967 < baseStart_6576967 := by decide
  rcases family_descends (prefixWord ++ tailWord_6576967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6577004 : List Nat := [2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 4]
def baseStart_6577004 : Nat := 118140960795 + 6577004 * 2 ^ 59
def prefixEnd_6577004 : Nat := 4983230072969 + 3 ^ 40 * 6577004 * 2
def baseEnd_6577004 : Nat := 3377164318543490675302915

theorem tailTrace_6577004 : CollatzResearch.WordTrace tailWord_6577004 prefixEnd_6577004 3377164318543490675302915 := by
  unfold tailWord_6577004
  simp only [CollatzResearch.WordTrace]
  refine ⟨119941521532322622850393033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159922028709763497133857377 119941521532322622850393033)
  ·
    refine ⟨89956141149241967137794775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119941521532322622850393033 89956141149241967137794775)
    ·
      refine ⟨134934211723862950706692163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89956141149241967137794775 134934211723862950706692163)
      ·
        refine ⟨202401317585794426060038245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134934211723862950706692163 202401317585794426060038245)
        ·
          refine ⟨37950247047336454886257171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 202401317585794426060038245 37950247047336454886257171)
          ·
            refine ⟨56925370571004682329385757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37950247047336454886257171 56925370571004682329385757)
            ·
              refine ⟨21347013964126755873519659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56925370571004682329385757 21347013964126755873519659)
              ·
                refine ⟨32020520946190133810279489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21347013964126755873519659 32020520946190133810279489)
                ·
                  refine ⟨24015390709642600357709617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32020520946190133810279489 24015390709642600357709617)
                  ·
                    refine ⟨18011543032231950268282213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24015390709642600357709617 18011543032231950268282213)
                    ·
                      refine ⟨3377164318543490675302915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18011543032231950268282213 3377164318543490675302915)
                      ·
                        rfl

theorem cell23_6577004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 4].length) (baseStart_6577004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6577004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6577004 prefixEnd_6577004 := by exact prefixLift 6577004
  have htrace : WordTrace (prefixWord ++ tailWord_6577004) baseStart_6577004 baseEnd_6577004 := by
    simpa [prefixWord, tailWord_6577004, baseEnd_6577004] using wordTrace_append hprefix tailTrace_6577004
  have hstable : (prefixWord ++ tailWord_6577004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6577004).length < 2 ^ (prefixWord ++ tailWord_6577004).sum := by decide
  have hdescent : baseEnd_6577004 < baseStart_6577004 := by decide
  rcases family_descends (prefixWord ++ tailWord_6577004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6577008 : List Nat := [2, 1, 1, 1, 4, 1, 4, 3, 2, 2, 2]
def baseStart_6577008 : Nat := 118140960795 + 6577008 * 2 ^ 59
def prefixEnd_6577008 : Nat := 4983230072969 + 3 ^ 40 * 6577008 * 2
def baseEnd_6577008 : Nat := 3377166372466108659652897

theorem tailTrace_6577008 : CollatzResearch.WordTrace tailWord_6577008 prefixEnd_6577008 3377166372466108659652897 := by
  unfold tailWord_6577008
  simp only [CollatzResearch.WordTrace]
  refine ⟨119941594478315377191965839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159922125971087169589287785 119941594478315377191965839)
  ·
    refine ⟨179912391717473065787948759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119941594478315377191965839 179912391717473065787948759)
    ·
      refine ⟨269868587576209598681923139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179912391717473065787948759 269868587576209598681923139)
      ·
        refine ⟨404802881364314398022884709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 269868587576209598681923139 404802881364314398022884709)
        ·
          refine ⟨75900540255808949629290883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 404802881364314398022884709 75900540255808949629290883)
          ·
            refine ⟨113850810383713424443936325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75900540255808949629290883 113850810383713424443936325)
            ·
              refine ⟨21347026946946267083238061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 113850810383713424443936325 21347026946946267083238061)
              ·
                refine ⟨8005135105104850156214273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21347026946946267083238061 8005135105104850156214273)
                ·
                  refine ⟨6003851328828637617160705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8005135105104850156214273 6003851328828637617160705)
                  ·
                    refine ⟨4502888496621478212870529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6003851328828637617160705 4502888496621478212870529)
                    ·
                      refine ⟨3377166372466108659652897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4502888496621478212870529 3377166372466108659652897)
                      ·
                        rfl

theorem cell23_6577008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 4, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 4, 3, 2, 2, 2].length) (baseStart_6577008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6577008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6577008 prefixEnd_6577008 := by exact prefixLift 6577008
  have htrace : WordTrace (prefixWord ++ tailWord_6577008) baseStart_6577008 baseEnd_6577008 := by
    simpa [prefixWord, tailWord_6577008, baseEnd_6577008] using wordTrace_append hprefix tailTrace_6577008
  have hstable : (prefixWord ++ tailWord_6577008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6577008).length < 2 ^ (prefixWord ++ tailWord_6577008).sum := by decide
  have hdescent : baseEnd_6577008 < baseStart_6577008 := by decide
  rcases family_descends (prefixWord ++ tailWord_6577008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6577031 : List Nat := [1, 1, 4, 2, 3, 1, 1, 5, 5]
def baseStart_6577031 : Nat := 118140960795 + 6577031 * 2 ^ 59
def prefixEnd_6577031 : Nat := 4983230072969 + 3 ^ 40 * 6577031 * 2
def baseEnd_6577031 : Nat := 375242020280129118851699

theorem tailTrace_6577031 : CollatzResearch.WordTrace tailWord_6577031 prefixEnd_6577031 375242020280129118851699 := by
  unfold tailWord_6577031
  simp only [CollatzResearch.WordTrace]
  refine ⟨239884027835547429312018947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159922685223698286208012631 239884027835547429312018947)
  ·
    refine ⟨359826041753321143968028421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 239884027835547429312018947 359826041753321143968028421)
    ·
      refine ⟨67467382828747714494005329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 359826041753321143968028421 67467382828747714494005329)
      ·
        refine ⟨50600537121560785870503997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67467382828747714494005329 50600537121560785870503997)
        ·
          refine ⟨18975201420585294701438999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50600537121560785870503997 18975201420585294701438999)
          ·
            refine ⟨28462802130877942052158499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18975201420585294701438999 28462802130877942052158499)
            ·
              refine ⟨42694203196316913078237749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28462802130877942052158499 42694203196316913078237749)
              ·
                refine ⟨4002581549654710601084789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 42694203196316913078237749 4002581549654710601084789)
                ·
                  refine ⟨375242020280129118851699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4002581549654710601084789 375242020280129118851699)
                  ·
                    rfl

theorem cell23_6577031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 1, 5, 5].length) (baseStart_6577031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6577031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6577031 prefixEnd_6577031 := by exact prefixLift 6577031
  have htrace : WordTrace (prefixWord ++ tailWord_6577031) baseStart_6577031 baseEnd_6577031 := by
    simpa [prefixWord, tailWord_6577031, baseEnd_6577031] using wordTrace_append hprefix tailTrace_6577031
  have hstable : (prefixWord ++ tailWord_6577031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6577031).length < 2 ^ (prefixWord ++ tailWord_6577031).sum := by decide
  have hdescent : baseEnd_6577031 < baseStart_6577031 := by decide
  rcases family_descends (prefixWord ++ tailWord_6577031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6577104 : List Nat := [2, 1, 1, 1, 1, 2, 3, 6, 6]
def baseStart_6577104 : Nat := 118140960795 + 6577104 * 2 ^ 59
def prefixEnd_6577104 : Nat := 4983230072969 + 3 ^ 40 * 6577104 * 2
def baseEnd_6577104 : Nat := 375246185178771142672495

theorem tailTrace_6577104 : CollatzResearch.WordTrace tailWord_6577104 prefixEnd_6577104 375246185178771142672495 := by
  unfold tailWord_6577104
  simp only [CollatzResearch.WordTrace]
  refine ⟨119943345182141481389713183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159924460242855308519617577 119943345182141481389713183)
  ·
    refine ⟨179915017773212222084569775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119943345182141481389713183 179915017773212222084569775)
    ·
      refine ⟨269872526659818333126854663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179915017773212222084569775 269872526659818333126854663)
      ·
        refine ⟨404808789989727499690281995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 269872526659818333126854663 404808789989727499690281995)
        ·
          refine ⟨607213184984591249535422993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 404808789989727499690281995 607213184984591249535422993)
          ·
            refine ⟨455409888738443437151567245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 607213184984591249535422993 455409888738443437151567245)
            ·
              refine ⟨170778708276916288931837717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 455409888738443437151567245 170778708276916288931837717)
              ·
                refine ⟨8005251950480451043679893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 170778708276916288931837717 8005251950480451043679893)
                ·
                  refine ⟨375246185178771142672495, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8005251950480451043679893 375246185178771142672495)
                  ·
                    rfl

theorem cell23_6577104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 6, 6].length) (baseStart_6577104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6577104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6577104 prefixEnd_6577104 := by exact prefixLift 6577104
  have htrace : WordTrace (prefixWord ++ tailWord_6577104) baseStart_6577104 baseEnd_6577104 := by
    simpa [prefixWord, tailWord_6577104, baseEnd_6577104] using wordTrace_append hprefix tailTrace_6577104
  have hstable : (prefixWord ++ tailWord_6577104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6577104).length < 2 ^ (prefixWord ++ tailWord_6577104).sum := by decide
  have hdescent : baseEnd_6577104 < baseStart_6577104 := by decide
  rcases family_descends (prefixWord ++ tailWord_6577104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6577108 : List Nat := [2, 4, 1, 2, 1, 2, 3, 1, 3, 4]
def baseStart_6577108 : Nat := 118140960795 + 6577108 * 2 ^ 59
def prefixEnd_6577108 : Nat := 4983230072969 + 3 ^ 40 * 6577108 * 2
def baseEnd_6577108 : Nat := 1125739240177186089467479

theorem tailTrace_6577108 : CollatzResearch.WordTrace tailWord_6577108 prefixEnd_6577108 1125739240177186089467479 := by
  unfold tailWord_6577108
  simp only [CollatzResearch.WordTrace]
  refine ⟨119943418128134235731285989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159924557504178980975047985 119943418128134235731285989)
  ·
    refine ⟨22489390899025169199616123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 119943418128134235731285989 22489390899025169199616123)
    ·
      refine ⟨33734086348537753799424185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22489390899025169199616123 33734086348537753799424185)
      ·
        refine ⟨25300564761403315349568139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33734086348537753799424185 25300564761403315349568139)
        ·
          refine ⟨37950847142104973024352209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25300564761403315349568139 37950847142104973024352209)
          ·
            refine ⟨28463135356578729768264157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37950847142104973024352209 28463135356578729768264157)
            ·
              refine ⟨10673675758717023663099059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28463135356578729768264157 10673675758717023663099059)
              ·
                refine ⟨16010513638075535494648589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10673675758717023663099059 16010513638075535494648589)
                ·
                  refine ⟨6003942614278325810493221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16010513638075535494648589 6003942614278325810493221)
                  ·
                    refine ⟨1125739240177186089467479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6003942614278325810493221 1125739240177186089467479)
                    ·
                      rfl

theorem cell23_6577108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 3, 1, 3, 4].length) (baseStart_6577108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6577108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6577108 prefixEnd_6577108 := by exact prefixLift 6577108
  have htrace : WordTrace (prefixWord ++ tailWord_6577108) baseStart_6577108 baseEnd_6577108 := by
    simpa [prefixWord, tailWord_6577108, baseEnd_6577108] using wordTrace_append hprefix tailTrace_6577108
  have hstable : (prefixWord ++ tailWord_6577108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6577108).length < 2 ^ (prefixWord ++ tailWord_6577108).sum := by decide
  have hdescent : baseEnd_6577108 < baseStart_6577108 := by decide
  rcases family_descends (prefixWord ++ tailWord_6577108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6577171 : List Nat := [1, 1, 1, 2, 1, 4, 1, 2, 2, 6, 2]
def baseStart_6577171 : Nat := 118140960795 + 6577171 * 2 ^ 59
def prefixEnd_6577171 : Nat := 4983230072969 + 3 ^ 40 * 6577171 * 2
def baseEnd_6577171 : Nat := 3377250069812791521914647

theorem tailTrace_6577171 : CollatzResearch.WordTrace tailWord_6577171 prefixEnd_6577171 3377250069812791521914647 := by
  unfold tailWord_6577171
  simp only [CollatzResearch.WordTrace]
  refine ⟨239889134055040233222115367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159926089370026822148076911 239889134055040233222115367)
  ·
    refine ⟨359833701082560349833173051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 239889134055040233222115367 359833701082560349833173051)
    ·
      refine ⟨539750551623840524749759577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 359833701082560349833173051 539750551623840524749759577)
      ·
        refine ⟨404812913717880393562319683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 539750551623840524749759577 404812913717880393562319683)
        ·
          refine ⟨607219370576820590343479525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 404812913717880393562319683 607219370576820590343479525)
          ·
            refine ⟨113853631983153860689402411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 607219370576820590343479525 113853631983153860689402411)
            ·
              refine ⟨170780447974730791034103617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 113853631983153860689402411 170780447974730791034103617)
              ·
                refine ⟨128085335981048093275577713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 170780447974730791034103617 128085335981048093275577713)
                ·
                  refine ⟨96064001985786069956683285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 128085335981048093275577713 96064001985786069956683285)
                  ·
                    refine ⟨4503000093083722029219529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 96064001985786069956683285 4503000093083722029219529)
                    ·
                      refine ⟨3377250069812791521914647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4503000093083722029219529 3377250069812791521914647)
                      ·
                        rfl

theorem cell23_6577171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 2, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 2, 2, 6, 2].length) (baseStart_6577171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6577171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6577171 prefixEnd_6577171 := by exact prefixLift 6577171
  have htrace : WordTrace (prefixWord ++ tailWord_6577171) baseStart_6577171 baseEnd_6577171 := by
    simpa [prefixWord, tailWord_6577171, baseEnd_6577171] using wordTrace_append hprefix tailTrace_6577171
  have hstable : (prefixWord ++ tailWord_6577171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6577171).length < 2 ^ (prefixWord ++ tailWord_6577171).sum := by decide
  have hdescent : baseEnd_6577171 < baseStart_6577171 := by decide
  rcases family_descends (prefixWord ++ tailWord_6577171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6577188 : List Nat := [2, 3, 1, 4, 1, 1, 2, 1, 3, 1, 4]
def baseStart_6577188 : Nat := 118140960795 + 6577188 * 2 ^ 59
def prefixEnd_6577188 : Nat := 4983230072969 + 3 ^ 40 * 6577188 * 2
def baseEnd_6577188 : Nat := 3377258798983917955402069

theorem tailTrace_6577188 : CollatzResearch.WordTrace tailWord_6577188 prefixEnd_6577188 3377258798983917955402069 := by
  unfold tailWord_6577188
  simp only [CollatzResearch.WordTrace]
  refine ⟨119944877047989322562742109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159926502730652430083656145 119944877047989322562742109)
  ·
    refine ⟨44979328892995995961028291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 119944877047989322562742109 44979328892995995961028291)
    ·
      refine ⟨67468993339493993941542437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44979328892995995961028291 67468993339493993941542437)
      ·
        refine ⟨12650436251155123864039207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 67468993339493993941542437 12650436251155123864039207)
        ·
          refine ⟨18975654376732685796058811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12650436251155123864039207 18975654376732685796058811)
          ·
            refine ⟨28463481565099028694088217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18975654376732685796058811 28463481565099028694088217)
            ·
              refine ⟨21347611173824271520566163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28463481565099028694088217 21347611173824271520566163)
              ·
                refine ⟨32021416760736407280849245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21347611173824271520566163 32021416760736407280849245)
                ·
                  refine ⟨12008031285276152730318467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32021416760736407280849245 12008031285276152730318467)
                  ·
                    refine ⟨18012046927914229095477701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12008031285276152730318467 18012046927914229095477701)
                    ·
                      refine ⟨3377258798983917955402069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18012046927914229095477701 3377258798983917955402069)
                      ·
                        rfl

theorem cell23_6577188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 2, 1, 3, 1, 4].length) (baseStart_6577188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6577188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6577188 prefixEnd_6577188 := by exact prefixLift 6577188
  have htrace : WordTrace (prefixWord ++ tailWord_6577188) baseStart_6577188 baseEnd_6577188 := by
    simpa [prefixWord, tailWord_6577188, baseEnd_6577188] using wordTrace_append hprefix tailTrace_6577188
  have hstable : (prefixWord ++ tailWord_6577188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6577188).length < 2 ^ (prefixWord ++ tailWord_6577188).sum := by decide
  have hdescent : baseEnd_6577188 < baseStart_6577188 := by decide
  rcases family_descends (prefixWord ++ tailWord_6577188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6577198 : List Nat := [4, 1, 3, 1, 1, 1, 2, 2, 4, 4]
def baseStart_6577198 : Nat := 118140960795 + 6577198 * 2 ^ 59
def prefixEnd_6577198 : Nat := 4983230072969 + 3 ^ 40 * 6577198 * 2
def baseEnd_6577198 : Nat := 1125754644596820972092341

theorem tailTrace_6577198 : CollatzResearch.WordTrace tailWord_6577198 prefixEnd_6577198 1125754644596820972092341 := by
  unfold tailWord_6577198
  simp only [CollatzResearch.WordTrace]
  refine ⟨29986264853242802104168531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 159926745883961611222232165 29986264853242802104168531)
  ·
    refine ⟨44979397279864203156252797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29986264853242802104168531 44979397279864203156252797)
    ·
      refine ⟨16867273979949076183594799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44979397279864203156252797 16867273979949076183594799)
      ·
        refine ⟨25300910969923614275392199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16867273979949076183594799 25300910969923614275392199)
        ·
          refine ⟨37951366454885421413088299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25300910969923614275392199 37951366454885421413088299)
          ·
            refine ⟨56927049682328132119632449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37951366454885421413088299 56927049682328132119632449)
            ·
              refine ⟨42695287261746099089724337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56927049682328132119632449 42695287261746099089724337)
              ·
                refine ⟨32021465446309574317293253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42695287261746099089724337 32021465446309574317293253)
                ·
                  refine ⟨6004024771183045184492485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32021465446309574317293253 6004024771183045184492485)
                  ·
                    refine ⟨1125754644596820972092341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6004024771183045184492485 1125754644596820972092341)
                    ·
                      rfl

theorem cell23_6577198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 2, 2, 4, 4].length) (baseStart_6577198 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6577198 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6577198 prefixEnd_6577198 := by exact prefixLift 6577198
  have htrace : WordTrace (prefixWord ++ tailWord_6577198) baseStart_6577198 baseEnd_6577198 := by
    simpa [prefixWord, tailWord_6577198, baseEnd_6577198] using wordTrace_append hprefix tailTrace_6577198
  have hstable : (prefixWord ++ tailWord_6577198).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6577198).length < 2 ^ (prefixWord ++ tailWord_6577198).sum := by decide
  have hdescent : baseEnd_6577198 < baseStart_6577198 := by decide
  rcases family_descends (prefixWord ++ tailWord_6577198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6577201 : List Nat := [1, 2, 2, 3, 1, 2, 1, 4, 1, 2, 4]
def baseStart_6577201 : Nat := 118140960795 + 6577201 * 2 ^ 59
def prefixEnd_6577201 : Nat := 4983230072969 + 3 ^ 40 * 6577201 * 2
def baseEnd_6577201 : Nat := 3377265474232426404539509

theorem tailTrace_6577201 : CollatzResearch.WordTrace tailWord_6577201 prefixEnd_6577201 3377265474232426404539509 := by
  unfold tailWord_6577201
  simp only [CollatzResearch.WordTrace]
  refine ⟨239890228244931548345707457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159926818829954365563804971 239890228244931548345707457)
  ·
    refine ⟨179917671183698661259280593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 239890228244931548345707457 179917671183698661259280593)
    ·
      refine ⟨134938253387773995944460445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 179917671183698661259280593 134938253387773995944460445)
      ·
        refine ⟨50601845020415248479172667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 134938253387773995944460445 50601845020415248479172667)
        ·
          refine ⟨75902767530622872718759001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50601845020415248479172667 75902767530622872718759001)
          ·
            refine ⟨56927075647967154539069251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75902767530622872718759001 56927075647967154539069251)
            ·
              refine ⟨85390613471950731808603877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56927075647967154539069251 85390613471950731808603877)
              ·
                refine ⟨16010740025990762214113227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 85390613471950731808603877 16010740025990762214113227)
                ·
                  refine ⟨24016110038986143321169841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16010740025990762214113227 24016110038986143321169841)
                  ·
                    refine ⟨18012082529239607490877381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24016110038986143321169841 18012082529239607490877381)
                    ·
                      refine ⟨3377265474232426404539509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18012082529239607490877381 3377265474232426404539509)
                      ·
                        rfl

theorem cell23_6577201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 4, 1, 2, 4].length) (baseStart_6577201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6577201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6577201 prefixEnd_6577201 := by exact prefixLift 6577201
  have htrace : WordTrace (prefixWord ++ tailWord_6577201) baseStart_6577201 baseEnd_6577201 := by
    simpa [prefixWord, tailWord_6577201, baseEnd_6577201] using wordTrace_append hprefix tailTrace_6577201
  have hstable : (prefixWord ++ tailWord_6577201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6577201).length < 2 ^ (prefixWord ++ tailWord_6577201).sum := by decide
  have hdescent : baseEnd_6577201 < baseStart_6577201 := by decide
  rcases family_descends (prefixWord ++ tailWord_6577201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6577221 : List Nat := [1, 3, 1, 1, 1, 3, 2, 2, 3, 3, 3]
def baseStart_6577221 : Nat := 118140960795 + 6577221 * 2 ^ 59
def prefixEnd_6577221 : Nat := 4983230072969 + 3 ^ 40 * 6577221 * 2
def baseEnd_6577221 : Nat := 3377275743845516326289417

theorem tailTrace_6577221 : CollatzResearch.WordTrace tailWord_6577221 prefixEnd_6577221 3377275743845516326289417 := by
  unfold tailWord_6577221
  simp only [CollatzResearch.WordTrace]
  refine ⟨239890957704859091761435517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159927305136572727840957011 239890957704859091761435517)
  ·
    refine ⟨89959109139322159410538319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 239890957704859091761435517 89959109139322159410538319)
    ·
      refine ⟨134938663708983239115807479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89959109139322159410538319 134938663708983239115807479)
      ·
        refine ⟨202407995563474858673711219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134938663708983239115807479 202407995563474858673711219)
        ·
          refine ⟨303611993345212288010566829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 202407995563474858673711219 303611993345212288010566829)
          ·
            refine ⟨113854497504454608003962561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 303611993345212288010566829 113854497504454608003962561)
            ·
              refine ⟨85390873128340956002971921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 113854497504454608003962561 85390873128340956002971921)
              ·
                refine ⟨64043154846255717002228941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 85390873128340956002971921 64043154846255717002228941)
                ·
                  refine ⟨24016183067345893875835853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 64043154846255717002228941 24016183067345893875835853)
                  ·
                    refine ⟨9006068650254710203438445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24016183067345893875835853 9006068650254710203438445)
                    ·
                      refine ⟨3377275743845516326289417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9006068650254710203438445 3377275743845516326289417)
                      ·
                        rfl

theorem cell23_6577221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 2, 3, 3, 3].length) (baseStart_6577221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6577221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6577221 prefixEnd_6577221 := by exact prefixLift 6577221
  have htrace : WordTrace (prefixWord ++ tailWord_6577221) baseStart_6577221 baseEnd_6577221 := by
    simpa [prefixWord, tailWord_6577221, baseEnd_6577221] using wordTrace_append hprefix tailTrace_6577221
  have hstable : (prefixWord ++ tailWord_6577221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6577221).length < 2 ^ (prefixWord ++ tailWord_6577221).sum := by decide
  have hdescent : baseEnd_6577221 < baseStart_6577221 := by decide
  rcases family_descends (prefixWord ++ tailWord_6577221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6577291 : List Nat := [1, 1, 1, 1, 4, 1, 1, 5, 2, 2, 4]
def baseStart_6577291 : Nat := 118140960795 + 6577291 * 2 ^ 59
def prefixEnd_6577291 : Nat := 4983230072969 + 3 ^ 40 * 6577291 * 2
def baseEnd_6577291 : Nat := 3377311687491331052414095

theorem tailTrace_6577291 : CollatzResearch.WordTrace tailWord_6577291 prefixEnd_6577291 3377311687491331052414095 := by
  unfold tailWord_6577291
  simp only [CollatzResearch.WordTrace]
  refine ⟨239893510814605493716483727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159929007209736995810989151 239893510814605493716483727)
  ·
    refine ⟨359840266221908240574725591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 239893510814605493716483727 359840266221908240574725591)
    ·
      refine ⟨539760399332862360862088387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 359840266221908240574725591 539760399332862360862088387)
      ·
        refine ⟨809640598999293541293132581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 539760399332862360862088387 809640598999293541293132581)
        ·
          refine ⟨151807612312367538992462359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 809640598999293541293132581 151807612312367538992462359)
          ·
            refine ⟨227711418468551308488693539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 151807612312367538992462359 227711418468551308488693539)
            ·
              refine ⟨341567127702826962733040309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 227711418468551308488693539 341567127702826962733040309)
              ·
                refine ⟨32021918222140027756222529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 341567127702826962733040309 32021918222140027756222529)
                ·
                  refine ⟨24016438666605020817166897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32021918222140027756222529 24016438666605020817166897)
                  ·
                    refine ⟨18012328999953765612875173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24016438666605020817166897 18012328999953765612875173)
                    ·
                      refine ⟨3377311687491331052414095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18012328999953765612875173 3377311687491331052414095)
                      ·
                        rfl

theorem cell23_6577291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 5, 2, 2, 4].length) (baseStart_6577291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6577291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6577291 prefixEnd_6577291 := by exact prefixLift 6577291
  have htrace : WordTrace (prefixWord ++ tailWord_6577291) baseStart_6577291 baseEnd_6577291 := by
    simpa [prefixWord, tailWord_6577291, baseEnd_6577291] using wordTrace_append hprefix tailTrace_6577291
  have hstable : (prefixWord ++ tailWord_6577291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6577291).length < 2 ^ (prefixWord ++ tailWord_6577291).sum := by decide
  have hdescent : baseEnd_6577291 < baseStart_6577291 := by decide
  rcases family_descends (prefixWord ++ tailWord_6577291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6577298 : List Nat := [3, 2, 3, 1, 1, 2, 1, 2, 2, 1, 5]
def baseStart_6577298 : Nat := 118140960795 + 6577298 * 2 ^ 59
def prefixEnd_6577298 : Nat := 4983230072969 + 3 ^ 40 * 6577298 * 2
def baseEnd_6577298 : Nat := 3377315281855912525026563

theorem tailTrace_6577298 : CollatzResearch.WordTrace tailWord_6577298 prefixEnd_6577298 3377315281855912525026563 := by
  unfold tailWord_6577298
  simp only [CollatzResearch.WordTrace]
  refine ⟨59973441531395033477997137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 159929177417053422607992365 59973441531395033477997137)
  ·
    refine ⟨44980081148546275108497853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59973441531395033477997137 44980081148546275108497853)
    ·
      refine ⟨16867530430704853165686695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44980081148546275108497853 16867530430704853165686695)
      ·
        refine ⟨25301295646057279748530043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16867530430704853165686695 25301295646057279748530043)
        ·
          refine ⟨37951943469085919622795065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25301295646057279748530043 37951943469085919622795065)
          ·
            refine ⟨28463957601814439717096299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37951943469085919622795065 28463957601814439717096299)
            ·
              refine ⟨42695936402721659575644449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28463957601814439717096299 42695936402721659575644449)
              ·
                refine ⟨32021952302041244681733337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42695936402721659575644449 32021952302041244681733337)
                ·
                  refine ⟨24016464226530933511300003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32021952302041244681733337 24016464226530933511300003)
                  ·
                    refine ⟨36024696339796400266950005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24016464226530933511300003 36024696339796400266950005)
                    ·
                      refine ⟨3377315281855912525026563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36024696339796400266950005 3377315281855912525026563)
                      ·
                        rfl

theorem cell23_6577298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 1, 2, 2, 1, 5].length) (baseStart_6577298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6577298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6577298 prefixEnd_6577298 := by exact prefixLift 6577298
  have htrace : WordTrace (prefixWord ++ tailWord_6577298) baseStart_6577298 baseEnd_6577298 := by
    simpa [prefixWord, tailWord_6577298, baseEnd_6577298] using wordTrace_append hprefix tailTrace_6577298
  have hstable : (prefixWord ++ tailWord_6577298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6577298).length < 2 ^ (prefixWord ++ tailWord_6577298).sum := by decide
  have hdescent : baseEnd_6577298 < baseStart_6577298 := by decide
  rcases family_descends (prefixWord ++ tailWord_6577298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6577329 : List Nat := [1, 2, 2, 5, 1, 2, 2, 2, 2, 2, 2]
def baseStart_6577329 : Nat := 118140960795 + 6577329 * 2 ^ 59
def prefixEnd_6577329 : Nat := 4983230072969 + 3 ^ 40 * 6577329 * 2
def baseEnd_6577329 : Nat := 3377331199756201903738921

theorem tailTrace_6577329 : CollatzResearch.WordTrace tailWord_6577329 prefixEnd_6577329 3377331199756201903738921 := by
  unfold tailWord_6577329
  simp only [CollatzResearch.WordTrace]
  refine ⟨239894896788467826206367041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159929931192311884137578027 239894896788467826206367041)
  ·
    refine ⟨179921172591350869654775281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 239894896788467826206367041 179921172591350869654775281)
    ·
      refine ⟨134940879443513152241081461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 179921172591350869654775281 134940879443513152241081461)
      ·
        refine ⟨12650707447829358022601387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 134940879443513152241081461 12650707447829358022601387)
        ·
          refine ⟨18976061171744037033902081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12650707447829358022601387 18976061171744037033902081)
          ·
            refine ⟨14232045878808027775426561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18976061171744037033902081 14232045878808027775426561)
            ·
              refine ⟨10674034409106020831569921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14232045878808027775426561 10674034409106020831569921)
              ·
                refine ⟨8005525806829515623677441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10674034409106020831569921 8005525806829515623677441)
                ·
                  refine ⟨6004144355122136717758081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8005525806829515623677441 6004144355122136717758081)
                  ·
                    refine ⟨4503108266341602538318561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6004144355122136717758081 4503108266341602538318561)
                    ·
                      refine ⟨3377331199756201903738921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4503108266341602538318561 3377331199756201903738921)
                      ·
                        rfl

theorem cell23_6577329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 2, 2, 2, 2, 2].length) (baseStart_6577329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6577329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6577329 prefixEnd_6577329 := by exact prefixLift 6577329
  have htrace : WordTrace (prefixWord ++ tailWord_6577329) baseStart_6577329 baseEnd_6577329 := by
    simpa [prefixWord, tailWord_6577329, baseEnd_6577329] using wordTrace_append hprefix tailTrace_6577329
  have hstable : (prefixWord ++ tailWord_6577329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6577329).length < 2 ^ (prefixWord ++ tailWord_6577329).sum := by decide
  have hdescent : baseEnd_6577329 < baseStart_6577329 := by decide
  rcases family_descends (prefixWord ++ tailWord_6577329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6577345 : List Nat := [1, 2, 6, 1, 1, 1, 1, 1, 1, 5, 3]
def baseStart_6577345 : Nat := 118140960795 + 6577345 * 2 ^ 59
def prefixEnd_6577345 : Nat := 4983230072969 + 3 ^ 40 * 6577345 * 2
def baseEnd_6577345 : Nat := 3377339415446673841138847

theorem tailTrace_6577345 : CollatzResearch.WordTrace tailWord_6577345 prefixEnd_6577345 3377339415446673841138847 := by
  unfold tailWord_6577345
  simp only [CollatzResearch.WordTrace]
  refine ⟨239895480356409860938949489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159930320237606573959299659 239895480356409860938949489)
  ·
    refine ⟨179921610267307395704212117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 239895480356409860938949489 179921610267307395704212117)
    ·
      refine ⟨8433825481280034173634943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 179921610267307395704212117 8433825481280034173634943)
      ·
        refine ⟨12650738221920051260452415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8433825481280034173634943 12650738221920051260452415)
        ·
          refine ⟨18976107332880076890678623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12650738221920051260452415 18976107332880076890678623)
          ·
            refine ⟨28464160999320115336017935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18976107332880076890678623 28464160999320115336017935)
            ·
              refine ⟨42696241498980173004026903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28464160999320115336017935 42696241498980173004026903)
              ·
                refine ⟨64044362248470259506040355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42696241498980173004026903 64044362248470259506040355)
                ·
                  refine ⟨96066543372705389259060533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 64044362248470259506040355 96066543372705389259060533)
                  ·
                    refine ⟨9006238441191130243036925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 96066543372705389259060533 9006238441191130243036925)
                    ·
                      refine ⟨3377339415446673841138847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9006238441191130243036925 3377339415446673841138847)
                      ·
                        rfl

theorem cell23_6577345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 1, 1, 1, 5, 3].length) (baseStart_6577345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6577345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6577345 prefixEnd_6577345 := by exact prefixLift 6577345
  have htrace : WordTrace (prefixWord ++ tailWord_6577345) baseStart_6577345 baseEnd_6577345 := by
    simpa [prefixWord, tailWord_6577345, baseEnd_6577345] using wordTrace_append hprefix tailTrace_6577345
  have hstable : (prefixWord ++ tailWord_6577345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6577345).length < 2 ^ (prefixWord ++ tailWord_6577345).sum := by decide
  have hdescent : baseEnd_6577345 < baseStart_6577345 := by decide
  rcases family_descends (prefixWord ++ tailWord_6577345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6577346 : List Nat := [3, 5, 1, 1, 2, 1, 2, 1, 1, 4, 2]
def baseStart_6577346 : Nat := 118140960795 + 6577346 * 2 ^ 59
def prefixEnd_6577346 : Nat := 4983230072969 + 3 ^ 40 * 6577346 * 2
def baseEnd_6577346 : Nat := 3377339928927328337226343

theorem tailTrace_6577346 : CollatzResearch.WordTrace tailWord_6577346 prefixEnd_6577346 3377339928927328337226343 := by
  unfold tailWord_6577346
  simp only [CollatzResearch.WordTrace]
  refine ⟨59973879207351559527433973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 159930344552937492073157261 59973879207351559527433973)
  ·
    refine ⟨5622551175689208705696935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 59973879207351559527433973 5622551175689208705696935)
    ·
      refine ⟨8433826763533813058545403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5622551175689208705696935 8433826763533813058545403)
      ·
        refine ⟨12650740145300719587818105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8433826763533813058545403 12650740145300719587818105)
        ·
          refine ⟨9488055108975539690863579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12650740145300719587818105 9488055108975539690863579)
          ·
            refine ⟨14232082663463309536295369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9488055108975539690863579 14232082663463309536295369)
            ·
              refine ⟨10674061997597482152221527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14232082663463309536295369 10674061997597482152221527)
              ·
                refine ⟨16011092996396223228332291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10674061997597482152221527 16011092996396223228332291)
                ·
                  refine ⟨24016639494594334842498437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16011092996396223228332291 24016639494594334842498437)
                  ·
                    refine ⟨4503119905236437782968457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24016639494594334842498437 4503119905236437782968457)
                    ·
                      refine ⟨3377339928927328337226343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4503119905236437782968457 3377339928927328337226343)
                      ·
                        rfl

theorem cell23_6577346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 2, 1, 1, 4, 2].length) (baseStart_6577346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6577346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6577346 prefixEnd_6577346 := by exact prefixLift 6577346
  have htrace : WordTrace (prefixWord ++ tailWord_6577346) baseStart_6577346 baseEnd_6577346 := by
    simpa [prefixWord, tailWord_6577346, baseEnd_6577346] using wordTrace_append hprefix tailTrace_6577346
  have hstable : (prefixWord ++ tailWord_6577346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6577346).length < 2 ^ (prefixWord ++ tailWord_6577346).sum := by decide
  have hdescent : baseEnd_6577346 < baseStart_6577346 := by decide
  rcases family_descends (prefixWord ++ tailWord_6577346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6577365 : List Nat := [1, 3, 2, 4, 1, 1, 3, 1, 2, 5]
def baseStart_6577365 : Nat := 118140960795 + 6577365 * 2 ^ 59
def prefixEnd_6577365 : Nat := 4983230072969 + 3 ^ 40 * 6577365 * 2
def baseEnd_6577365 : Nat := 1125783228353254587629585

theorem tailTrace_6577365 : CollatzResearch.WordTrace tailWord_6577365 prefixEnd_6577365 1125783228353254587629585 := by
  unfold tailWord_6577365
  simp only [CollatzResearch.WordTrace]
  refine ⟨239896209816337404354677549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159930806544224936236451699 239896209816337404354677549)
  ·
    refine ⟨89961078681126526633004081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 239896209816337404354677549 89961078681126526633004081)
    ·
      refine ⟨67470809010844894974753061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89961078681126526633004081 67470809010844894974753061)
      ·
        refine ⟨12650776689533417807766199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 67470809010844894974753061 12650776689533417807766199)
        ·
          refine ⟨18976165034300126711649299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12650776689533417807766199 18976165034300126711649299)
          ·
            refine ⟨28464247551450190067473949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18976165034300126711649299 28464247551450190067473949)
            ·
              refine ⟨10674092831793821275302731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28464247551450190067473949 10674092831793821275302731)
              ·
                refine ⟨16011139247690731912954097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10674092831793821275302731 16011139247690731912954097)
                ·
                  refine ⟨12008354435768048934715573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16011139247690731912954097 12008354435768048934715573)
                  ·
                    refine ⟨1125783228353254587629585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12008354435768048934715573 1125783228353254587629585)
                    ·
                      rfl

theorem cell23_6577365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 3, 1, 2, 5].length) (baseStart_6577365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6577365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6577365 prefixEnd_6577365 := by exact prefixLift 6577365
  have htrace : WordTrace (prefixWord ++ tailWord_6577365) baseStart_6577365 baseEnd_6577365 := by
    simpa [prefixWord, tailWord_6577365, baseEnd_6577365] using wordTrace_append hprefix tailTrace_6577365
  have hstable : (prefixWord ++ tailWord_6577365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6577365).length < 2 ^ (prefixWord ++ tailWord_6577365).sum := by decide
  have hdescent : baseEnd_6577365 < baseStart_6577365 := by decide
  rcases family_descends (prefixWord ++ tailWord_6577365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6577395 : List Nat := [1, 1, 1, 2, 2, 6, 2, 1, 3, 4]
def baseStart_6577395 : Nat := 118140960795 + 6577395 * 2 ^ 59
def prefixEnd_6577395 : Nat := 4983230072969 + 3 ^ 40 * 6577395 * 2
def baseEnd_6577395 : Nat := 1125788363159799548504539

theorem tailTrace_6577395 : CollatzResearch.WordTrace tailWord_6577395 prefixEnd_6577395 1125788363159799548504539 := by
  unfold tailWord_6577395
  simp only [CollatzResearch.WordTrace]
  refine ⟨239897304006228719478269639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159931536004152479652179759 239897304006228719478269639)
  ·
    refine ⟨359845956009343079217404459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 239897304006228719478269639 359845956009343079217404459)
    ·
      refine ⟨539768934014014618826106689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 359845956009343079217404459 539768934014014618826106689)
      ·
        refine ⟨404826700510510964119580017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 539768934014014618826106689 404826700510510964119580017)
        ·
          refine ⟨303620025382883223089685013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 404826700510510964119580017 303620025382883223089685013)
          ·
            refine ⟨14232188689822651082328985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 303620025382883223089685013 14232188689822651082328985)
            ·
              refine ⟨10674141517366988311746739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14232188689822651082328985 10674141517366988311746739)
              ·
                refine ⟨16011212276050482467620109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10674141517366988311746739 16011212276050482467620109)
                ·
                  refine ⟨6004204603518930925357541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16011212276050482467620109 6004204603518930925357541)
                  ·
                    refine ⟨1125788363159799548504539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6004204603518930925357541 1125788363159799548504539)
                    ·
                      rfl

theorem cell23_6577395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 2, 1, 3, 4].length) (baseStart_6577395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6577395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6577395 prefixEnd_6577395 := by exact prefixLift 6577395
  have htrace : WordTrace (prefixWord ++ tailWord_6577395) baseStart_6577395 baseEnd_6577395 := by
    simpa [prefixWord, tailWord_6577395, baseEnd_6577395] using wordTrace_append hprefix tailTrace_6577395
  have hstable : (prefixWord ++ tailWord_6577395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6577395).length < 2 ^ (prefixWord ++ tailWord_6577395).sum := by decide
  have hdescent : baseEnd_6577395 < baseStart_6577395 := by decide
  rcases family_descends (prefixWord ++ tailWord_6577395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6577398 : List Nat := [5, 1, 1, 1, 1, 1, 1, 1, 4, 1, 6]
def baseStart_6577398 : Nat := 118140960795 + 6577398 * 2 ^ 59
def prefixEnd_6577398 : Nat := 4983230072969 + 3 ^ 40 * 6577398 * 2
def baseEnd_6577398 : Nat := 3377366629921362133776103

theorem tailTrace_6577398 : CollatzResearch.WordTrace tailWord_6577398 prefixEnd_6577398 3377366629921362133776103 := by
  unfold tailWord_6577398
  simp only [CollatzResearch.WordTrace]
  refine ⟨14993588339076115686914303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 159931608950145233993752565 14993588339076115686914303)
  ·
    refine ⟨22490382508614173530371455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14993588339076115686914303 22490382508614173530371455)
    ·
      refine ⟨33735573762921260295557183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22490382508614173530371455 33735573762921260295557183)
      ·
        refine ⟨50603360644381890443335775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33735573762921260295557183 50603360644381890443335775)
        ·
          refine ⟨75905040966572835665003663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50603360644381890443335775 75905040966572835665003663)
          ·
            refine ⟨113857561449859253497505495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75905040966572835665003663 113857561449859253497505495)
            ·
              refine ⟨170786342174788880246258243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 113857561449859253497505495 170786342174788880246258243)
              ·
                refine ⟨256179513262183320369387365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 170786342174788880246258243 256179513262183320369387365)
                ·
                  refine ⟨48033658736659372569260131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 256179513262183320369387365 48033658736659372569260131)
                  ·
                    refine ⟨72050488104989058853890197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 48033658736659372569260131 72050488104989058853890197)
                    ·
                      refine ⟨3377366629921362133776103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 72050488104989058853890197 3377366629921362133776103)
                      ·
                        rfl

theorem cell23_6577398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 1, 4, 1, 6].length) (baseStart_6577398 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6577398 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6577398 prefixEnd_6577398 := by exact prefixLift 6577398
  have htrace : WordTrace (prefixWord ++ tailWord_6577398) baseStart_6577398 baseEnd_6577398 := by
    simpa [prefixWord, tailWord_6577398, baseEnd_6577398] using wordTrace_append hprefix tailTrace_6577398
  have hstable : (prefixWord ++ tailWord_6577398).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6577398).length < 2 ^ (prefixWord ++ tailWord_6577398).sum := by decide
  have hdescent : baseEnd_6577398 < baseStart_6577398 := by decide
  rcases family_descends (prefixWord ++ tailWord_6577398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6577418 : List Nat := [3, 1, 2, 2, 1, 1, 1, 1, 1, 7, 3]
def baseStart_6577418 : Nat := 118140960795 + 6577418 * 2 ^ 59
def prefixEnd_6577418 : Nat := 4983230072969 + 3 ^ 40 * 6577418 * 2
def baseEnd_6577418 : Nat := 3377376899534452055526011

theorem tailTrace_6577418 : CollatzResearch.WordTrace tailWord_6577418 prefixEnd_6577418 3377376899534452055526011 := by
  unfold tailWord_6577418
  simp only [CollatzResearch.WordTrace]
  refine ⟨59974535721286348601589227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 159932095256763596270904605 59974535721286348601589227)
  ·
    refine ⟨89961803581929522902383841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59974535721286348601589227 89961803581929522902383841)
    ·
      refine ⟨67471352686447142176787881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89961803581929522902383841 67471352686447142176787881)
      ·
        refine ⟨50603514514835356632590911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67471352686447142176787881 50603514514835356632590911)
        ·
          refine ⟨75905271772253034948886367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50603514514835356632590911 75905271772253034948886367)
          ·
            refine ⟨113857907658379552423329551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75905271772253034948886367 113857907658379552423329551)
            ·
              refine ⟨170786861487569328634994327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 113857907658379552423329551 170786861487569328634994327)
              ·
                refine ⟨256180292231353992952491491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 170786861487569328634994327 256180292231353992952491491)
                ·
                  refine ⟨384270438347030989428737237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 256180292231353992952491491 384270438347030989428737237)
                  ·
                    refine ⟨9006338398758538814736029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 384270438347030989428737237 9006338398758538814736029)
                    ·
                      refine ⟨3377376899534452055526011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9006338398758538814736029 3377376899534452055526011)
                      ·
                        rfl

theorem cell23_6577418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 1, 1, 7, 3].length) (baseStart_6577418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6577418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6577418 prefixEnd_6577418 := by exact prefixLift 6577418
  have htrace : WordTrace (prefixWord ++ tailWord_6577418) baseStart_6577418 baseEnd_6577418 := by
    simpa [prefixWord, tailWord_6577418, baseEnd_6577418] using wordTrace_append hprefix tailTrace_6577418
  have hstable : (prefixWord ++ tailWord_6577418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6577418).length < 2 ^ (prefixWord ++ tailWord_6577418).sum := by decide
  have hdescent : baseEnd_6577418 < baseStart_6577418 := by decide
  rcases family_descends (prefixWord ++ tailWord_6577418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6577495 : List Nat := [1, 1, 3, 2, 3, 2, 3, 1, 1, 1, 5]
def baseStart_6577495 : Nat := 118140960795 + 6577495 * 2 ^ 59
def prefixEnd_6577495 : Nat := 4983230072969 + 3 ^ 40 * 6577495 * 2
def baseEnd_6577495 : Nat := 3377416437544848254263157

theorem tailTrace_6577495 : CollatzResearch.WordTrace tailWord_6577495 prefixEnd_6577495 3377416437544848254263157 := by
  unfold tailWord_6577495
  simp only [CollatzResearch.WordTrace]
  refine ⟨239900951305866436556909939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159933967537244291037939959 239900951305866436556909939)
  ·
    refine ⟨359851426958799654835364909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 239900951305866436556909939 359851426958799654835364909)
    ·
      refine ⟨134944285109549870563261841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 359851426958799654835364909 134944285109549870563261841)
      ·
        refine ⟨101208213832162402922446381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 134944285109549870563261841 101208213832162402922446381)
        ·
          refine ⟨37953080187060901095917393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 101208213832162402922446381 37953080187060901095917393)
          ·
            refine ⟨28464810140295675821938045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37953080187060901095917393 28464810140295675821938045)
            ·
              refine ⟨10674303802610878433226767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28464810140295675821938045 10674303802610878433226767)
              ·
                refine ⟨16011455703916317649840151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10674303802610878433226767 16011455703916317649840151)
                ·
                  refine ⟨24017183555874476474760227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16011455703916317649840151 24017183555874476474760227)
                  ·
                    refine ⟨36025775333811714712140341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24017183555874476474760227 36025775333811714712140341)
                    ·
                      refine ⟨3377416437544848254263157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36025775333811714712140341 3377416437544848254263157)
                      ·
                        rfl

theorem cell23_6577495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 3, 1, 1, 1, 5].length) (baseStart_6577495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6577495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6577495 prefixEnd_6577495 := by exact prefixLift 6577495
  have htrace : WordTrace (prefixWord ++ tailWord_6577495) baseStart_6577495 baseEnd_6577495 := by
    simpa [prefixWord, tailWord_6577495, baseEnd_6577495] using wordTrace_append hprefix tailTrace_6577495
  have hstable : (prefixWord ++ tailWord_6577495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6577495).length < 2 ^ (prefixWord ++ tailWord_6577495).sum := by decide
  have hdescent : baseEnd_6577495 < baseStart_6577495 := by decide
  rcases family_descends (prefixWord ++ tailWord_6577495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6577575 : List Nat := [1, 1, 6, 1, 1, 1, 1, 3, 2, 6]
def baseStart_6577575 : Nat := 118140960795 + 6577575 * 2 ^ 59
def prefixEnd_6577575 : Nat := 4983230072969 + 3 ^ 40 * 6577575 * 2
def baseEnd_6577575 : Nat := 1125819171999069313754263

theorem tailTrace_6577575 : CollatzResearch.WordTrace tailWord_6577575 prefixEnd_6577575 1125819171999069313754263 := by
  unfold tailWord_6577575
  simp only [CollatzResearch.WordTrace]
  refine ⟨239903869145576610219822179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159935912763717740146548119 239903869145576610219822179)
  ·
    refine ⟨359855803718364915329733269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 239903869145576610219822179 359855803718364915329733269)
    ·
      refine ⟨16868240799298355406081247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 359855803718364915329733269 16868240799298355406081247)
      ·
        refine ⟨25302361198947533109121871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16868240799298355406081247 25302361198947533109121871)
        ·
          refine ⟨37953541798421299663682807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25302361198947533109121871 37953541798421299663682807)
          ·
            refine ⟨56930312697631949495524211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37953541798421299663682807 56930312697631949495524211)
            ·
              refine ⟨85395469046447924243286317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56930312697631949495524211 85395469046447924243286317)
              ·
                refine ⟨32023300892417971591232369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 85395469046447924243286317 32023300892417971591232369)
                ·
                  refine ⟨24017475669313478693424277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32023300892417971591232369 24017475669313478693424277)
                  ·
                    refine ⟨1125819171999069313754263, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24017475669313478693424277 1125819171999069313754263)
                    ·
                      rfl

theorem cell23_6577575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 3, 2, 6].length) (baseStart_6577575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6577575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6577575 prefixEnd_6577575 := by exact prefixLift 6577575
  have htrace : WordTrace (prefixWord ++ tailWord_6577575) baseStart_6577575 baseEnd_6577575 := by
    simpa [prefixWord, tailWord_6577575, baseEnd_6577575] using wordTrace_append hprefix tailTrace_6577575
  have hstable : (prefixWord ++ tailWord_6577575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6577575).length < 2 ^ (prefixWord ++ tailWord_6577575).sum := by decide
  have hdescent : baseEnd_6577575 < baseStart_6577575 := by decide
  rcases family_descends (prefixWord ++ tailWord_6577575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6577576 : List Nat := [2, 1, 6, 1, 2, 2, 1, 1, 1, 3, 3]
def baseStart_6577576 : Nat := 118140960795 + 6577576 * 2 ^ 59
def prefixEnd_6577576 : Nat := 4983230072969 + 3 ^ 40 * 6577576 * 2
def baseEnd_6577576 : Nat := 3377458029477862437350285

theorem tailTrace_6577576 : CollatzResearch.WordTrace tailWord_6577576 prefixEnd_6577576 3377458029477862437350285 := by
  unfold tailWord_6577576
  simp only [CollatzResearch.WordTrace]
  refine ⟨119951952809286493695304291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159935937079048658260405721 119951952809286493695304291)
  ·
    refine ⟨179927929213929740542956437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119951952809286493695304291 179927929213929740542956437)
    ·
      refine ⟨8434121681902956587951083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 179927929213929740542956437 8434121681902956587951083)
      ·
        refine ⟨12651182522854434881926625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8434121681902956587951083 12651182522854434881926625)
        ·
          refine ⟨9488386892140826161444969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12651182522854434881926625 9488386892140826161444969)
          ·
            refine ⟨7116290169105619621083727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9488386892140826161444969 7116290169105619621083727)
            ·
              refine ⟨10674435253658429431625591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7116290169105619621083727 10674435253658429431625591)
              ·
                refine ⟨16011652880487644147438387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10674435253658429431625591 16011652880487644147438387)
                ·
                  refine ⟨24017479320731466221157581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16011652880487644147438387 24017479320731466221157581)
                  ·
                    refine ⟨9006554745274299832934093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24017479320731466221157581 9006554745274299832934093)
                    ·
                      refine ⟨3377458029477862437350285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9006554745274299832934093 3377458029477862437350285)
                      ·
                        rfl

theorem cell23_6577576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 2, 1, 1, 1, 3, 3].length) (baseStart_6577576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6577576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6577576 prefixEnd_6577576 := by exact prefixLift 6577576
  have htrace : WordTrace (prefixWord ++ tailWord_6577576) baseStart_6577576 baseEnd_6577576 := by
    simpa [prefixWord, tailWord_6577576, baseEnd_6577576] using wordTrace_append hprefix tailTrace_6577576
  have hstable : (prefixWord ++ tailWord_6577576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6577576).length < 2 ^ (prefixWord ++ tailWord_6577576).sum := by decide
  have hdescent : baseEnd_6577576 < baseStart_6577576 := by decide
  rcases family_descends (prefixWord ++ tailWord_6577576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6577585 : List Nat := [1, 2, 2, 4, 1, 1, 2, 2, 2, 1, 5]
def baseStart_6577585 : Nat := 118140960795 + 6577585 * 2 ^ 59
def prefixEnd_6577585 : Nat := 4983230072969 + 3 ^ 40 * 6577585 * 2
def baseEnd_6577585 : Nat := 3377462650803752902137743

theorem tailTrace_6577585 : CollatzResearch.WordTrace tailWord_6577585 prefixEnd_6577585 3377462650803752902137743 := by
  unfold tailWord_6577585
  simp only [CollatzResearch.WordTrace]
  refine ⟨239904233875540381927686209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159936155917026921285124139 239904233875540381927686209)
  ·
    refine ⟨179928175406655286445764657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 239904233875540381927686209 179928175406655286445764657)
    ·
      refine ⟨134946131554991464834323493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 179928175406655286445764657 134946131554991464834323493)
      ·
        refine ⟨25302399666560899656435655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 134946131554991464834323493 25302399666560899656435655)
        ·
          refine ⟨37953599499841349484653483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25302399666560899656435655 37953599499841349484653483)
          ·
            refine ⟨56930399249762024226980225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37953599499841349484653483 56930399249762024226980225)
            ·
              refine ⟨42697799437321518170235169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56930399249762024226980225 42697799437321518170235169)
              ·
                refine ⟨32023349577991138627676377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42697799437321518170235169 32023349577991138627676377)
                ·
                  refine ⟨24017512183493353970757283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32023349577991138627676377 24017512183493353970757283)
                  ·
                    refine ⟨36026268275240030956135925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24017512183493353970757283 36026268275240030956135925)
                    ·
                      refine ⟨3377462650803752902137743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36026268275240030956135925 3377462650803752902137743)
                      ·
                        rfl

theorem cell23_6577585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 2, 2, 2, 1, 5].length) (baseStart_6577585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6577585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6577585 prefixEnd_6577585 := by exact prefixLift 6577585
  have htrace : WordTrace (prefixWord ++ tailWord_6577585) baseStart_6577585 baseEnd_6577585 := by
    simpa [prefixWord, tailWord_6577585, baseEnd_6577585] using wordTrace_append hprefix tailTrace_6577585
  have hstable : (prefixWord ++ tailWord_6577585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6577585).length < 2 ^ (prefixWord ++ tailWord_6577585).sum := by decide
  have hdescent : baseEnd_6577585 < baseStart_6577585 := by decide
  rcases family_descends (prefixWord ++ tailWord_6577585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6577615 : List Nat := [1, 1, 2, 1, 1, 4, 2, 1, 4, 3, 3]
def baseStart_6577615 : Nat := 118140960795 + 6577615 * 2 ^ 59
def prefixEnd_6577615 : Nat := 4983230072969 + 3 ^ 40 * 6577615 * 2
def baseEnd_6577615 : Nat := 3377478055223387784762605

theorem tailTrace_6577615 : CollatzResearch.WordTrace tailWord_6577615 prefixEnd_6577615 3377478055223387784762605 := by
  unfold tailWord_6577615
  simp only [CollatzResearch.WordTrace]
  refine ⟨239905328065431697051278299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159936885376954464700852199 239905328065431697051278299)
  ·
    refine ⟨359857992098147545576917449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 239905328065431697051278299 359857992098147545576917449)
    ·
      refine ⟨269893494073610659182688087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 359857992098147545576917449 269893494073610659182688087)
      ·
        refine ⟨404840241110415988774032131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 269893494073610659182688087 404840241110415988774032131)
        ·
          refine ⟨607260361665623983161048197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 404840241110415988774032131 607260361665623983161048197)
          ·
            refine ⟨113861317812304496842696537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 607260361665623983161048197 113861317812304496842696537)
            ·
              refine ⟨85395988359228372632022403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 113861317812304496842696537 85395988359228372632022403)
              ·
                refine ⟨128093982538842558948033605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 85395988359228372632022403 128093982538842558948033605)
                ·
                  refine ⟨24017621726032979802756301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 128093982538842558948033605 24017621726032979802756301)
                  ·
                    refine ⟨9006608147262367426033613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24017621726032979802756301 9006608147262367426033613)
                    ·
                      refine ⟨3377478055223387784762605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9006608147262367426033613 3377478055223387784762605)
                      ·
                        rfl

theorem cell23_6577615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 1, 4, 3, 3].length) (baseStart_6577615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6577615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6577615 prefixEnd_6577615 := by exact prefixLift 6577615
  have htrace : WordTrace (prefixWord ++ tailWord_6577615) baseStart_6577615 baseEnd_6577615 := by
    simpa [prefixWord, tailWord_6577615, baseEnd_6577615] using wordTrace_append hprefix tailTrace_6577615
  have hstable : (prefixWord ++ tailWord_6577615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6577615).length < 2 ^ (prefixWord ++ tailWord_6577615).sum := by decide
  have hdescent : baseEnd_6577615 < baseStart_6577615 := by decide
  rcases family_descends (prefixWord ++ tailWord_6577615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6577633 : List Nat := [1, 2, 3, 1, 2, 5, 2, 1, 2, 2, 2]
def baseStart_6577633 : Nat := 118140960795 + 6577633 * 2 ^ 59
def prefixEnd_6577633 : Nat := 4983230072969 + 3 ^ 40 * 6577633 * 2
def baseEnd_6577633 : Nat := 3377487297875168714337523

theorem tailTrace_6577633 : CollatzResearch.WordTrace tailWord_6577633 prefixEnd_6577633 3377487297875168714337523 := by
  unfold tailWord_6577633
  simp only [CollatzResearch.WordTrace]
  refine ⟨239905984579366486125433553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159937323052910990750289035 239905984579366486125433553)
  ·
    refine ⟨179929488434524864594075165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 239905984579366486125433553 179929488434524864594075165)
    ·
      refine ⟨67473558162946824222778187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 179929488434524864594075165 67473558162946824222778187)
      ·
        refine ⟨101210337244420236334167281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67473558162946824222778187 101210337244420236334167281)
        ·
          refine ⟨75907752933315177250625461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101210337244420236334167281 75907752933315177250625461)
          ·
            refine ⟨7116351837498297867246137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 75907752933315177250625461 7116351837498297867246137)
            ·
              refine ⟨5337263878123723400434603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7116351837498297867246137 5337263878123723400434603)
              ·
                refine ⟨8005895817185585100651905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5337263878123723400434603 8005895817185585100651905)
                ·
                  refine ⟨6004421862889188825488929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8005895817185585100651905 6004421862889188825488929)
                  ·
                    refine ⟨4503316397166891619116697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6004421862889188825488929 4503316397166891619116697)
                    ·
                      refine ⟨3377487297875168714337523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4503316397166891619116697 3377487297875168714337523)
                      ·
                        rfl

theorem cell23_6577633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 5, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 5, 2, 1, 2, 2, 2].length) (baseStart_6577633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6577633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6577633 prefixEnd_6577633 := by exact prefixLift 6577633
  have htrace : WordTrace (prefixWord ++ tailWord_6577633) baseStart_6577633 baseEnd_6577633 := by
    simpa [prefixWord, tailWord_6577633, baseEnd_6577633] using wordTrace_append hprefix tailTrace_6577633
  have hstable : (prefixWord ++ tailWord_6577633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6577633).length < 2 ^ (prefixWord ++ tailWord_6577633).sum := by decide
  have hdescent : baseEnd_6577633 < baseStart_6577633 := by decide
  rcases family_descends (prefixWord ++ tailWord_6577633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6577672 : List Nat := [2, 1, 3, 2, 1, 1, 4, 2, 2, 1, 4]
def baseStart_6577672 : Nat := 118140960795 + 6577672 * 2 ^ 59
def prefixEnd_6577672 : Nat := 4983230072969 + 3 ^ 40 * 6577672 * 2
def baseEnd_6577672 : Nat := 3377507323620694061749843

theorem tailTrace_6577672 : CollatzResearch.WordTrace tailWord_6577672 prefixEnd_6577672 3377507323620694061749843 := by
  unfold tailWord_6577672
  simp only [CollatzResearch.WordTrace]
  refine ⟨119953703513112597893051635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159938271350816797190735513 119953703513112597893051635)
  ·
    refine ⟨179930555269668896839577453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119953703513112597893051635 179930555269668896839577453)
    ·
      refine ⟨67473958226125836314841545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 179930555269668896839577453 67473958226125836314841545)
      ·
        refine ⟨50605468669594377236131159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67473958226125836314841545 50605468669594377236131159)
        ·
          refine ⟨75908203004391565854196739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50605468669594377236131159 75908203004391565854196739)
          ·
            refine ⟨113862304506587348781295109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75908203004391565854196739 113862304506587348781295109)
            ·
              refine ⟨21349182094985127896492833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 113862304506587348781295109 21349182094985127896492833)
              ·
                refine ⟨16011886571238845922369625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21349182094985127896492833 16011886571238845922369625)
                ·
                  refine ⟨12008914928429134441777219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16011886571238845922369625 12008914928429134441777219)
                  ·
                    refine ⟨18013372392643701662665829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12008914928429134441777219 18013372392643701662665829)
                    ·
                      refine ⟨3377507323620694061749843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18013372392643701662665829 3377507323620694061749843)
                      ·
                        rfl

theorem cell23_6577672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 4, 2, 2, 1, 4].length) (baseStart_6577672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6577672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6577672 prefixEnd_6577672 := by exact prefixLift 6577672
  have htrace : WordTrace (prefixWord ++ tailWord_6577672) baseStart_6577672 baseEnd_6577672 := by
    simpa [prefixWord, tailWord_6577672, baseEnd_6577672] using wordTrace_append hprefix tailTrace_6577672
  have hstable : (prefixWord ++ tailWord_6577672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6577672).length < 2 ^ (prefixWord ++ tailWord_6577672).sum := by decide
  have hdescent : baseEnd_6577672 < baseStart_6577672 := by decide
  rcases family_descends (prefixWord ++ tailWord_6577672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6577692 : List Nat := [2, 2, 3, 1, 2, 1, 2, 2, 1, 4, 3]
def baseStart_6577692 : Nat := 118140960795 + 6577692 * 2 ^ 59
def prefixEnd_6577692 : Nat := 4983230072969 + 3 ^ 40 * 6577692 * 2
def baseEnd_6577692 : Nat := 3377517593233783983499751

theorem tailTrace_6577692 : CollatzResearch.WordTrace tailWord_6577692 prefixEnd_6577692 3377517593233783983499751 := by
  unfold tailWord_6577692
  simp only [CollatzResearch.WordTrace]
  refine ⟨119954068243076369600915665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159938757657435159467887553 119954068243076369600915665)
  ·
    refine ⟨89965551182307277200686749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119954068243076369600915665 89965551182307277200686749)
    ·
      refine ⟨33737081693365228950257531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 89965551182307277200686749 33737081693365228950257531)
      ·
        refine ⟨50605622540047843425386297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33737081693365228950257531 50605622540047843425386297)
        ·
          refine ⟨37954216905035882569039723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50605622540047843425386297 37954216905035882569039723)
          ·
            refine ⟨56931325357553823853559585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37954216905035882569039723 56931325357553823853559585)
            ·
              refine ⟨42698494018165367890169689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56931325357553823853559585 42698494018165367890169689)
              ·
                refine ⟨32023870513624025917627267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42698494018165367890169689 32023870513624025917627267)
                ·
                  refine ⟨48035805770436038876440901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32023870513624025917627267 48035805770436038876440901)
                  ·
                    refine ⟨9006713581956757289332669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 48035805770436038876440901 9006713581956757289332669)
                    ·
                      refine ⟨3377517593233783983499751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9006713581956757289332669 3377517593233783983499751)
                      ·
                        rfl

theorem cell23_6577692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 2, 2, 1, 4, 3].length) (baseStart_6577692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6577692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6577692 prefixEnd_6577692 := by exact prefixLift 6577692
  have htrace : WordTrace (prefixWord ++ tailWord_6577692) baseStart_6577692 baseEnd_6577692 := by
    simpa [prefixWord, tailWord_6577692, baseEnd_6577692] using wordTrace_append hprefix tailTrace_6577692
  have hstable : (prefixWord ++ tailWord_6577692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6577692).length < 2 ^ (prefixWord ++ tailWord_6577692).sum := by decide
  have hdescent : baseEnd_6577692 < baseStart_6577692 := by decide
  rcases family_descends (prefixWord ++ tailWord_6577692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6577699 : List Nat := [1, 1, 1, 4, 5, 1, 1, 2, 3, 4]
def baseStart_6577699 : Nat := 118140960795 + 6577699 * 2 ^ 59
def prefixEnd_6577699 : Nat := 4983230072969 + 3 ^ 40 * 6577699 * 2
def baseEnd_6577699 : Nat := 1125840395866121818704073

theorem tailTrace_6577699 : CollatzResearch.WordTrace tailWord_6577699 prefixEnd_6577699 1125840395866121818704073 := by
  unfold tailWord_6577699
  simp only [CollatzResearch.WordTrace]
  refine ⟨239908391797127379397336151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159938927864751586264890767 239908391797127379397336151)
  ·
    refine ⟨359862587695691069096004227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 239908391797127379397336151 359862587695691069096004227)
    ·
      refine ⟨539793881543536603644006341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 359862587695691069096004227 539793881543536603644006341)
      ·
        refine ⟨101211352789413113183251189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 539793881543536603644006341 101211352789413113183251189)
        ·
          refine ⟨9488564324007479360929799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 101211352789413113183251189 9488564324007479360929799)
          ·
            refine ⟨14232846486011219041394699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9488564324007479360929799 14232846486011219041394699)
            ·
              refine ⟨21349269729016828562092049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14232846486011219041394699 21349269729016828562092049)
              ·
                refine ⟨16011952296762621421569037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21349269729016828562092049 16011952296762621421569037)
                ·
                  refine ⟨6004482111285983033088389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16011952296762621421569037 6004482111285983033088389)
                  ·
                    refine ⟨1125840395866121818704073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6004482111285983033088389 1125840395866121818704073)
                    ·
                      rfl

theorem cell23_6577699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 1, 2, 3, 4].length) (baseStart_6577699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6577699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6577699 prefixEnd_6577699 := by exact prefixLift 6577699
  have htrace : WordTrace (prefixWord ++ tailWord_6577699) baseStart_6577699 baseEnd_6577699 := by
    simpa [prefixWord, tailWord_6577699, baseEnd_6577699] using wordTrace_append hprefix tailTrace_6577699
  have hstable : (prefixWord ++ tailWord_6577699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6577699).length < 2 ^ (prefixWord ++ tailWord_6577699).sum := by decide
  have hdescent : baseEnd_6577699 < baseStart_6577699 := by decide
  rcases family_descends (prefixWord ++ tailWord_6577699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6577756 : List Nat := [2, 2, 4, 1, 2, 1, 2, 2, 3, 1, 3]
def baseStart_6577756 : Nat := 118140960795 + 6577756 * 2 ^ 59
def prefixEnd_6577756 : Nat := 4983230072969 + 3 ^ 40 * 6577756 * 2
def baseEnd_6577756 : Nat := 3377550455995671733099457

theorem tailTrace_6577756 : CollatzResearch.WordTrace tailWord_6577756 prefixEnd_6577756 3377550455995671733099457 := by
  unfold tailWord_6577756
  simp only [CollatzResearch.WordTrace]
  refine ⟨119955235378960439066080561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159940313838613918754774081 119955235378960439066080561)
  ·
    refine ⟨89966426534220329299560421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119955235378960439066080561 89966426534220329299560421)
    ·
      refine ⟨16868704975166311743667579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 89966426534220329299560421 16868704975166311743667579)
      ·
        refine ⟨25303057462749467615501369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16868704975166311743667579 25303057462749467615501369)
        ·
          refine ⟨18977293097062100711626027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25303057462749467615501369 18977293097062100711626027)
          ·
            refine ⟨28465939645593151067439041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18977293097062100711626027 28465939645593151067439041)
            ·
              refine ⟨21349454734194863300579281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28465939645593151067439041 21349454734194863300579281)
              ·
                refine ⟨16012091050646147475434461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21349454734194863300579281 16012091050646147475434461)
                ·
                  refine ⟨6004534143992305303287923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16012091050646147475434461 6004534143992305303287923)
                  ·
                    refine ⟨9006801215988457954931885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6004534143992305303287923 9006801215988457954931885)
                    ·
                      refine ⟨3377550455995671733099457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9006801215988457954931885 3377550455995671733099457)
                      ·
                        rfl

theorem cell23_6577756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 2, 2, 3, 1, 3].length) (baseStart_6577756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6577756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6577756 prefixEnd_6577756 := by exact prefixLift 6577756
  have htrace : WordTrace (prefixWord ++ tailWord_6577756) baseStart_6577756 baseEnd_6577756 := by
    simpa [prefixWord, tailWord_6577756, baseEnd_6577756] using wordTrace_append hprefix tailTrace_6577756
  have hstable : (prefixWord ++ tailWord_6577756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6577756).length < 2 ^ (prefixWord ++ tailWord_6577756).sum := by decide
  have hdescent : baseEnd_6577756 < baseStart_6577756 := by decide
  rcases family_descends (prefixWord ++ tailWord_6577756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6577789 : List Nat := [1, 4, 1, 1, 4, 1, 2, 1, 4, 4]
def baseStart_6577789 : Nat := 118140960795 + 6577789 * 2 ^ 59
def prefixEnd_6577789 : Nat := 4983230072969 + 3 ^ 40 * 6577789 * 2
def baseEnd_6577789 : Nat := 1125855800285756701328935

theorem tailTrace_6577789 : CollatzResearch.WordTrace tailWord_6577789 prefixEnd_6577789 1125855800285756701328935 := by
  unfold tailWord_6577789
  simp only [CollatzResearch.WordTrace]
  refine ⟨239911674366801324768112421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159941116244534216512074947 239911674366801324768112421)
  ·
    refine ⟨44983438943775248394021079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 239911674366801324768112421 44983438943775248394021079)
    ·
      refine ⟨67475158415662872591031619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44983438943775248394021079 67475158415662872591031619)
      ·
        refine ⟨101212737623494308886547429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67475158415662872591031619 101212737623494308886547429)
        ·
          refine ⟨18977388304405182916227643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 101212737623494308886547429 18977388304405182916227643)
          ·
            refine ⟨28466082456607774374341465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18977388304405182916227643 28466082456607774374341465)
            ·
              refine ⟨21349561842455830780756099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28466082456607774374341465 21349561842455830780756099)
              ·
                refine ⟨32024342763683746171134149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21349561842455830780756099 32024342763683746171134149)
                ·
                  refine ⟨6004564268190702407087653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32024342763683746171134149 6004564268190702407087653)
                  ·
                    refine ⟨1125855800285756701328935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6004564268190702407087653 1125855800285756701328935)
                    ·
                      rfl

theorem cell23_6577789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 2, 1, 4, 4].length) (baseStart_6577789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6577789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6577789 prefixEnd_6577789 := by exact prefixLift 6577789
  have htrace : WordTrace (prefixWord ++ tailWord_6577789) baseStart_6577789 baseEnd_6577789 := by
    simpa [prefixWord, tailWord_6577789, baseEnd_6577789] using wordTrace_append hprefix tailTrace_6577789
  have hstable : (prefixWord ++ tailWord_6577789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6577789).length < 2 ^ (prefixWord ++ tailWord_6577789).sum := by decide
  have hdescent : baseEnd_6577789 < baseStart_6577789 := by decide
  rcases family_descends (prefixWord ++ tailWord_6577789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6577802 : List Nat := [3, 1, 2, 3, 2, 1, 1, 10]
def baseStart_6577802 : Nat := 118140960795 + 6577802 * 2 ^ 59
def prefixEnd_6577802 : Nat := 4983230072969 + 3 ^ 40 * 6577802 * 2
def baseEnd_6577802 : Nat := 125095336152065872337935

theorem tailTrace_6577802 : CollatzResearch.WordTrace tailWord_6577802 prefixEnd_6577802 125095336152065872337935 := by
  unfold tailWord_6577802
  simp only [CollatzResearch.WordTrace]
  refine ⟨59978037128938556997083915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 159941432343836151992223773 59978037128938556997083915)
  ·
    refine ⟨89967055693407835495625873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59978037128938556997083915 89967055693407835495625873)
    ·
      refine ⟨67475291770055876621719405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89967055693407835495625873 67475291770055876621719405)
      ·
        refine ⟨25303234413770953733144777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67475291770055876621719405 25303234413770953733144777)
        ·
          refine ⟨18977425810328215299858583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25303234413770953733144777 18977425810328215299858583)
          ·
            refine ⟨28466138715492322949787875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18977425810328215299858583 28466138715492322949787875)
            ·
              refine ⟨42699208073238484424681813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28466138715492322949787875 42699208073238484424681813)
              ·
                refine ⟨125095336152065872337935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 42699208073238484424681813 125095336152065872337935)
                ·
                  rfl

theorem cell23_6577802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 1, 10].length) (baseStart_6577802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6577802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6577802 prefixEnd_6577802 := by exact prefixLift 6577802
  have htrace : WordTrace (prefixWord ++ tailWord_6577802) baseStart_6577802 baseEnd_6577802 := by
    simpa [prefixWord, tailWord_6577802, baseEnd_6577802] using wordTrace_append hprefix tailTrace_6577802
  have hstable : (prefixWord ++ tailWord_6577802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6577802).length < 2 ^ (prefixWord ++ tailWord_6577802).sum := by decide
  have hdescent : baseEnd_6577802 < baseStart_6577802 := by decide
  rcases family_descends (prefixWord ++ tailWord_6577802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6577806 : List Nat := [4, 1, 1, 3, 1, 3, 1, 3, 2, 4]
def baseStart_6577806 : Nat := 118140960795 + 6577806 * 2 ^ 59
def prefixEnd_6577806 : Nat := 4983230072969 + 3 ^ 40 * 6577806 * 2
def baseEnd_6577806 : Nat := 1125858710009465512491409

theorem tailTrace_6577806 : CollatzResearch.WordTrace tailWord_6577806 prefixEnd_6577806 1125858710009465512491409 := by
  unfold tailWord_6577806
  simp only [CollatzResearch.WordTrace]
  refine ⟨29989036800967467083935159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 159941529605159824447654181 29989036800967467083935159)
  ·
    refine ⟨44983555201451200625902739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29989036800967467083935159 44983555201451200625902739)
    ·
      refine ⟨67475332802176800938854109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44983555201451200625902739 67475332802176800938854109)
      ·
        refine ⟨25303249800816300352070291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67475332802176800938854109 25303249800816300352070291)
        ·
          refine ⟨37954874701224450528105437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25303249800816300352070291 37954874701224450528105437)
          ·
            refine ⟨14233078012959168948039539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37954874701224450528105437 14233078012959168948039539)
            ·
              refine ⟨21349617019438753422059309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14233078012959168948039539 21349617019438753422059309)
              ·
                refine ⟨8006106382289532533272241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21349617019438753422059309 8006106382289532533272241)
                ·
                  refine ⟨6004579786717149399954181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8006106382289532533272241 6004579786717149399954181)
                  ·
                    refine ⟨1125858710009465512491409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6004579786717149399954181 1125858710009465512491409)
                    ·
                      rfl

theorem cell23_6577806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 1, 3, 2, 4].length) (baseStart_6577806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6577806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6577806 prefixEnd_6577806 := by exact prefixLift 6577806
  have htrace : WordTrace (prefixWord ++ tailWord_6577806) baseStart_6577806 baseEnd_6577806 := by
    simpa [prefixWord, tailWord_6577806, baseEnd_6577806] using wordTrace_append hprefix tailTrace_6577806
  have hstable : (prefixWord ++ tailWord_6577806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6577806).length < 2 ^ (prefixWord ++ tailWord_6577806).sum := by decide
  have hdescent : baseEnd_6577806 < baseStart_6577806 := by decide
  rcases family_descends (prefixWord ++ tailWord_6577806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6577816 : List Nat := [2, 1, 2, 4, 1, 2, 3, 2, 1, 2, 3]
def baseStart_6577816 : Nat := 118140960795 + 6577816 * 2 ^ 59
def prefixEnd_6577816 : Nat := 4983230072969 + 3 ^ 40 * 6577816 * 2
def baseEnd_6577816 : Nat := 3377581264834941498349181

theorem tailTrace_6577816 : CollatzResearch.WordTrace tailWord_6577816 prefixEnd_6577816 3377581264834941498349181 := by
  unfold tailWord_6577816
  simp only [CollatzResearch.WordTrace]
  refine ⟨119956329568851754189672651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159941772758469005586230201 119956329568851754189672651)
  ·
    refine ⟨179934494353277631284508977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119956329568851754189672651 179934494353277631284508977)
    ·
      refine ⟨134950870764958223463381733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 179934494353277631284508977 134950870764958223463381733)
      ·
        refine ⟨25303288268429666899384075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 134950870764958223463381733 25303288268429666899384075)
        ·
          refine ⟨37954932402644500349076113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25303288268429666899384075 37954932402644500349076113)
          ·
            refine ⟨28466199301983375261807085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37954932402644500349076113 28466199301983375261807085)
            ·
              refine ⟨10674824738243765723177657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28466199301983375261807085 10674824738243765723177657)
              ·
                refine ⟨8006118553682824292383243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10674824738243765723177657 8006118553682824292383243)
                ·
                  refine ⟨12009177830524236438574865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8006118553682824292383243 12009177830524236438574865)
                  ·
                    refine ⟨9006883372893177328931149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12009177830524236438574865 9006883372893177328931149)
                    ·
                      refine ⟨3377581264834941498349181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9006883372893177328931149 3377581264834941498349181)
                      ·
                        rfl

theorem cell23_6577816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 3, 2, 1, 2, 3].length) (baseStart_6577816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6577816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6577816 prefixEnd_6577816 := by exact prefixLift 6577816
  have htrace : WordTrace (prefixWord ++ tailWord_6577816) baseStart_6577816 baseEnd_6577816 := by
    simpa [prefixWord, tailWord_6577816, baseEnd_6577816] using wordTrace_append hprefix tailTrace_6577816
  have hstable : (prefixWord ++ tailWord_6577816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6577816).length < 2 ^ (prefixWord ++ tailWord_6577816).sum := by decide
  have hdescent : baseEnd_6577816 < baseStart_6577816 := by decide
  rcases family_descends (prefixWord ++ tailWord_6577816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6577829 : List Nat := [1, 3, 1, 2, 1, 2, 2, 1, 6, 1, 3]
def baseStart_6577829 : Nat := 118140960795 + 6577829 * 2 ^ 59
def prefixEnd_6577829 : Nat := 4983230072969 + 3 ^ 40 * 6577829 * 2
def baseEnd_6577829 : Nat := 3377587940083449947486621

theorem tailTrace_6577829 : CollatzResearch.WordTrace tailWord_6577829 prefixEnd_6577829 3377587940083449947486621 := by
  unfold tailWord_6577829
  simp only [CollatzResearch.WordTrace]
  refine ⟨239913133286656411599568541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159942088857770941066379027 239913133286656411599568541)
  ·
    refine ⟨89967424982496154349838203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 239913133286656411599568541 89967424982496154349838203)
    ·
      refine ⟨134951137473744231524757305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89967424982496154349838203 134951137473744231524757305)
      ·
        refine ⟨101213353105308173643567979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 134951137473744231524757305 101213353105308173643567979)
        ·
          refine ⟨151820029657962260465351969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101213353105308173643567979 151820029657962260465351969)
          ·
            refine ⟨113865022243471695349013977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 151820029657962260465351969 113865022243471695349013977)
            ·
              refine ⟨85398766682603771511760483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 113865022243471695349013977 85398766682603771511760483)
              ·
                refine ⟨128098150023905657267640725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 85398766682603771511760483 128098150023905657267640725)
                ·
                  refine ⟨6004600782370577684420659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 128098150023905657267640725 6004600782370577684420659)
                  ·
                    refine ⟨9006901173555866526630989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6004600782370577684420659 9006901173555866526630989)
                    ·
                      refine ⟨3377587940083449947486621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9006901173555866526630989 3377587940083449947486621)
                      ·
                        rfl

theorem cell23_6577829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 1, 6, 1, 3].length) (baseStart_6577829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6577829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6577829 prefixEnd_6577829 := by exact prefixLift 6577829
  have htrace : WordTrace (prefixWord ++ tailWord_6577829) baseStart_6577829 baseEnd_6577829 := by
    simpa [prefixWord, tailWord_6577829, baseEnd_6577829] using wordTrace_append hprefix tailTrace_6577829
  have hstable : (prefixWord ++ tailWord_6577829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6577829).length < 2 ^ (prefixWord ++ tailWord_6577829).sum := by decide
  have hdescent : baseEnd_6577829 < baseStart_6577829 := by decide
  rcases family_descends (prefixWord ++ tailWord_6577829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6577842 : List Nat := [3, 2, 1, 1, 1, 2, 2, 2, 2, 2, 5]
def baseStart_6577842 : Nat := 118140960795 + 6577842 * 2 ^ 59
def prefixEnd_6577842 : Nat := 4983230072969 + 3 ^ 40 * 6577842 * 2
def baseEnd_6577842 : Nat := 3377594615331958396624061

theorem tailTrace_6577842 : CollatzResearch.WordTrace tailWord_6577842 prefixEnd_6577842 3377594615331958396624061 := by
  unfold tailWord_6577842
  simp only [CollatzResearch.WordTrace]
  refine ⟨59978401858902328704947945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 159942404957072876546527853 59978401858902328704947945)
  ·
    refine ⟨44983801394176746528710959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59978401858902328704947945 44983801394176746528710959)
    ·
      refine ⟨67475702091265119793066439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44983801394176746528710959 67475702091265119793066439)
      ·
        refine ⟨101213553136897679689599659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67475702091265119793066439 101213553136897679689599659)
        ·
          refine ⟨151820329705346519534399489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101213553136897679689599659 151820329705346519534399489)
          ·
            refine ⟨113865247279009889650799617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 151820329705346519534399489 113865247279009889650799617)
            ·
              refine ⟨85398935459257417238099713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 113865247279009889650799617 85398935459257417238099713)
              ·
                refine ⟨64049201594443062928574785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 85398935459257417238099713 64049201594443062928574785)
                ·
                  refine ⟨48036901195832297196431089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 64049201594443062928574785 48036901195832297196431089)
                  ·
                    refine ⟨36027675896874222897323317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 48036901195832297196431089 36027675896874222897323317)
                    ·
                      refine ⟨3377594615331958396624061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36027675896874222897323317 3377594615331958396624061)
                      ·
                        rfl

theorem cell23_6577842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 2, 2, 2, 5].length) (baseStart_6577842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6577842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6577842 prefixEnd_6577842 := by exact prefixLift 6577842
  have htrace : WordTrace (prefixWord ++ tailWord_6577842) baseStart_6577842 baseEnd_6577842 := by
    simpa [prefixWord, tailWord_6577842, baseEnd_6577842] using wordTrace_append hprefix tailTrace_6577842
  have hstable : (prefixWord ++ tailWord_6577842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6577842).length < 2 ^ (prefixWord ++ tailWord_6577842).sum := by decide
  have hdescent : baseEnd_6577842 < baseStart_6577842 := by decide
  rcases family_descends (prefixWord ++ tailWord_6577842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6577847 : List Nat := [1, 1, 3, 1, 5, 3, 2, 2, 1, 2, 2]
def baseStart_6577847 : Nat := 118140960795 + 6577847 * 2 ^ 59
def prefixEnd_6577847 : Nat := 4983230072969 + 3 ^ 40 * 6577847 * 2
def baseEnd_6577847 : Nat := 3377597182735230877061539

theorem tailTrace_6577847 : CollatzResearch.WordTrace tailWord_6577847 prefixEnd_6577847 3377597182735230877061539 := by
  unfold tailWord_6577847
  simp only [CollatzResearch.WordTrace]
  refine ⟨239913789800591200673723795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159942526533727467115815863 239913789800591200673723795)
  ·
    refine ⟨359870684700886801010585693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 239913789800591200673723795 359870684700886801010585693)
    ·
      refine ⟨134951506762832550378969635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 359870684700886801010585693 134951506762832550378969635)
      ·
        refine ⟨202427260144248825568454453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134951506762832550378969635 202427260144248825568454453)
        ·
          refine ⟨18977555638523327397042605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 202427260144248825568454453 18977555638523327397042605)
          ·
            refine ⟨7116583364446247773890977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18977555638523327397042605 7116583364446247773890977)
            ·
              refine ⟨5337437523334685830418233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7116583364446247773890977 5337437523334685830418233)
              ·
                refine ⟨4003078142501014372813675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5337437523334685830418233 4003078142501014372813675)
                ·
                  refine ⟨6004617213751521559220513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4003078142501014372813675 6004617213751521559220513)
                  ·
                    refine ⟨4503462910313641169415385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6004617213751521559220513 4503462910313641169415385)
                    ·
                      refine ⟨3377597182735230877061539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4503462910313641169415385 3377597182735230877061539)
                      ·
                        rfl

theorem cell23_6577847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 3, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 3, 2, 2, 1, 2, 2].length) (baseStart_6577847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6577847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6577847 prefixEnd_6577847 := by exact prefixLift 6577847
  have htrace : WordTrace (prefixWord ++ tailWord_6577847) baseStart_6577847 baseEnd_6577847 := by
    simpa [prefixWord, tailWord_6577847, baseEnd_6577847] using wordTrace_append hprefix tailTrace_6577847
  have hstable : (prefixWord ++ tailWord_6577847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6577847).length < 2 ^ (prefixWord ++ tailWord_6577847).sum := by decide
  have hdescent : baseEnd_6577847 < baseStart_6577847 := by decide
  rcases family_descends (prefixWord ++ tailWord_6577847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6577872 : List Nat := [2, 1, 1, 1, 1, 2, 1, 6, 2, 1, 5]
def baseStart_6577872 : Nat := 118140960795 + 6577872 * 2 ^ 59
def prefixEnd_6577872 : Nat := 4983230072969 + 3 ^ 40 * 6577872 * 2
def baseEnd_6577872 : Nat := 3377610019751593279248923

theorem tailTrace_6577872 : CollatzResearch.WordTrace tailWord_6577872 prefixEnd_6577872 3377610019751593279248923 := by
  unfold tailWord_6577872
  simp only [CollatzResearch.WordTrace]
  refine ⟨119957350812750314971691935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159943134417000419962255913 119957350812750314971691935)
  ·
    refine ⟨179936026219125472457537903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119957350812750314971691935 179936026219125472457537903)
    ·
      refine ⟨269904039328688208686306855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179936026219125472457537903 269904039328688208686306855)
      ·
        refine ⟨404856058993032313029460283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 269904039328688208686306855 404856058993032313029460283)
        ·
          refine ⟨607284088489548469544190425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 404856058993032313029460283 607284088489548469544190425)
          ·
            refine ⟨455463066367161352158142819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 607284088489548469544190425 455463066367161352158142819)
            ·
              refine ⟨683194599550742028237214229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 455463066367161352158142819 683194599550742028237214229)
              ·
                refine ⟨32024746853941032573619417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 683194599550742028237214229 32024746853941032573619417)
                ·
                  refine ⟨24018560140455774430214563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32024746853941032573619417 24018560140455774430214563)
                  ·
                    refine ⟨36027840210683661645321845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24018560140455774430214563 36027840210683661645321845)
                    ·
                      refine ⟨3377610019751593279248923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36027840210683661645321845 3377610019751593279248923)
                      ·
                        rfl

theorem cell23_6577872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 6, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 6, 2, 1, 5].length) (baseStart_6577872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6577872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6577872 prefixEnd_6577872 := by exact prefixLift 6577872
  have htrace : WordTrace (prefixWord ++ tailWord_6577872) baseStart_6577872 baseEnd_6577872 := by
    simpa [prefixWord, tailWord_6577872, baseEnd_6577872] using wordTrace_append hprefix tailTrace_6577872
  have hstable : (prefixWord ++ tailWord_6577872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6577872).length < 2 ^ (prefixWord ++ tailWord_6577872).sum := by decide
  have hdescent : baseEnd_6577872 < baseStart_6577872 := by decide
  rcases family_descends (prefixWord ++ tailWord_6577872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6577892 : List Nat := [2, 3, 1, 1, 1, 3, 1, 2, 9]
def baseStart_6577892 : Nat := 118140960795 + 6577892 * 2 ^ 59
def prefixEnd_6577892 : Nat := 4983230072969 + 3 ^ 40 * 6577892 * 2
def baseEnd_6577892 : Nat := 375291143262742577888759

theorem tailTrace_6577892 : CollatzResearch.WordTrace tailWord_6577892 prefixEnd_6577892 375291143262742577888759 := by
  unfold tailWord_6577892
  simp only [CollatzResearch.WordTrace]
  refine ⟨119957715542714086679555965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159943620723618782239407953 119957715542714086679555965)
  ·
    refine ⟨44984143328517782504833487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 119957715542714086679555965 44984143328517782504833487)
    ·
      refine ⟨67476214992776673757250231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44984143328517782504833487 67476214992776673757250231)
      ·
        refine ⟨101214322489165010635875347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67476214992776673757250231 101214322489165010635875347)
        ·
          refine ⟨151821483733747515953813021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101214322489165010635875347 151821483733747515953813021)
          ·
            refine ⟨56933056400155318482679883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 151821483733747515953813021 56933056400155318482679883)
            ·
              refine ⟨85399584600232977724019825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56933056400155318482679883 85399584600232977724019825)
              ·
                refine ⟨64049688450174733293014869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 85399584600232977724019825 64049688450174733293014869)
                ·
                  refine ⟨375291143262742577888759, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 64049688450174733293014869 375291143262742577888759)
                  ·
                    rfl

theorem cell23_6577892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 2, 9].length) (baseStart_6577892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6577892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6577892 prefixEnd_6577892 := by exact prefixLift 6577892
  have htrace : WordTrace (prefixWord ++ tailWord_6577892) baseStart_6577892 baseEnd_6577892 := by
    simpa [prefixWord, tailWord_6577892, baseEnd_6577892] using wordTrace_append hprefix tailTrace_6577892
  have hstable : (prefixWord ++ tailWord_6577892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6577892).length < 2 ^ (prefixWord ++ tailWord_6577892).sum := by decide
  have hdescent : baseEnd_6577892 < baseStart_6577892 := by decide
  rcases family_descends (prefixWord ++ tailWord_6577892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6577919 : List Nat := [1, 1, 2, 2, 1, 3, 4, 1, 2, 3, 3]
def baseStart_6577919 : Nat := 118140960795 + 6577919 * 2 ^ 59
def prefixEnd_6577919 : Nat := 4983230072969 + 3 ^ 40 * 6577919 * 2
def baseEnd_6577919 : Nat := 3377634153342354595361207

theorem tailTrace_6577919 : CollatzResearch.WordTrace tailWord_6577919 prefixEnd_6577919 3377634153342354595361207 := by
  unfold tailWord_6577919
  simp only [CollatzResearch.WordTrace]
  refine ⟨239916415856330356970344811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159944277237553571313563207 239916415856330356970344811)
  ·
    refine ⟨359874623784495535455517217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 239916415856330356970344811 359874623784495535455517217)
    ·
      refine ⟨269905967838371651591637913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 359874623784495535455517217 269905967838371651591637913)
      ·
        refine ⟨202429475878778738693728435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 269905967838371651591637913 202429475878778738693728435)
        ·
          refine ⟨303644213818168108040592653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 202429475878778738693728435 303644213818168108040592653)
          ·
            refine ⟨113866580181813040515222245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 303644213818168108040592653 113866580181813040515222245)
            ·
              refine ⟨21349983784089945096604171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 113866580181813040515222245 21349983784089945096604171)
              ·
                refine ⟨32024975676134917644906257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21349983784089945096604171 32024975676134917644906257)
                ·
                  refine ⟨24018731757101188233679693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32024975676134917644906257 24018731757101188233679693)
                  ·
                    refine ⟨9007024408912945587629885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24018731757101188233679693 9007024408912945587629885)
                    ·
                      refine ⟨3377634153342354595361207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9007024408912945587629885 3377634153342354595361207)
                      ·
                        rfl

theorem cell23_6577919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 4, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 4, 1, 2, 3, 3].length) (baseStart_6577919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6577919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6577919 prefixEnd_6577919 := by exact prefixLift 6577919
  have htrace : WordTrace (prefixWord ++ tailWord_6577919) baseStart_6577919 baseEnd_6577919 := by
    simpa [prefixWord, tailWord_6577919, baseEnd_6577919] using wordTrace_append hprefix tailTrace_6577919
  have hstable : (prefixWord ++ tailWord_6577919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6577919).length < 2 ^ (prefixWord ++ tailWord_6577919).sum := by decide
  have hdescent : baseEnd_6577919 < baseStart_6577919 := by decide
  rcases family_descends (prefixWord ++ tailWord_6577919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6577940 : List Nat := [2, 4, 4, 1, 1, 1, 1, 1, 2, 1, 5]
def baseStart_6577940 : Nat := 118140960795 + 6577940 * 2 ^ 59
def prefixEnd_6577940 : Nat := 4983230072969 + 3 ^ 40 * 6577940 * 2
def baseEnd_6577940 : Nat := 3377644936436099013198611

theorem tailTrace_6577940 : CollatzResearch.WordTrace tailWord_6577940 prefixEnd_6577940 3377644936436099013198611 := by
  unfold tailWord_6577940
  simp only [CollatzResearch.WordTrace]
  refine ⟨119958590894627138778429637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159944787859502851704572849 119958590894627138778429637)
  ·
    refine ⟨22492235792742588520955557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 119958590894627138778429637 22492235792742588520955557)
    ·
      refine ⟨4217294211139235347679167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22492235792742588520955557 4217294211139235347679167)
      ·
        refine ⟨6325941316708853021518751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4217294211139235347679167 6325941316708853021518751)
        ·
          refine ⟨9488911975063279532278127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6325941316708853021518751 9488911975063279532278127)
          ·
            refine ⟨14233367962594919298417191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9488911975063279532278127 14233367962594919298417191)
            ·
              refine ⟨21350051943892378947625787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14233367962594919298417191 21350051943892378947625787)
              ·
                refine ⟨32025077915838568421438681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21350051943892378947625787 32025077915838568421438681)
                ·
                  refine ⟨24018808436878926316079011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32025077915838568421438681 24018808436878926316079011)
                  ·
                    refine ⟨36028212655318389474118517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24018808436878926316079011 36028212655318389474118517)
                    ·
                      refine ⟨3377644936436099013198611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36028212655318389474118517 3377644936436099013198611)
                      ·
                        rfl

theorem cell23_6577940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 1, 1, 2, 1, 5].length) (baseStart_6577940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6577940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6577940 prefixEnd_6577940 := by exact prefixLift 6577940
  have htrace : WordTrace (prefixWord ++ tailWord_6577940) baseStart_6577940 baseEnd_6577940 := by
    simpa [prefixWord, tailWord_6577940, baseEnd_6577940] using wordTrace_append hprefix tailTrace_6577940
  have hstable : (prefixWord ++ tailWord_6577940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6577940).length < 2 ^ (prefixWord ++ tailWord_6577940).sum := by decide
  have hdescent : baseEnd_6577940 < baseStart_6577940 := by decide
  rcases family_descends (prefixWord ++ tailWord_6577940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6577943 : List Nat := [1, 1, 3, 4, 2, 3, 1, 3, 5]
def baseStart_6577943 : Nat := 118140960795 + 6577943 * 2 ^ 59
def prefixEnd_6577943 : Nat := 4983230072969 + 3 ^ 40 * 6577943 * 2
def baseEnd_6577943 : Nat := 375294052986451389051233

theorem tailTrace_6577943 : CollatzResearch.WordTrace tailWord_6577943 prefixEnd_6577943 375294052986451389051233 := by
  unfold tailWord_6577943
  simp only [CollatzResearch.WordTrace]
  refine ⟨239917291208243409069218483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159944860805495606046145655 239917291208243409069218483)
  ·
    refine ⟨359875936812365113603827725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 239917291208243409069218483 359875936812365113603827725)
    ·
      refine ⟨134953476304636917601435397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 359875936812365113603827725 134953476304636917601435397)
      ·
        refine ⟨25303776807119422050269137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 134953476304636917601435397 25303776807119422050269137)
        ·
          refine ⟨18977832605339566537701853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25303776807119422050269137 18977832605339566537701853)
          ·
            refine ⟨7116687227002337451638195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18977832605339566537701853 7116687227002337451638195)
            ·
              refine ⟨10675030840503506177457293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7116687227002337451638195 10675030840503506177457293)
              ·
                refine ⟨4003136565188814816546485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10675030840503506177457293 4003136565188814816546485)
                ·
                  refine ⟨375294052986451389051233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4003136565188814816546485 375294052986451389051233)
                  ·
                    rfl

theorem cell23_6577943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 3, 1, 3, 5].length) (baseStart_6577943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6577943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6577943 prefixEnd_6577943 := by exact prefixLift 6577943
  have htrace : WordTrace (prefixWord ++ tailWord_6577943) baseStart_6577943 baseEnd_6577943 := by
    simpa [prefixWord, tailWord_6577943, baseEnd_6577943] using wordTrace_append hprefix tailTrace_6577943
  have hstable : (prefixWord ++ tailWord_6577943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6577943).length < 2 ^ (prefixWord ++ tailWord_6577943).sum := by decide
  have hdescent : baseEnd_6577943 < baseStart_6577943 := by decide
  rcases family_descends (prefixWord ++ tailWord_6577943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6577956 : List Nat := [2, 3, 1, 3, 2, 2, 1, 2, 2, 5]
def baseStart_6577956 : Nat := 118140960795 + 6577956 * 2 ^ 59
def prefixEnd_6577956 : Nat := 4983230072969 + 3 ^ 40 * 6577956 * 2
def baseEnd_6577956 : Nat := 1125884384042190316866179

theorem tailTrace_6577956 : CollatzResearch.WordTrace tailWord_6577956 prefixEnd_6577956 1125884384042190316866179 := by
  unfold tailWord_6577956
  simp only [CollatzResearch.WordTrace]
  refine ⟨119958882678598156144720861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159945176904797541526294481 119958882678598156144720861)
  ·
    refine ⟨44984581004474308554270323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 119958882678598156144720861 44984581004474308554270323)
    ·
      refine ⟨67476871506711462831405485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44984581004474308554270323 67476871506711462831405485)
      ·
        refine ⟨25303826815016798561777057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67476871506711462831405485 25303826815016798561777057)
        ·
          refine ⟨18977870111262598921332793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25303826815016798561777057 18977870111262598921332793)
          ·
            refine ⟨14233402583446949190999595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18977870111262598921332793 14233402583446949190999595)
            ·
              refine ⟨21350103875170423786499393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14233402583446949190999595 21350103875170423786499393)
              ·
                refine ⟨16012577906377817839874545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21350103875170423786499393 16012577906377817839874545)
                ·
                  refine ⟨12009433429783363379905909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16012577906377817839874545 12009433429783363379905909)
                  ·
                    refine ⟨1125884384042190316866179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12009433429783363379905909 1125884384042190316866179)
                    ·
                      rfl

theorem cell23_6577956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 1, 2, 2, 5].length) (baseStart_6577956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6577956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6577956 prefixEnd_6577956 := by exact prefixLift 6577956
  have htrace : WordTrace (prefixWord ++ tailWord_6577956) baseStart_6577956 baseEnd_6577956 := by
    simpa [prefixWord, tailWord_6577956, baseEnd_6577956] using wordTrace_append hprefix tailTrace_6577956
  have hstable : (prefixWord ++ tailWord_6577956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6577956).length < 2 ^ (prefixWord ++ tailWord_6577956).sum := by decide
  have hdescent : baseEnd_6577956 < baseStart_6577956 := by decide
  rcases family_descends (prefixWord ++ tailWord_6577956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6577990 : List Nat := [6, 1, 1, 2, 1, 2, 2, 1, 2, 5]
def baseStart_6577990 : Nat := 118140960795 + 6577990 * 2 ^ 59
def prefixEnd_6577990 : Nat := 4983230072969 + 3 ^ 40 * 6577990 * 2
def baseEnd_6577990 : Nat := 1125890203489607939191127

theorem tailTrace_6577990 : CollatzResearch.WordTrace tailWord_6577990 prefixEnd_6577990 1125890203489607939191127 := by
  unfold tailWord_6577990
  simp only [CollatzResearch.WordTrace]
  refine ⟨7497468919971035503005607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 159946003626048757397452949 7497468919971035503005607)
  ·
    refine ⟨11246203379956553254508411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7497468919971035503005607 11246203379956553254508411)
    ·
      refine ⟨16869305069934829881762617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11246203379956553254508411 16869305069934829881762617)
      ·
        refine ⟨12651978802451122411321963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16869305069934829881762617 12651978802451122411321963)
        ·
          refine ⟨18977968203676683616982945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12651978802451122411321963 18977968203676683616982945)
          ·
            refine ⟨14233476152757512712737209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18977968203676683616982945 14233476152757512712737209)
            ·
              refine ⟨10675107114568134534552907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14233476152757512712737209 10675107114568134534552907)
              ·
                refine ⟨16012660671852201801829361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10675107114568134534552907 16012660671852201801829361)
                ·
                  refine ⟨12009495503889151351372021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16012660671852201801829361 12009495503889151351372021)
                  ·
                    refine ⟨1125890203489607939191127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12009495503889151351372021 1125890203489607939191127)
                    ·
                      rfl

theorem cell23_6577990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 2, 1, 2, 5].length) (baseStart_6577990 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6577990 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6577990 prefixEnd_6577990 := by exact prefixLift 6577990
  have htrace : WordTrace (prefixWord ++ tailWord_6577990) baseStart_6577990 baseEnd_6577990 := by
    simpa [prefixWord, tailWord_6577990, baseEnd_6577990] using wordTrace_append hprefix tailTrace_6577990
  have hstable : (prefixWord ++ tailWord_6577990).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6577990).length < 2 ^ (prefixWord ++ tailWord_6577990).sum := by decide
  have hdescent : baseEnd_6577990 < baseStart_6577990 := by decide
  rcases family_descends (prefixWord ++ tailWord_6577990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6578016 : List Nat := [2, 1, 1, 3, 3, 3, 2, 2, 6]
def baseStart_6578016 : Nat := 118140960795 + 6578016 * 2 ^ 59
def prefixEnd_6578016 : Nat := 4983230072969 + 3 ^ 40 * 6578016 * 2
def baseEnd_6578016 : Nat := 375298217885093412872029

theorem tailTrace_6578016 : CollatzResearch.WordTrace tailWord_6578016 prefixEnd_6578016 375298217885093412872029 := by
  unfold tailWord_6578016
  simp only [CollatzResearch.WordTrace]
  refine ⟨119959976868489471268312951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159946635824652628357750601 119959976868489471268312951)
  ·
    refine ⟨179939965302734206902469427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119959976868489471268312951 179939965302734206902469427)
    ·
      refine ⟨269909947954101310353704141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179939965302734206902469427 269909947954101310353704141)
      ·
        refine ⟨101216230482787991382639053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 269909947954101310353704141 101216230482787991382639053)
        ·
          refine ⟨37956086431045496768489645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 101216230482787991382639053 37956086431045496768489645)
          ·
            refine ⟨14233532411642061288183617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37956086431045496768489645 14233532411642061288183617)
            ·
              refine ⟨10675149308731545966137713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14233532411642061288183617 10675149308731545966137713)
              ·
                refine ⟨8006361981548659474603285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10675149308731545966137713 8006361981548659474603285)
                ·
                  refine ⟨375298217885093412872029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8006361981548659474603285 375298217885093412872029)
                  ·
                    rfl

theorem cell23_6578016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 2, 2, 6].length) (baseStart_6578016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6578016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6578016 prefixEnd_6578016 := by exact prefixLift 6578016
  have htrace : WordTrace (prefixWord ++ tailWord_6578016) baseStart_6578016 baseEnd_6578016 := by
    simpa [prefixWord, tailWord_6578016, baseEnd_6578016] using wordTrace_append hprefix tailTrace_6578016
  have hstable : (prefixWord ++ tailWord_6578016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6578016).length < 2 ^ (prefixWord ++ tailWord_6578016).sum := by decide
  have hdescent : baseEnd_6578016 < baseStart_6578016 := by decide
  rcases family_descends (prefixWord ++ tailWord_6578016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6578020 : List Nat := [2, 3, 1, 1, 5, 1, 1, 4, 1, 4]
def baseStart_6578020 : Nat := 118140960795 + 6578020 * 2 ^ 59
def prefixEnd_6578020 : Nat := 4983230072969 + 3 ^ 40 * 6578020 * 2
def baseEnd_6578020 : Nat := 1125895338296152900066081

theorem tailTrace_6578020 : CollatzResearch.WordTrace tailWord_6578020 prefixEnd_6578020 1125895338296152900066081 := by
  unfold tailWord_6578020
  simp only [CollatzResearch.WordTrace]
  refine ⟨119960049814482225609885757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159946733085976300813181009 119960049814482225609885757)
  ·
    refine ⟨44985018680430834603707159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 119960049814482225609885757 44985018680430834603707159)
    ·
      refine ⟨67477528020646251905560739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44985018680430834603707159 67477528020646251905560739)
      ·
        refine ⟨101216292030969377858341109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67477528020646251905560739 101216292030969377858341109)
        ·
          refine ⟨9489027377903379174219479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 101216292030969377858341109 9489027377903379174219479)
          ·
            refine ⟨14233541066855068761329219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9489027377903379174219479 14233541066855068761329219)
            ·
              refine ⟨21350311600282603141993829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14233541066855068761329219 21350311600282603141993829)
              ·
                refine ⟨4003183425052988089123843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21350311600282603141993829 4003183425052988089123843)
                ·
                  refine ⟨6004775137579482133685765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4003183425052988089123843 6004775137579482133685765)
                  ·
                    refine ⟨1125895338296152900066081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6004775137579482133685765 1125895338296152900066081)
                    ·
                      rfl

theorem cell23_6578020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 1, 4, 1, 4].length) (baseStart_6578020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6578020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6578020 prefixEnd_6578020 := by exact prefixLift 6578020
  have htrace : WordTrace (prefixWord ++ tailWord_6578020) baseStart_6578020 baseEnd_6578020 := by
    simpa [prefixWord, tailWord_6578020, baseEnd_6578020] using wordTrace_append hprefix tailTrace_6578020
  have hstable : (prefixWord ++ tailWord_6578020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6578020).length < 2 ^ (prefixWord ++ tailWord_6578020).sum := by decide
  have hdescent : baseEnd_6578020 < baseStart_6578020 := by decide
  rcases family_descends (prefixWord ++ tailWord_6578020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6578119 : List Nat := [1, 1, 4, 1, 1, 2, 1, 2, 1, 9]
def baseStart_6578119 : Nat := 118140960795 + 6578119 * 2 ^ 59
def prefixEnd_6578119 : Nat := 4983230072969 + 3 ^ 40 * 6578119 * 2
def baseEnd_6578119 : Nat := 1125912283157751270953429

theorem tailTrace_6578119 : CollatzResearch.WordTrace tailWord_6578119 prefixEnd_6578119 1125912283157751270953429 := by
  unfold tailWord_6578119
  simp only [CollatzResearch.WordTrace]
  refine ⟨239923710455605791127625411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159949140303737194085083607 239923710455605791127625411)
  ·
    refine ⟨359885565683408686691438117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 239923710455605791127625411 359885565683408686691438117)
    ·
      refine ⟨67478543565639128754644647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 359885565683408686691438117 67478543565639128754644647)
      ·
        refine ⟨101217815348458693131966971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67478543565639128754644647 101217815348458693131966971)
        ·
          refine ⟨151826723022688039697950457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101217815348458693131966971 151826723022688039697950457)
          ·
            refine ⟨113870042267016029773462843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 151826723022688039697950457 113870042267016029773462843)
            ·
              refine ⟨170805063400524044660194265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 113870042267016029773462843 170805063400524044660194265)
              ·
                refine ⟨128103797550393033495145699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 170805063400524044660194265 128103797550393033495145699)
                ·
                  refine ⟨192155696325589550242718549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 128103797550393033495145699 192155696325589550242718549)
                  ·
                    refine ⟨1125912283157751270953429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 192155696325589550242718549 1125912283157751270953429)
                    ·
                      rfl

theorem cell23_6578119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 2, 1, 9].length) (baseStart_6578119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6578119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6578119 prefixEnd_6578119 := by exact prefixLift 6578119
  have htrace : WordTrace (prefixWord ++ tailWord_6578119) baseStart_6578119 baseEnd_6578119 := by
    simpa [prefixWord, tailWord_6578119, baseEnd_6578119] using wordTrace_append hprefix tailTrace_6578119
  have hstable : (prefixWord ++ tailWord_6578119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6578119).length < 2 ^ (prefixWord ++ tailWord_6578119).sum := by decide
  have hdescent : baseEnd_6578119 < baseStart_6578119 := by decide
  rcases family_descends (prefixWord ++ tailWord_6578119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6578160 : List Nat := [2, 1, 1, 1, 3, 2, 5, 2, 1, 3, 2]
def baseStart_6578160 : Nat := 118140960795 + 6578160 * 2 ^ 59
def prefixEnd_6578160 : Nat := 4983230072969 + 3 ^ 40 * 6578160 * 2
def baseEnd_6578160 : Nat := 3377757902180088152447599

theorem tailTrace_6578160 : CollatzResearch.WordTrace tailWord_6578160 prefixEnd_6578160 3377757902180088152447599 := by
  unfold tailWord_6578160
  simp only [CollatzResearch.WordTrace]
  refine ⟨119962602924228627564933967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159950137232304836753245289 119962602924228627564933967)
  ·
    refine ⟨179943904386342941347400951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119962602924228627564933967 179943904386342941347400951)
    ·
      refine ⟨269915856579514412021101427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179943904386342941347400951 269915856579514412021101427)
      ·
        refine ⟨404873784869271618031652141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 269915856579514412021101427 404873784869271618031652141)
        ·
          refine ⟨151827669325976856761869553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 404873784869271618031652141 151827669325976856761869553)
          ·
            refine ⟨113870751994482642571402165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 151827669325976856761869553 113870751994482642571402165)
            ·
              refine ⟨10675382999482747741068953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 113870751994482642571402165 10675382999482747741068953)
              ·
                refine ⟨8006537249612060805801715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10675382999482747741068953 8006537249612060805801715)
                ·
                  refine ⟨12009805874418091208702573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8006537249612060805801715 12009805874418091208702573)
                  ·
                    refine ⟨4503677202906784203263465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12009805874418091208702573 4503677202906784203263465)
                    ·
                      refine ⟨3377757902180088152447599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4503677202906784203263465 3377757902180088152447599)
                      ·
                        rfl

theorem cell23_6578160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 5, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 5, 2, 1, 3, 2].length) (baseStart_6578160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6578160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6578160 prefixEnd_6578160 := by exact prefixLift 6578160
  have htrace : WordTrace (prefixWord ++ tailWord_6578160) baseStart_6578160 baseEnd_6578160 := by
    simpa [prefixWord, tailWord_6578160, baseEnd_6578160] using wordTrace_append hprefix tailTrace_6578160
  have hstable : (prefixWord ++ tailWord_6578160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6578160).length < 2 ^ (prefixWord ++ tailWord_6578160).sum := by decide
  have hdescent : baseEnd_6578160 < baseStart_6578160 := by decide
  rcases family_descends (prefixWord ++ tailWord_6578160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6578173 : List Nat := [1, 4, 1, 1, 1, 2, 3, 1, 3, 4, 2]
def baseStart_6578173 : Nat := 118140960795 + 6578173 * 2 ^ 59
def prefixEnd_6578173 : Nat := 4983230072969 + 3 ^ 40 * 6578173 * 2
def baseEnd_6578173 : Nat := 3377764577428596601585039

theorem tailTrace_6578173 : CollatzResearch.WordTrace tailWord_6578173 prefixEnd_6578173 3377764577428596601585039 := by
  unfold tailWord_6578173
  simp only [CollatzResearch.WordTrace]
  refine ⟨239925679997410158350091173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159950453331606772233394115 239925679997410158350091173)
  ·
    refine ⟨44986064999514404690642095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 239925679997410158350091173 44986064999514404690642095)
    ·
      refine ⟨67479097499271607035963143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44986064999514404690642095 67479097499271607035963143)
      ·
        refine ⟨101218646248907410553944715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67479097499271607035963143 101218646248907410553944715)
        ·
          refine ⟨151827969373361115830917073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101218646248907410553944715 151827969373361115830917073)
          ·
            refine ⟨113870977030020836873187805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 151827969373361115830917073 113870977030020836873187805)
            ·
              refine ⟨42701616386257813827445427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 113870977030020836873187805 42701616386257813827445427)
              ·
                refine ⟨64052424579386720741168141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42701616386257813827445427 64052424579386720741168141)
                ·
                  refine ⟨24019659217270020277938053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 64052424579386720741168141 24019659217270020277938053)
                  ·
                    refine ⟨4503686103238128802113385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24019659217270020277938053 4503686103238128802113385)
                    ·
                      refine ⟨3377764577428596601585039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4503686103238128802113385 3377764577428596601585039)
                      ·
                        rfl

theorem cell23_6578173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 3, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 3, 1, 3, 4, 2].length) (baseStart_6578173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6578173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6578173 prefixEnd_6578173 := by exact prefixLift 6578173
  have htrace : WordTrace (prefixWord ++ tailWord_6578173) baseStart_6578173 baseEnd_6578173 := by
    simpa [prefixWord, tailWord_6578173, baseEnd_6578173] using wordTrace_append hprefix tailTrace_6578173
  have hstable : (prefixWord ++ tailWord_6578173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6578173).length < 2 ^ (prefixWord ++ tailWord_6578173).sum := by decide
  have hdescent : baseEnd_6578173 < baseStart_6578173 := by decide
  rcases family_descends (prefixWord ++ tailWord_6578173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6578177 : List Nat := [1, 2, 4, 1, 2, 1, 5, 1, 1, 3, 2]
def baseStart_6578177 : Nat := 118140960795 + 6578177 * 2 ^ 59
def prefixEnd_6578177 : Nat := 4983230072969 + 3 ^ 40 * 6578177 * 2
def baseEnd_6578177 : Nat := 3377766631351214585935021

theorem tailTrace_6578177 : CollatzResearch.WordTrace tailWord_6578177 prefixEnd_6578177 3377766631351214585935021 := by
  unfold tailWord_6578177
  simp only [CollatzResearch.WordTrace]
  refine ⟨239925825889395667033236785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159950550592930444688824523 239925825889395667033236785)
  ·
    refine ⟨179944369417046750274927589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 239925825889395667033236785 179944369417046750274927589)
    ·
      refine ⟨33739569265696265676548923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 179944369417046750274927589 33739569265696265676548923)
      ·
        refine ⟨50609353898544398514823385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33739569265696265676548923 50609353898544398514823385)
        ·
          refine ⟨37957015423908298886117539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50609353898544398514823385 37957015423908298886117539)
          ·
            refine ⟨56935523135862448329176309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37957015423908298886117539 56935523135862448329176309)
            ·
              refine ⟨5337705293987104530860279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 56935523135862448329176309 5337705293987104530860279)
              ·
                refine ⟨8006557940980656796290419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5337705293987104530860279 8006557940980656796290419)
                ·
                  refine ⟨12009836911470985194435629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8006557940980656796290419 12009836911470985194435629)
                  ·
                    refine ⟨4503688841801619447913361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12009836911470985194435629 4503688841801619447913361)
                    ·
                      refine ⟨3377766631351214585935021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4503688841801619447913361 3377766631351214585935021)
                      ·
                        rfl

theorem cell23_6578177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 5, 1, 1, 3, 2].length) (baseStart_6578177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6578177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6578177 prefixEnd_6578177 := by exact prefixLift 6578177
  have htrace : WordTrace (prefixWord ++ tailWord_6578177) baseStart_6578177 baseEnd_6578177 := by
    simpa [prefixWord, tailWord_6578177, baseEnd_6578177] using wordTrace_append hprefix tailTrace_6578177
  have hstable : (prefixWord ++ tailWord_6578177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6578177).length < 2 ^ (prefixWord ++ tailWord_6578177).sum := by decide
  have hdescent : baseEnd_6578177 < baseStart_6578177 := by decide
  rcases family_descends (prefixWord ++ tailWord_6578177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6578228 : List Nat := [2, 5, 1, 2, 3, 1, 2, 1, 1, 3, 2]
def baseStart_6578228 : Nat := 118140960795 + 6578228 * 2 ^ 59
def prefixEnd_6578228 : Nat := 4983230072969 + 3 ^ 40 * 6578228 * 2
def baseEnd_6578228 : Nat := 3377792818864593886397287

theorem tailTrace_6578228 : CollatzResearch.WordTrace tailWord_6578228 prefixEnd_6578228 3377792818864593886397287 := by
  unfold tailWord_6578228
  simp only [CollatzResearch.WordTrace]
  refine ⟨119963843006105451371671669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159951790674807268495562225 119963843006105451371671669)
  ·
    refine ⟨11246610281822386066094219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 119963843006105451371671669 11246610281822386066094219)
    ·
      refine ⟨16869915422733579099141329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11246610281822386066094219 16869915422733579099141329)
      ·
        refine ⟨12652436567050184324355997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16869915422733579099141329 12652436567050184324355997)
        ·
          refine ⟨4744663712643819121633499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12652436567050184324355997 4744663712643819121633499)
          ·
            refine ⟨7116995568965728682450249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4744663712643819121633499 7116995568965728682450249)
            ·
              refine ⟨5337746676724296511837687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7116995568965728682450249 5337746676724296511837687)
              ·
                refine ⟨8006620015086444767756531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5337746676724296511837687 8006620015086444767756531)
                ·
                  refine ⟨12009930022629667151634797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8006620015086444767756531 12009930022629667151634797)
                  ·
                    refine ⟨4503723758486125181863049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12009930022629667151634797 4503723758486125181863049)
                    ·
                      refine ⟨3377792818864593886397287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4503723758486125181863049 3377792818864593886397287)
                      ·
                        rfl

theorem cell23_6578228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 3, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 3, 1, 2, 1, 1, 3, 2].length) (baseStart_6578228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6578228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6578228 prefixEnd_6578228 := by exact prefixLift 6578228
  have htrace : WordTrace (prefixWord ++ tailWord_6578228) baseStart_6578228 baseEnd_6578228 := by
    simpa [prefixWord, tailWord_6578228, baseEnd_6578228] using wordTrace_append hprefix tailTrace_6578228
  have hstable : (prefixWord ++ tailWord_6578228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6578228).length < 2 ^ (prefixWord ++ tailWord_6578228).sum := by decide
  have hdescent : baseEnd_6578228 < baseStart_6578228 := by decide
  rcases family_descends (prefixWord ++ tailWord_6578228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6578253 : List Nat := [1, 6, 1, 1, 1, 1, 2, 1, 1, 1, 7]
def baseStart_6578253 : Nat := 118140960795 + 6578253 * 2 ^ 59
def prefixEnd_6578253 : Nat := 4983230072969 + 3 ^ 40 * 6578253 * 2
def baseEnd_6578253 : Nat := 3377805655880956288584671

theorem tailTrace_6578253 : CollatzResearch.WordTrace tailWord_6578253 prefixEnd_6578253 3377805655880956288584671 := by
  unfold tailWord_6578253
  simp only [CollatzResearch.WordTrace]
  refine ⟨239928597837120332013003413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159952398558080221342002275 239928597837120332013003413)
  ·
    refine ⟨11246653023615015563109535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 239928597837120332013003413 11246653023615015563109535)
    ·
      refine ⟨16869979535422523344664303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11246653023615015563109535 16869979535422523344664303)
      ·
        refine ⟨25304969303133785016996455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16869979535422523344664303 25304969303133785016996455)
        ·
          refine ⟨37957453954700677525494683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25304969303133785016996455 37957453954700677525494683)
          ·
            refine ⟨56936180932051016288242025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37957453954700677525494683 56936180932051016288242025)
            ·
              refine ⟨42702135699038262216181519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56936180932051016288242025 42702135699038262216181519)
              ·
                refine ⟨64053203548557393324272279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42702135699038262216181519 64053203548557393324272279)
                ·
                  refine ⟨96079805322836089986408419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 64053203548557393324272279 96079805322836089986408419)
                  ·
                    refine ⟨144119707984254134979612629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 96079805322836089986408419 144119707984254134979612629)
                    ·
                      refine ⟨3377805655880956288584671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 144119707984254134979612629 3377805655880956288584671)
                      ·
                        rfl

theorem cell23_6578253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 2, 1, 1, 1, 7].length) (baseStart_6578253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6578253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6578253 prefixEnd_6578253 := by exact prefixLift 6578253
  have htrace : WordTrace (prefixWord ++ tailWord_6578253) baseStart_6578253 baseEnd_6578253 := by
    simpa [prefixWord, tailWord_6578253, baseEnd_6578253] using wordTrace_append hprefix tailTrace_6578253
  have hstable : (prefixWord ++ tailWord_6578253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6578253).length < 2 ^ (prefixWord ++ tailWord_6578253).sum := by decide
  have hdescent : baseEnd_6578253 < baseStart_6578253 := by decide
  rcases family_descends (prefixWord ++ tailWord_6578253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6578300 : List Nat := [2, 2, 2, 1, 1, 5, 1, 2, 2, 2, 3]
def baseStart_6578300 : Nat := 118140960795 + 6578300 * 2 ^ 59
def prefixEnd_6578300 : Nat := 4983230072969 + 3 ^ 40 * 6578300 * 2
def baseEnd_6578300 : Nat := 3377829789471717604696955

theorem tailTrace_6578300 : CollatzResearch.WordTrace tailWord_6578300 prefixEnd_6578300 3377829789471717604696955 := by
  unfold tailWord_6578300
  simp only [CollatzResearch.WordTrace]
  refine ⟨119965156033975029519982177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159953541378633372693309569 119965156033975029519982177)
  ·
    refine ⟨89973867025481272139986633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119965156033975029519982177 89973867025481272139986633)
    ·
      refine ⟨67480400269110954104989975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89973867025481272139986633 67480400269110954104989975)
      ·
        refine ⟨101220600403666431157484963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67480400269110954104989975 101220600403666431157484963)
        ·
          refine ⟨151830900605499646736227445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101220600403666431157484963 151830900605499646736227445)
          ·
            refine ⟨14234146931765591881521323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 151830900605499646736227445 14234146931765591881521323)
            ·
              refine ⟨21351220397648387822281985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14234146931765591881521323 21351220397648387822281985)
              ·
                refine ⟨16013415298236290866711489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21351220397648387822281985 16013415298236290866711489)
                ·
                  refine ⟨12010061473677218150033617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16013415298236290866711489 12010061473677218150033617)
                  ·
                    refine ⟨9007546105257913612525213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12010061473677218150033617 9007546105257913612525213)
                    ·
                      refine ⟨3377829789471717604696955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9007546105257913612525213 3377829789471717604696955)
                      ·
                        rfl

theorem cell23_6578300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 1, 2, 2, 2, 3].length) (baseStart_6578300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6578300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6578300 prefixEnd_6578300 := by exact prefixLift 6578300
  have htrace : WordTrace (prefixWord ++ tailWord_6578300) baseStart_6578300 baseEnd_6578300 := by
    simpa [prefixWord, tailWord_6578300, baseEnd_6578300] using wordTrace_append hprefix tailTrace_6578300
  have hstable : (prefixWord ++ tailWord_6578300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6578300).length < 2 ^ (prefixWord ++ tailWord_6578300).sum := by decide
  have hdescent : baseEnd_6578300 < baseStart_6578300 := by decide
  rcases family_descends (prefixWord ++ tailWord_6578300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6578316 : List Nat := [2, 2, 1, 2, 1, 1, 1, 1, 1, 11]
def baseStart_6578316 : Nat := 118140960795 + 6578316 * 2 ^ 59
def prefixEnd_6578316 : Nat := 4983230072969 + 3 ^ 40 * 6578316 * 2
def baseEnd_6578316 : Nat := 1125946001720729847365627

theorem tailTrace_6578316 : CollatzResearch.WordTrace tailWord_6578316 prefixEnd_6578316 1125946001720729847365627 := by
  unfold tailWord_6578316
  simp only [CollatzResearch.WordTrace]
  refine ⟨119965447817946046886273401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159953930423928062515031201 119965447817946046886273401)
  ·
    refine ⟨89974085863459535164705051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119965447817946046886273401 89974085863459535164705051)
    ·
      refine ⟨134961128795189302747057577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89974085863459535164705051 134961128795189302747057577)
      ·
        refine ⟨101220846596391977060293183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 134961128795189302747057577 101220846596391977060293183)
        ·
          refine ⟨151831269894587965590439775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101220846596391977060293183 151831269894587965590439775)
          ·
            refine ⟨227746904841881948385659663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 151831269894587965590439775 227746904841881948385659663)
            ·
              refine ⟨341620357262822922578489495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 227746904841881948385659663 341620357262822922578489495)
              ·
                refine ⟨512430535894234383867734243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 341620357262822922578489495 512430535894234383867734243)
                ·
                  refine ⟨768645803841351575801601365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 512430535894234383867734243 768645803841351575801601365)
                  ·
                    refine ⟨1125946001720729847365627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 11 768645803841351575801601365 1125946001720729847365627)
                    ·
                      rfl

theorem cell23_6578316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 1, 1, 11].length) (baseStart_6578316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6578316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6578316 prefixEnd_6578316 := by exact prefixLift 6578316
  have htrace : WordTrace (prefixWord ++ tailWord_6578316) baseStart_6578316 baseEnd_6578316 := by
    simpa [prefixWord, tailWord_6578316, baseEnd_6578316] using wordTrace_append hprefix tailTrace_6578316
  have hstable : (prefixWord ++ tailWord_6578316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6578316).length < 2 ^ (prefixWord ++ tailWord_6578316).sum := by decide
  have hdescent : baseEnd_6578316 < baseStart_6578316 := by decide
  rcases family_descends (prefixWord ++ tailWord_6578316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6578334 : List Nat := [4, 3, 1, 1, 3, 1, 2, 1, 2, 2, 3]
def baseStart_6578334 : Nat := 118140960795 + 6578334 * 2 ^ 59
def prefixEnd_6578334 : Nat := 4983230072969 + 3 ^ 40 * 6578334 * 2
def baseEnd_6578334 : Nat := 3377847247813970471671799

theorem tailTrace_6578334 : CollatzResearch.WordTrace tailWord_6578334 prefixEnd_6578334 3377847247813970471671799 := by
  unfold tailWord_6578334
  simp only [CollatzResearch.WordTrace]
  refine ⟨29991444018728360355837757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 159954368099884588564468037 29991444018728360355837757)
  ·
    refine ⟨11246791507023135133439159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29991444018728360355837757 11246791507023135133439159)
    ·
      refine ⟨16870187260534702700158739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11246791507023135133439159 16870187260534702700158739)
      ·
        refine ⟨25305280890802054050238109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16870187260534702700158739 25305280890802054050238109)
        ·
          refine ⟨9489480334050770268839291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25305280890802054050238109 9489480334050770268839291)
          ·
            refine ⟨14234220501076155403258937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9489480334050770268839291 14234220501076155403258937)
            ·
              refine ⟨10675665375807116552444203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14234220501076155403258937 10675665375807116552444203)
              ·
                refine ⟨16013498063710674828666305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10675665375807116552444203 16013498063710674828666305)
                ·
                  refine ⟨12010123547783006121499729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16013498063710674828666305 12010123547783006121499729)
                  ·
                    refine ⟨9007592660837254591124797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12010123547783006121499729 9007592660837254591124797)
                    ·
                      refine ⟨3377847247813970471671799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9007592660837254591124797 3377847247813970471671799)
                      ·
                        rfl

theorem cell23_6578334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 2, 1, 2, 2, 3].length) (baseStart_6578334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6578334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6578334 prefixEnd_6578334 := by exact prefixLift 6578334
  have htrace : WordTrace (prefixWord ++ tailWord_6578334) baseStart_6578334 baseEnd_6578334 := by
    simpa [prefixWord, tailWord_6578334, baseEnd_6578334] using wordTrace_append hprefix tailTrace_6578334
  have hstable : (prefixWord ++ tailWord_6578334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6578334).length < 2 ^ (prefixWord ++ tailWord_6578334).sum := by decide
  have hdescent : baseEnd_6578334 < baseStart_6578334 := by decide
  rcases family_descends (prefixWord ++ tailWord_6578334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6578373 : List Nat := [1, 3, 1, 1, 1, 1, 4, 4, 1, 1, 5]
def baseStart_6578373 : Nat := 118140960795 + 6578373 * 2 ^ 59
def prefixEnd_6578373 : Nat := 4983230072969 + 3 ^ 40 * 6578373 * 2
def baseEnd_6578373 : Nat := 3377867273559495819084119

theorem tailTrace_6578373 : CollatzResearch.WordTrace tailWord_6578373 prefixEnd_6578373 3377867273559495819084119 := by
  unfold tailWord_6578373
  simp only [CollatzResearch.WordTrace]
  refine ⟨239932974596685592507371773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159955316397790395004914515 239932974596685592507371773)
  ·
    refine ⟨89974865473757097190264415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 239932974596685592507371773 89974865473757097190264415)
    ·
      refine ⟨134962298210635645785396623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89974865473757097190264415 134962298210635645785396623)
      ·
        refine ⟨202443447315953468678094935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134962298210635645785396623 202443447315953468678094935)
        ·
          refine ⟨303665170973930203017142403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 202443447315953468678094935 303665170973930203017142403)
          ·
            refine ⟨455497756460895304525713605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 303665170973930203017142403 455497756460895304525713605)
            ·
              refine ⟨85405829336417869598571301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 455497756460895304525713605 85405829336417869598571301)
              ·
                refine ⟨16013593000578350549732119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 85405829336417869598571301 16013593000578350549732119)
                ·
                  refine ⟨24020389500867525824598179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16013593000578350549732119 24020389500867525824598179)
                  ·
                    refine ⟨36030584251301288736897269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24020389500867525824598179 36030584251301288736897269)
                    ·
                      refine ⟨3377867273559495819084119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36030584251301288736897269 3377867273559495819084119)
                      ·
                        rfl

theorem cell23_6578373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 4, 1, 1, 5].length) (baseStart_6578373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6578373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6578373 prefixEnd_6578373 := by exact prefixLift 6578373
  have htrace : WordTrace (prefixWord ++ tailWord_6578373) baseStart_6578373 baseEnd_6578373 := by
    simpa [prefixWord, tailWord_6578373, baseEnd_6578373] using wordTrace_append hprefix tailTrace_6578373
  have hstable : (prefixWord ++ tailWord_6578373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6578373).length < 2 ^ (prefixWord ++ tailWord_6578373).sum := by decide
  have hdescent : baseEnd_6578373 < baseStart_6578373 := by decide
  rcases family_descends (prefixWord ++ tailWord_6578373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6578434 : List Nat := [3, 4, 1, 1, 2, 3, 1, 1, 1, 2, 4]
def baseStart_6578434 : Nat := 118140960795 + 6578434 * 2 ^ 59
def prefixEnd_6578434 : Nat := 4983230072969 + 3 ^ 40 * 6578434 * 2
def baseEnd_6578434 : Nat := 3377898595879420080421339

theorem tailTrace_6578434 : CollatzResearch.WordTrace tailWord_6578434 prefixEnd_6578434 3377898595879420080421339 := by
  unfold tailWord_6578434
  simp only [CollatzResearch.WordTrace]
  refine ⟨59983799862366149981335589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 159956799632976399950228237 59983799862366149981335589)
  ·
    refine ⟨11246962474193653121500423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 59983799862366149981335589 11246962474193653121500423)
    ·
      refine ⟨16870443711290479682250635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11246962474193653121500423 16870443711290479682250635)
      ·
        refine ⟨25305665566935719523375953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16870443711290479682250635 25305665566935719523375953)
        ·
          refine ⟨18979249175201789642531965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25305665566935719523375953 18979249175201789642531965)
          ·
            refine ⟨7117218440700671115949487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18979249175201789642531965 7117218440700671115949487)
            ·
              refine ⟨10675827661051006673924231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7117218440700671115949487 10675827661051006673924231)
              ·
                refine ⟨16013741491576510010886347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10675827661051006673924231 16013741491576510010886347)
                ·
                  refine ⟨24020612237364765016329521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16013741491576510010886347 24020612237364765016329521)
                  ·
                    refine ⟨18015459178023573762247141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24020612237364765016329521 18015459178023573762247141)
                    ·
                      refine ⟨3377898595879420080421339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18015459178023573762247141 3377898595879420080421339)
                      ·
                        rfl

theorem cell23_6578434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 3, 1, 1, 1, 2, 4].length) (baseStart_6578434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6578434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6578434 prefixEnd_6578434 := by exact prefixLift 6578434
  have htrace : WordTrace (prefixWord ++ tailWord_6578434) baseStart_6578434 baseEnd_6578434 := by
    simpa [prefixWord, tailWord_6578434, baseEnd_6578434] using wordTrace_append hprefix tailTrace_6578434
  have hstable : (prefixWord ++ tailWord_6578434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6578434).length < 2 ^ (prefixWord ++ tailWord_6578434).sum := by decide
  have hdescent : baseEnd_6578434 < baseStart_6578434 := by decide
  rcases family_descends (prefixWord ++ tailWord_6578434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6578453 : List Nat := [1, 3, 2, 1, 2, 1, 2, 2, 1, 8]
def baseStart_6578453 : Nat := 118140960795 + 6578453 * 2 ^ 59
def prefixEnd_6578453 : Nat := 4983230072969 + 3 ^ 40 * 6578453 * 2
def baseEnd_6578453 : Nat := 1125969450670618502027917

theorem tailTrace_6578453 : CollatzResearch.WordTrace tailWord_6578453 prefixEnd_6578453 1125969450670618502027917 := by
  unfold tailWord_6578453
  simp only [CollatzResearch.WordTrace]
  refine ⟨239935892436395766170284013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159957261624263844113522675 239935892436395766170284013)
  ·
    refine ⟨89975959663648412313856505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 239935892436395766170284013 89975959663648412313856505)
    ·
      refine ⟨67481969747736309235392379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89975959663648412313856505 67481969747736309235392379)
      ·
        refine ⟨101222954621604463853088569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67481969747736309235392379 101222954621604463853088569)
        ·
          refine ⟨75917215966203347889816427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101222954621604463853088569 75917215966203347889816427)
          ·
            refine ⟨113875823949305021834724641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75917215966203347889816427 113875823949305021834724641)
            ·
              refine ⟨85406867961978766376043481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 113875823949305021834724641 85406867961978766376043481)
              ·
                refine ⟨64055150971484074782032611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 85406867961978766376043481 64055150971484074782032611)
                ·
                  refine ⟨96082726457226112173048917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 64055150971484074782032611 96082726457226112173048917)
                  ·
                    refine ⟨1125969450670618502027917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 96082726457226112173048917 1125969450670618502027917)
                    ·
                      rfl

theorem cell23_6578453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 2, 1, 8].length) (baseStart_6578453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6578453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6578453 prefixEnd_6578453 := by exact prefixLift 6578453
  have htrace : WordTrace (prefixWord ++ tailWord_6578453) baseStart_6578453 baseEnd_6578453 := by
    simpa [prefixWord, tailWord_6578453, baseEnd_6578453] using wordTrace_append hprefix tailTrace_6578453
  have hstable : (prefixWord ++ tailWord_6578453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6578453).length < 2 ^ (prefixWord ++ tailWord_6578453).sum := by decide
  have hdescent : baseEnd_6578453 < baseStart_6578453 := by decide
  rcases family_descends (prefixWord ++ tailWord_6578453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6578464 : List Nat := [2, 1, 1, 5, 2, 1, 2, 3, 1, 3, 2]
def baseStart_6578464 : Nat := 118140960795 + 6578464 * 2 ^ 59
def prefixEnd_6578464 : Nat := 4983230072969 + 3 ^ 40 * 6578464 * 2
def baseEnd_6578464 : Nat := 3377914000299054963046201

theorem tailTrace_6578464 : CollatzResearch.WordTrace tailWord_6578464 prefixEnd_6578464 3377914000299054963046201 := by
  unfold tailWord_6578464
  simp only [CollatzResearch.WordTrace]
  refine ⟨119968146819677957524467223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159957529092903943365956297 119968146819677957524467223)
  ·
    refine ⟨179952220229516936286700835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119968146819677957524467223 179952220229516936286700835)
    ·
      refine ⟨269928330344275404430051253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179952220229516936286700835 269928330344275404430051253)
      ·
        refine ⟨25305780969775819165317305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 269928330344275404430051253 25305780969775819165317305)
        ·
          refine ⟨18979335727331864373987979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25305780969775819165317305 18979335727331864373987979)
          ·
            refine ⟨28469003590997796560981969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18979335727331864373987979 28469003590997796560981969)
            ·
              refine ⟨21351752693248347420736477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28469003590997796560981969 21351752693248347420736477)
              ·
                refine ⟨8006907259968130282776179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21351752693248347420736477 8006907259968130282776179)
                ·
                  refine ⟨12010360889952195424164269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8006907259968130282776179 12010360889952195424164269)
                  ·
                    refine ⟨4503885333732073284061601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12010360889952195424164269 4503885333732073284061601)
                    ·
                      refine ⟨3377914000299054963046201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4503885333732073284061601 3377914000299054963046201)
                      ·
                        rfl

theorem cell23_6578464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 2, 3, 1, 3, 2].length) (baseStart_6578464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6578464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6578464 prefixEnd_6578464 := by exact prefixLift 6578464
  have htrace : WordTrace (prefixWord ++ tailWord_6578464) baseStart_6578464 baseEnd_6578464 := by
    simpa [prefixWord, tailWord_6578464, baseEnd_6578464] using wordTrace_append hprefix tailTrace_6578464
  have hstable : (prefixWord ++ tailWord_6578464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6578464).length < 2 ^ (prefixWord ++ tailWord_6578464).sum := by decide
  have hdescent : baseEnd_6578464 < baseStart_6578464 := by decide
  rcases family_descends (prefixWord ++ tailWord_6578464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6578510 : List Nat := [4, 1, 1, 1, 1, 1, 2, 1, 3, 5, 3]
def baseStart_6578510 : Nat := 118140960795 + 6578510 * 2 ^ 59
def prefixEnd_6578510 : Nat := 4983230072969 + 3 ^ 40 * 6578510 * 2
def baseEnd_6578510 : Nat := 3377937620409161783070989

theorem tailTrace_6578510 : CollatzResearch.WordTrace tailWord_6578510 prefixEnd_6578510 3377937620409161783070989 := by
  unfold tailWord_6578510
  simp only [CollatzResearch.WordTrace]
  refine ⟨29992246424648658113138623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 159958647598126176603405989 29992246424648658113138623)
  ·
    refine ⟨44988369636972987169707935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29992246424648658113138623 44988369636972987169707935)
    ·
      refine ⟨67482554455459480754561903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44988369636972987169707935 67482554455459480754561903)
      ·
        refine ⟨101223831683189221131842855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67482554455459480754561903 101223831683189221131842855)
        ·
          refine ⟨151835747524783831697764283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101223831683189221131842855 151835747524783831697764283)
          ·
            refine ⟨227753621287175747546646425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 151835747524783831697764283 227753621287175747546646425)
            ·
              refine ⟨170815215965381810659984819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 227753621287175747546646425 170815215965381810659984819)
              ·
                refine ⟨256222823948072715989977229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 170815215965381810659984819 256222823948072715989977229)
                ·
                  refine ⟨96083558980527268496241461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 256222823948072715989977229 96083558980527268496241461)
                  ·
                    refine ⟨9007833654424431421522637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 96083558980527268496241461 9007833654424431421522637)
                    ·
                      refine ⟨3377937620409161783070989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9007833654424431421522637 3377937620409161783070989)
                      ·
                        rfl

theorem cell23_6578510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 1, 3, 5, 3].length) (baseStart_6578510 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6578510 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6578510 prefixEnd_6578510 := by exact prefixLift 6578510
  have htrace : WordTrace (prefixWord ++ tailWord_6578510) baseStart_6578510 baseEnd_6578510 := by
    simpa [prefixWord, tailWord_6578510, baseEnd_6578510] using wordTrace_append hprefix tailTrace_6578510
  have hstable : (prefixWord ++ tailWord_6578510).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6578510).length < 2 ^ (prefixWord ++ tailWord_6578510).sum := by decide
  have hdescent : baseEnd_6578510 < baseStart_6578510 := by decide
  rcases family_descends (prefixWord ++ tailWord_6578510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6578567 : List Nat := [1, 1, 4, 2, 2, 1, 1, 2, 1, 6, 2]
def baseStart_6578567 : Nat := 118140960795 + 6578567 * 2 ^ 59
def prefixEnd_6578567 : Nat := 4983230072969 + 3 ^ 40 * 6578567 * 2
def baseEnd_6578567 : Nat := 3377966888806468060058227

theorem tailTrace_6578567 : CollatzResearch.WordTrace tailWord_6578567 prefixEnd_6578567 3377966888806468060058227 := by
  unfold tailWord_6578567
  simp only [CollatzResearch.WordTrace]
  refine ⟨239940050357982763639933955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159960033571988509093289303 239940050357982763639933955)
  ·
    refine ⟨359910075536974145459900933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 239940050357982763639933955 359910075536974145459900933)
    ·
      refine ⟨67483139163182652273731425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 359910075536974145459900933 67483139163182652273731425)
      ·
        refine ⟨50612354372386989205298569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67483139163182652273731425 50612354372386989205298569)
        ·
          refine ⟨37959265779290241903973927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50612354372386989205298569 37959265779290241903973927)
          ·
            refine ⟨56938898668935362855960891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37959265779290241903973927 56938898668935362855960891)
            ·
              refine ⟨85408348003403044283941337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56938898668935362855960891 85408348003403044283941337)
              ·
                refine ⟨64056261002552283212956003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 85408348003403044283941337 64056261002552283212956003)
                ·
                  refine ⟨96084391503828424819434005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 64056261002552283212956003 96084391503828424819434005)
                  ·
                    refine ⟨4503955851741957413410969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 96084391503828424819434005 4503955851741957413410969)
                    ·
                      refine ⟨3377966888806468060058227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4503955851741957413410969 3377966888806468060058227)
                      ·
                        rfl

theorem cell23_6578567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 2, 1, 6, 2].length) (baseStart_6578567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6578567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6578567 prefixEnd_6578567 := by exact prefixLift 6578567
  have htrace : WordTrace (prefixWord ++ tailWord_6578567) baseStart_6578567 baseEnd_6578567 := by
    simpa [prefixWord, tailWord_6578567, baseEnd_6578567] using wordTrace_append hprefix tailTrace_6578567
  have hstable : (prefixWord ++ tailWord_6578567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6578567).length < 2 ^ (prefixWord ++ tailWord_6578567).sum := by decide
  have hdescent : baseEnd_6578567 < baseStart_6578567 := by decide
  rcases family_descends (prefixWord ++ tailWord_6578567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6578584 : List Nat := [2, 1, 2, 5, 1, 1, 1, 2, 2, 4, 2]
def baseStart_6578584 : Nat := 118140960795 + 6578584 * 2 ^ 59
def prefixEnd_6578584 : Nat := 4983230072969 + 3 ^ 40 * 6578584 * 2
def baseEnd_6578584 : Nat := 3377975617977594493545649

theorem tailTrace_6578584 : CollatzResearch.WordTrace tailWord_6578584 prefixEnd_6578584 3377975617977594493545649 := by
  unfold tailWord_6578584
  simp only [CollatzResearch.WordTrace]
  refine ⟨119970335199460587771651403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159960446932614117028868537 119970335199460587771651403)
  ·
    refine ⟨179955502799190881657477105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119970335199460587771651403 179955502799190881657477105)
    ·
      refine ⟨134966627099393161243107829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 179955502799190881657477105 134966627099393161243107829)
      ·
        refine ⟨12653121290568108866541359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 134966627099393161243107829 12653121290568108866541359)
        ·
          refine ⟨18979681935852163299812039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12653121290568108866541359 18979681935852163299812039)
          ·
            refine ⟨28469522903778244949718059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18979681935852163299812039 28469522903778244949718059)
            ·
              refine ⟨42704284355667367424577089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28469522903778244949718059 42704284355667367424577089)
              ·
                refine ⟨32028213266750525568432817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42704284355667367424577089 32028213266750525568432817)
                ·
                  refine ⟨24021159950062894176324613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32028213266750525568432817 24021159950062894176324613)
                  ·
                    refine ⟨4503967490636792658060865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24021159950062894176324613 4503967490636792658060865)
                    ·
                      refine ⟨3377975617977594493545649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4503967490636792658060865 3377975617977594493545649)
                      ·
                        rfl

theorem cell23_6578584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 1, 2, 2, 4, 2].length) (baseStart_6578584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6578584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6578584 prefixEnd_6578584 := by exact prefixLift 6578584
  have htrace : WordTrace (prefixWord ++ tailWord_6578584) baseStart_6578584 baseEnd_6578584 := by
    simpa [prefixWord, tailWord_6578584, baseEnd_6578584] using wordTrace_append hprefix tailTrace_6578584
  have hstable : (prefixWord ++ tailWord_6578584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6578584).length < 2 ^ (prefixWord ++ tailWord_6578584).sum := by decide
  have hdescent : baseEnd_6578584 < baseStart_6578584 := by decide
  rcases family_descends (prefixWord ++ tailWord_6578584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6578594 : List Nat := [3, 3, 1, 2, 1, 1, 4, 1, 3, 4]
def baseStart_6578594 : Nat := 118140960795 + 6578594 * 2 ^ 59
def prefixEnd_6578594 : Nat := 4983230072969 + 3 ^ 40 * 6578594 * 2
def baseEnd_6578594 : Nat := 1125993584261379818140201

theorem tailTrace_6578594 : CollatzResearch.WordTrace tailWord_6578594 prefixEnd_6578594 1125993584261379818140201 := by
  unfold tailWord_6578594
  simp only [CollatzResearch.WordTrace]
  refine ⟨59985258782221236812791709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 159960690085923298167444557 59985258782221236812791709)
  ·
    refine ⟨22494472043332963804796891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59985258782221236812791709 22494472043332963804796891)
    ·
      refine ⟨33741708064999445707195337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22494472043332963804796891 33741708064999445707195337)
      ·
        refine ⟨25306281048749584280396503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33741708064999445707195337 25306281048749584280396503)
        ·
          refine ⟨37959421573124376420594755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25306281048749584280396503 37959421573124376420594755)
          ·
            refine ⟨56939132359686564630892133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37959421573124376420594755 56939132359686564630892133)
            ·
              refine ⟨10676087317441230868292275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 56939132359686564630892133 10676087317441230868292275)
              ·
                refine ⟨16014130976161846302438413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10676087317441230868292275 16014130976161846302438413)
                ·
                  refine ⟨6005299116060692363414405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16014130976161846302438413 6005299116060692363414405)
                  ·
                    refine ⟨1125993584261379818140201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6005299116060692363414405 1125993584261379818140201)
                    ·
                      rfl

theorem cell23_6578594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 4, 1, 3, 4].length) (baseStart_6578594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6578594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6578594 prefixEnd_6578594 := by exact prefixLift 6578594
  have htrace : WordTrace (prefixWord ++ tailWord_6578594) baseStart_6578594 baseEnd_6578594 := by
    simpa [prefixWord, tailWord_6578594, baseEnd_6578594] using wordTrace_append hprefix tailTrace_6578594
  have hstable : (prefixWord ++ tailWord_6578594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6578594).length < 2 ^ (prefixWord ++ tailWord_6578594).sum := by decide
  have hdescent : baseEnd_6578594 < baseStart_6578594 := by decide
  rcases family_descends (prefixWord ++ tailWord_6578594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6578610 : List Nat := [3, 2, 1, 1, 1, 1, 3, 2, 1, 2, 6]
def baseStart_6578610 : Nat := 118140960795 + 6578610 * 2 ^ 59
def prefixEnd_6578610 : Nat := 4983230072969 + 3 ^ 40 * 6578610 * 2
def baseEnd_6578610 : Nat := 3377988968474611391820529

theorem tailTrace_6578610 : CollatzResearch.WordTrace tailWord_6578610 prefixEnd_6578610 3377988968474611391820529 := by
  unfold tailWord_6578610
  simp only [CollatzResearch.WordTrace]
  refine ⟨59985404674206745495937321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 159961079131217987989166189 59985404674206745495937321)
  ·
    refine ⟨44989053505655059121952991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59985404674206745495937321 44989053505655059121952991)
    ·
      refine ⟨67483580258482588682929487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44989053505655059121952991 67483580258482588682929487)
      ·
        refine ⟨101225370387723883024394231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67483580258482588682929487 101225370387723883024394231)
        ·
          refine ⟨151838055581585824536591347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101225370387723883024394231 151838055581585824536591347)
          ·
            refine ⟨227757083372378736804887021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 151838055581585824536591347 227757083372378736804887021)
            ·
              refine ⟨85408906264642026301832633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 227757083372378736804887021 85408906264642026301832633)
              ·
                refine ⟨64056679698481519726374475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 85408906264642026301832633 64056679698481519726374475)
                ·
                  refine ⟨96085019547722279589561713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 64056679698481519726374475 96085019547722279589561713)
                  ·
                    refine ⟨72063764660791709692171285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 96085019547722279589561713 72063764660791709692171285)
                    ·
                      refine ⟨3377988968474611391820529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 72063764660791709692171285 3377988968474611391820529)
                      ·
                        rfl

theorem cell23_6578610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 2, 1, 2, 6].length) (baseStart_6578610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6578610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6578610 prefixEnd_6578610 := by exact prefixLift 6578610
  have htrace : WordTrace (prefixWord ++ tailWord_6578610) baseStart_6578610 baseEnd_6578610 := by
    simpa [prefixWord, tailWord_6578610, baseEnd_6578610] using wordTrace_append hprefix tailTrace_6578610
  have hstable : (prefixWord ++ tailWord_6578610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6578610).length < 2 ^ (prefixWord ++ tailWord_6578610).sum := by decide
  have hdescent : baseEnd_6578610 < baseStart_6578610 := by decide
  rcases family_descends (prefixWord ++ tailWord_6578610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6578657 : List Nat := [1, 2, 3, 1, 2, 2, 2, 2, 3, 1, 4]
def baseStart_6578657 : Nat := 118140960795 + 6578657 * 2 ^ 59
def prefixEnd_6578657 : Nat := 4983230072969 + 3 ^ 40 * 6578657 * 2
def baseEnd_6578657 : Nat := 3378013102065372707932813

theorem tailTrace_6578657 : CollatzResearch.WordTrace tailWord_6578657 prefixEnd_6578657 3378013102065372707932813 := by
  unfold tailWord_6578657
  simp only [CollatzResearch.WordTrace]
  refine ⟨239943332927656709010710225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159962221951771139340473483 239943332927656709010710225)
  ·
    refine ⟨179957499695742531758032669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 239943332927656709010710225 179957499695742531758032669)
    ·
      refine ⟨67484062385903449409262251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 179957499695742531758032669 67484062385903449409262251)
      ·
        refine ⟨101226093578855174113893377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67484062385903449409262251 101226093578855174113893377)
        ·
          refine ⟨75919570184141380585420033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101226093578855174113893377 75919570184141380585420033)
          ·
            refine ⟨56939677638106035439065025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75919570184141380585420033 56939677638106035439065025)
            ·
              refine ⟨42704758228579526579298769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56939677638106035439065025 42704758228579526579298769)
              ·
                refine ⟨32028568671434644934474077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42704758228579526579298769 32028568671434644934474077)
                ·
                  refine ⟨12010713251787991850427779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32028568671434644934474077 12010713251787991850427779)
                  ·
                    refine ⟨18016069877681987775641669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12010713251787991850427779 18016069877681987775641669)
                    ·
                      refine ⟨3378013102065372707932813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18016069877681987775641669 3378013102065372707932813)
                      ·
                        rfl

theorem cell23_6578657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 2, 2, 3, 1, 4].length) (baseStart_6578657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6578657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6578657 prefixEnd_6578657 := by exact prefixLift 6578657
  have htrace : WordTrace (prefixWord ++ tailWord_6578657) baseStart_6578657 baseEnd_6578657 := by
    simpa [prefixWord, tailWord_6578657, baseEnd_6578657] using wordTrace_append hprefix tailTrace_6578657
  have hstable : (prefixWord ++ tailWord_6578657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6578657).length < 2 ^ (prefixWord ++ tailWord_6578657).sum := by decide
  have hdescent : baseEnd_6578657 < baseStart_6578657 := by decide
  rcases family_descends (prefixWord ++ tailWord_6578657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6578680 : List Nat := [2, 1, 2, 1, 1, 4, 1, 11]
def baseStart_6578680 : Nat := 118140960795 + 6578680 * 2 ^ 59
def prefixEnd_6578680 : Nat := 4983230072969 + 3 ^ 40 * 6578680 * 2
def baseEnd_6578680 : Nat := 125112033782238004368341

theorem tailTrace_6578680 : CollatzResearch.WordTrace tailWord_6578680 prefixEnd_6578680 125112033782238004368341 := by
  unfold tailWord_6578680
  simp only [CollatzResearch.WordTrace]
  refine ⟨119972085903286691969398747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159962781204382255959198329 119972085903286691969398747)
  ·
    refine ⟨179958128854930037954098121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119972085903286691969398747 179958128854930037954098121)
    ·
      refine ⟨134968596641197528465573591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 179958128854930037954098121 134968596641197528465573591)
      ·
        refine ⟨202452894961796292698360387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134968596641197528465573591 202452894961796292698360387)
        ·
          refine ⟨303679342442694439047540581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 202452894961796292698360387 303679342442694439047540581)
          ·
            refine ⟨56939876708005207321413859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 303679342442694439047540581 56939876708005207321413859)
            ·
              refine ⟨85409815062007810982120789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56939876708005207321413859 85409815062007810982120789)
              ·
                refine ⟨125112033782238004368341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 85409815062007810982120789 125112033782238004368341)
                ·
                  rfl

theorem cell23_6578680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 11].length) (baseStart_6578680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6578680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6578680 prefixEnd_6578680 := by exact prefixLift 6578680
  have htrace : WordTrace (prefixWord ++ tailWord_6578680) baseStart_6578680 baseEnd_6578680 := by
    simpa [prefixWord, tailWord_6578680, baseEnd_6578680] using wordTrace_append hprefix tailTrace_6578680
  have hstable : (prefixWord ++ tailWord_6578680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6578680).length < 2 ^ (prefixWord ++ tailWord_6578680).sum := by decide
  have hdescent : baseEnd_6578680 < baseStart_6578680 := by decide
  rcases family_descends (prefixWord ++ tailWord_6578680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6578687 : List Nat := [1, 1, 2, 2, 1, 2, 5, 2, 1, 2, 4]
def baseStart_6578687 : Nat := 118140960795 + 6578687 * 2 ^ 59
def prefixEnd_6578687 : Nat := 4983230072969 + 3 ^ 40 * 6578687 * 2
def baseEnd_6578687 : Nat := 3378028506485007590557675

theorem tailTrace_6578687 : CollatzResearch.WordTrace tailWord_6578687 prefixEnd_6578687 3378028506485007590557675 := by
  unfold tailWord_6578687
  simp only [CollatzResearch.WordTrace]
  refine ⟨239944427117548024134302315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159962951411698682756201543 239944427117548024134302315)
  ·
    refine ⟨359916640676322036201453473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 239944427117548024134302315 359916640676322036201453473)
    ·
      refine ⟨269937480507241527151090105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 359916640676322036201453473 269937480507241527151090105)
      ·
        refine ⟨202453110380431145363317579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 269937480507241527151090105 202453110380431145363317579)
        ·
          refine ⟨303679665570646718044976369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 202453110380431145363317579 303679665570646718044976369)
          ·
            refine ⟨227759749177985038533732277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 303679665570646718044976369 227759749177985038533732277)
            ·
              refine ⟨21352476485436097362537401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 227759749177985038533732277 21352476485436097362537401)
              ·
                refine ⟨16014357364077073021903051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21352476485436097362537401 16014357364077073021903051)
                ·
                  refine ⟨24021536046115609532854577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16014357364077073021903051 24021536046115609532854577)
                  ·
                    refine ⟨18016152034586707149640933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24021536046115609532854577 18016152034586707149640933)
                    ·
                      refine ⟨3378028506485007590557675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18016152034586707149640933 3378028506485007590557675)
                      ·
                        rfl

theorem cell23_6578687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 5, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 5, 2, 1, 2, 4].length) (baseStart_6578687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6578687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6578687 prefixEnd_6578687 := by exact prefixLift 6578687
  have htrace : WordTrace (prefixWord ++ tailWord_6578687) baseStart_6578687 baseEnd_6578687 := by
    simpa [prefixWord, tailWord_6578687, baseEnd_6578687] using wordTrace_append hprefix tailTrace_6578687
  have hstable : (prefixWord ++ tailWord_6578687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6578687).length < 2 ^ (prefixWord ++ tailWord_6578687).sum := by decide
  have hdescent : baseEnd_6578687 < baseStart_6578687 := by decide
  rcases family_descends (prefixWord ++ tailWord_6578687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6578707 : List Nat := [1, 1, 1, 2, 1, 5, 1, 2, 3, 3, 3]
def baseStart_6578707 : Nat := 118140960795 + 6578707 * 2 ^ 59
def prefixEnd_6578707 : Nat := 4983230072969 + 3 ^ 40 * 6578707 * 2
def baseEnd_6578707 : Nat := 3378038776098097512307583

theorem tailTrace_6578707 : CollatzResearch.WordTrace tailWord_6578707 prefixEnd_6578707 3378038776098097512307583 := by
  unfold tailWord_6578707
  simp only [CollatzResearch.WordTrace]
  refine ⟨239945156577475567550030375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159963437718317045033353583 239945156577475567550030375)
  ·
    refine ⟨359917734866213351325045563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 239945156577475567550030375 359917734866213351325045563)
    ·
      refine ⟨539876602299320026987568345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 359917734866213351325045563 539876602299320026987568345)
      ·
        refine ⟨404907451724490020240676259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 539876602299320026987568345 404907451724490020240676259)
        ·
          refine ⟨607361177586735030361014389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 404907451724490020240676259 607361177586735030361014389)
          ·
            refine ⟨56940110398756409096345099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 607361177586735030361014389 56940110398756409096345099)
            ·
              refine ⟨85410165598134613644517649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56940110398756409096345099 85410165598134613644517649)
              ·
                refine ⟨64057624198600960233388237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 85410165598134613644517649 64057624198600960233388237)
                ·
                  refine ⟨24021609074475360087520589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 64057624198600960233388237 24021609074475360087520589)
                  ·
                    refine ⟨9008103402928260032820221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24021609074475360087520589 9008103402928260032820221)
                    ·
                      refine ⟨3378038776098097512307583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9008103402928260032820221 3378038776098097512307583)
                      ·
                        rfl

theorem cell23_6578707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 2, 3, 3, 3].length) (baseStart_6578707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6578707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6578707 prefixEnd_6578707 := by exact prefixLift 6578707
  have htrace : WordTrace (prefixWord ++ tailWord_6578707) baseStart_6578707 baseEnd_6578707 := by
    simpa [prefixWord, tailWord_6578707, baseEnd_6578707] using wordTrace_append hprefix tailTrace_6578707
  have hstable : (prefixWord ++ tailWord_6578707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6578707).length < 2 ^ (prefixWord ++ tailWord_6578707).sum := by decide
  have hdescent : baseEnd_6578707 < baseStart_6578707 := by decide
  rcases family_descends (prefixWord ++ tailWord_6578707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6578742 : List Nat := [5, 1, 2, 1, 2, 2, 2, 3, 1, 2, 2]
def baseStart_6578742 : Nat := 118140960795 + 6578742 * 2 ^ 59
def prefixEnd_6578742 : Nat := 4983230072969 + 3 ^ 40 * 6578742 * 2
def baseEnd_6578742 : Nat := 3378056747921004875369923

theorem tailTrace_6578742 : CollatzResearch.WordTrace tailWord_6578742 prefixEnd_6578742 3378056747921004875369923 := by
  unfold tailWord_6578742
  simp only [CollatzResearch.WordTrace]
  refine ⟨14996652070771798032972155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 159964288754899179018369653 14996652070771798032972155)
  ·
    refine ⟨22494978106157697049458233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14996652070771798032972155 22494978106157697049458233)
    ·
      refine ⟨16871233579618272787093675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22494978106157697049458233 16871233579618272787093675)
      ·
        refine ⟨25306850369427409180640513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16871233579618272787093675 25306850369427409180640513)
        ·
          refine ⟨18980137777070556885480385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25306850369427409180640513 18980137777070556885480385)
          ·
            refine ⟨14235103332802917664110289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18980137777070556885480385 14235103332802917664110289)
            ·
              refine ⟨10676327499602188248082717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14235103332802917664110289 10676327499602188248082717)
              ·
                refine ⟨4003622812350820593031019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10676327499602188248082717 4003622812350820593031019)
                ·
                  refine ⟨6005434218526230889546529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4003622812350820593031019 6005434218526230889546529)
                  ·
                    refine ⟨4504075663894673167159897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6005434218526230889546529 4504075663894673167159897)
                    ·
                      refine ⟨3378056747921004875369923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4504075663894673167159897 3378056747921004875369923)
                      ·
                        rfl

theorem cell23_6578742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 2, 3, 1, 2, 2].length) (baseStart_6578742 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6578742 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6578742 prefixEnd_6578742 := by exact prefixLift 6578742
  have htrace : WordTrace (prefixWord ++ tailWord_6578742) baseStart_6578742 baseEnd_6578742 := by
    simpa [prefixWord, tailWord_6578742, baseEnd_6578742] using wordTrace_append hprefix tailTrace_6578742
  have hstable : (prefixWord ++ tailWord_6578742).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6578742).length < 2 ^ (prefixWord ++ tailWord_6578742).sum := by decide
  have hdescent : baseEnd_6578742 < baseStart_6578742 := by decide
  rcases family_descends (prefixWord ++ tailWord_6578742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6578751 : List Nat := [1, 1, 2, 2, 3, 2, 3, 3, 1, 3, 2]
def baseStart_6578751 : Nat := 118140960795 + 6578751 * 2 ^ 59
def prefixEnd_6578751 : Nat := 4983230072969 + 3 ^ 40 * 6578751 * 2
def baseEnd_6578751 : Nat := 3378061369246895340157381

theorem tailTrace_6578751 : CollatzResearch.WordTrace tailWord_6578751 prefixEnd_6578751 3378061369246895340157381 := by
  unfold tailWord_6578751
  simp only [CollatzResearch.WordTrace]
  refine ⟨239946761389316163064632107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159964507592877442043088071 239946761389316163064632107)
  ·
    refine ⟨359920142083974244596948161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 239946761389316163064632107 359920142083974244596948161)
    ·
      refine ⟨269940106562980683447711121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 359920142083974244596948161 269940106562980683447711121)
      ·
        refine ⟨202455079922235512585783341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 269940106562980683447711121 202455079922235512585783341)
        ·
          refine ⟨75920654970838317219668753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 202455079922235512585783341 75920654970838317219668753)
          ·
            refine ⟨56940491228128737914751565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75920654970838317219668753 56940491228128737914751565)
            ·
              refine ⟨21352684210548276718031837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56940491228128737914751565 21352684210548276718031837)
              ·
                refine ⟨8007256578955603769261939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21352684210548276718031837 8007256578955603769261939)
                ·
                  refine ⟨12010884868433405653892909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8007256578955603769261939 12010884868433405653892909)
                  ·
                    refine ⟨4504081825662527120209841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12010884868433405653892909 4504081825662527120209841)
                    ·
                      refine ⟨3378061369246895340157381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4504081825662527120209841 3378061369246895340157381)
                      ·
                        rfl

theorem cell23_6578751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 3, 3, 1, 3, 2].length) (baseStart_6578751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6578751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6578751 prefixEnd_6578751 := by exact prefixLift 6578751
  have htrace : WordTrace (prefixWord ++ tailWord_6578751) baseStart_6578751 baseEnd_6578751 := by
    simpa [prefixWord, tailWord_6578751, baseEnd_6578751] using wordTrace_append hprefix tailTrace_6578751
  have hstable : (prefixWord ++ tailWord_6578751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6578751).length < 2 ^ (prefixWord ++ tailWord_6578751).sum := by decide
  have hdescent : baseEnd_6578751 < baseStart_6578751 := by decide
  rcases family_descends (prefixWord ++ tailWord_6578751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6578757 : List Nat := [1, 3, 1, 1, 1, 5, 1, 2, 2, 6]
def baseStart_6578757 : Nat := 118140960795 + 6578757 * 2 ^ 59
def prefixEnd_6578757 : Nat := 4983230072969 + 3 ^ 40 * 6578757 * 2
def baseEnd_6578757 : Nat := 1126021483376940772227451

theorem tailTrace_6578757 : CollatzResearch.WordTrace tailWord_6578757 prefixEnd_6578757 1126021483376940772227451 := by
  unfold tailWord_6578757
  simp only [CollatzResearch.WordTrace]
  refine ⟨239946980227294426089350525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159964653484862950726233683 239946980227294426089350525)
  ·
    refine ⟨89980117585235409783506447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 239946980227294426089350525 89980117585235409783506447)
    ·
      refine ⟨134970176377853114675259671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89980117585235409783506447 134970176377853114675259671)
      ·
        refine ⟨202455264566779672012889507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134970176377853114675259671 202455264566779672012889507)
        ·
          refine ⟨303682896850169508019334261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 202455264566779672012889507 303682896850169508019334261)
          ·
            refine ⟨28470271579703391376812587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 303682896850169508019334261 28470271579703391376812587)
            ·
              refine ⟨42705407369555087065218881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28470271579703391376812587 42705407369555087065218881)
              ·
                refine ⟨32029055527166315298914161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42705407369555087065218881 32029055527166315298914161)
                ·
                  refine ⟨24021791645374736474185621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32029055527166315298914161 24021791645374736474185621)
                  ·
                    refine ⟨1126021483376940772227451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24021791645374736474185621 1126021483376940772227451)
                    ·
                      rfl

theorem cell23_6578757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 1, 2, 2, 6].length) (baseStart_6578757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6578757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6578757 prefixEnd_6578757 := by exact prefixLift 6578757
  have htrace : WordTrace (prefixWord ++ tailWord_6578757) baseStart_6578757 baseEnd_6578757 := by
    simpa [prefixWord, tailWord_6578757, baseEnd_6578757] using wordTrace_append hprefix tailTrace_6578757
  have hstable : (prefixWord ++ tailWord_6578757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6578757).length < 2 ^ (prefixWord ++ tailWord_6578757).sum := by decide
  have hdescent : baseEnd_6578757 < baseStart_6578757 := by decide
  rcases family_descends (prefixWord ++ tailWord_6578757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6578767 : List Nat := [1, 1, 2, 1, 1, 2, 4, 1, 1, 6, 3]
def baseStart_6578767 : Nat := 118140960795 + 6578767 * 2 ^ 59
def prefixEnd_6578767 : Nat := 4983230072969 + 3 ^ 40 * 6578767 * 2
def baseEnd_6578767 : Nat := 3378069584937367277557307

theorem tailTrace_6578767 : CollatzResearch.WordTrace tailWord_6578767 prefixEnd_6578767 3378069584937367277557307 := by
  unfold tailWord_6578767
  simp only [CollatzResearch.WordTrace]
  refine ⟨239947344957258197797214555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159964896638172131864809703 239947344957258197797214555)
  ·
    refine ⟨359921017435887296695821833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 239947344957258197797214555 359921017435887296695821833)
    ·
      refine ⟨269940763076915472521866375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 359921017435887296695821833 269940763076915472521866375)
      ·
        refine ⟨404911144615373208782799563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 269940763076915472521866375 404911144615373208782799563)
        ·
          refine ⟨607366716923059813174199345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 404911144615373208782799563 607366716923059813174199345)
          ·
            refine ⟨455525037692294859880649509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 607366716923059813174199345 455525037692294859880649509)
            ·
              refine ⟨85410944567305286227621783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 455525037692294859880649509 85410944567305286227621783)
              ·
                refine ⟨128116416850957929341432675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 85410944567305286227621783 128116416850957929341432675)
                ·
                  refine ⟨192174625276436894012149013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 128116416850957929341432675 192174625276436894012149013)
                  ·
                    refine ⟨9008185559832979406819485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 192174625276436894012149013 9008185559832979406819485)
                    ·
                      refine ⟨3378069584937367277557307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9008185559832979406819485 3378069584937367277557307)
                      ·
                        rfl

theorem cell23_6578767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 1, 1, 6, 3].length) (baseStart_6578767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6578767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6578767 prefixEnd_6578767 := by exact prefixLift 6578767
  have htrace : WordTrace (prefixWord ++ tailWord_6578767) baseStart_6578767 baseEnd_6578767 := by
    simpa [prefixWord, tailWord_6578767, baseEnd_6578767] using wordTrace_append hprefix tailTrace_6578767
  have hstable : (prefixWord ++ tailWord_6578767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6578767).length < 2 ^ (prefixWord ++ tailWord_6578767).sum := by decide
  have hdescent : baseEnd_6578767 < baseStart_6578767 := by decide
  rcases family_descends (prefixWord ++ tailWord_6578767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6578782 : List Nat := [4, 4, 1, 2, 2, 1, 2, 7]
def baseStart_6578782 : Nat := 118140960795 + 6578782 * 2 ^ 59
def prefixEnd_6578782 : Nat := 4983230072969 + 3 ^ 40 * 6578782 * 2
def baseEnd_6578782 : Nat := 125113973598043878476657

theorem tailTrace_6578782 : CollatzResearch.WordTrace tailWord_6578782 prefixEnd_6578782 125113973598043878476657 := by
  unfold tailWord_6578782
  simp only [CollatzResearch.WordTrace]
  refine ⟨29993486506525481919876325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 159965261368135903572673733 29993486506525481919876325)
  ·
    refine ⟨5623778719973527859976811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29993486506525481919876325 5623778719973527859976811)
    ·
      refine ⟨8435668079960291789965217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5623778719973527859976811 8435668079960291789965217)
      ·
        refine ⟨6326751059970218842473913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8435668079960291789965217 6326751059970218842473913)
        ·
          refine ⟨4745063294977664131855435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6326751059970218842473913 4745063294977664131855435)
          ·
            refine ⟨7117594942466496197783153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4745063294977664131855435 7117594942466496197783153)
            ·
              refine ⟨5338196206849872148337365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7117594942466496197783153 5338196206849872148337365)
              ·
                refine ⟨125113973598043878476657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5338196206849872148337365 125113973598043878476657)
                ·
                  rfl

theorem cell23_6578782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 2, 1, 2, 7].length) (baseStart_6578782 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6578782 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6578782 prefixEnd_6578782 := by exact prefixLift 6578782
  have htrace : WordTrace (prefixWord ++ tailWord_6578782) baseStart_6578782 baseEnd_6578782 := by
    simpa [prefixWord, tailWord_6578782, baseEnd_6578782] using wordTrace_append hprefix tailTrace_6578782
  have hstable : (prefixWord ++ tailWord_6578782).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6578782).length < 2 ^ (prefixWord ++ tailWord_6578782).sum := by decide
  have hdescent : baseEnd_6578782 < baseStart_6578782 := by decide
  rcases family_descends (prefixWord ++ tailWord_6578782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6578787 : List Nat := [1, 1, 1, 5, 1, 2, 1, 4, 7]
def baseStart_6578787 : Nat := 118140960795 + 6578787 * 2 ^ 59
def prefixEnd_6578787 : Nat := 4983230072969 + 3 ^ 40 * 6578787 * 2
def baseEnd_6578787 : Nat := 375342206061161911034135

theorem tailTrace_6578787 : CollatzResearch.WordTrace tailWord_6578787 prefixEnd_6578787 375342206061161911034135 := by
  unfold tailWord_6578787
  simp only [CollatzResearch.WordTrace]
  refine ⟨239948074417185741212942615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159965382944790494141961743 239948074417185741212942615)
  ·
    refine ⟨359922111625778611819413923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 239948074417185741212942615 359922111625778611819413923)
    ·
      refine ⟨539883167438667917729120885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 359922111625778611819413923 539883167438667917729120885)
      ·
        refine ⟨50614046947375117287105083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 539883167438667917729120885 50614046947375117287105083)
        ·
          refine ⟨75921070421062675930657625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50614046947375117287105083 75921070421062675930657625)
          ·
            refine ⟨56940802815797006947993219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75921070421062675930657625 56940802815797006947993219)
            ·
              refine ⟨85411204223695510421989829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56940802815797006947993219 85411204223695510421989829)
              ·
                refine ⟨16014600791942908204123093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 85411204223695510421989829 16014600791942908204123093)
                ·
                  refine ⟨375342206061161911034135, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16014600791942908204123093 375342206061161911034135)
                  ·
                    rfl

theorem cell23_6578787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 4, 7].length) (baseStart_6578787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6578787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6578787 prefixEnd_6578787 := by exact prefixLift 6578787
  have htrace : WordTrace (prefixWord ++ tailWord_6578787) baseStart_6578787 baseEnd_6578787 := by
    simpa [prefixWord, tailWord_6578787, baseEnd_6578787] using wordTrace_append hprefix tailTrace_6578787
  have hstable : (prefixWord ++ tailWord_6578787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6578787).length < 2 ^ (prefixWord ++ tailWord_6578787).sum := by decide
  have hdescent : baseEnd_6578787 < baseStart_6578787 := by decide
  rcases family_descends (prefixWord ++ tailWord_6578787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6578798 : List Nat := [4, 1, 2, 2, 2, 1, 1, 2, 4, 2, 2]
def baseStart_6578798 : Nat := 118140960795 + 6578798 * 2 ^ 59
def prefixEnd_6578798 : Nat := 4983230072969 + 3 ^ 40 * 6578798 * 2
def baseEnd_6578798 : Nat := 3378085502837656656269665

theorem tailTrace_6578798 : CollatzResearch.WordTrace tailWord_6578798 prefixEnd_6578798 3378085502837656656269665 := by
  unfold tailWord_6578798
  simp only [CollatzResearch.WordTrace]
  refine ⟨29993559452518236261449131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 159965650413430593394395365 29993559452518236261449131)
  ·
    refine ⟨44990339178777354392173697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29993559452518236261449131 44990339178777354392173697)
    ·
      refine ⟨33742754384083015794130273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44990339178777354392173697 33742754384083015794130273)
      ·
        refine ⟨25307065788062261845597705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33742754384083015794130273 25307065788062261845597705)
        ·
          refine ⟨18980299341046696384198279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25307065788062261845597705 18980299341046696384198279)
          ·
            refine ⟨28470449011570044576297419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18980299341046696384198279 28470449011570044576297419)
            ·
              refine ⟨42705673517355066864446129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28470449011570044576297419 42705673517355066864446129)
              ·
                refine ⟨32029255138016300148334597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42705673517355066864446129 32029255138016300148334597)
                ·
                  refine ⟨6005485338378056277812737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32029255138016300148334597 6005485338378056277812737)
                  ·
                    refine ⟨4504114003783542208359553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6005485338378056277812737 4504114003783542208359553)
                    ·
                      refine ⟨3378085502837656656269665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4504114003783542208359553 3378085502837656656269665)
                      ·
                        rfl

theorem cell23_6578798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 1, 2, 4, 2, 2].length) (baseStart_6578798 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6578798 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6578798 prefixEnd_6578798 := by exact prefixLift 6578798
  have htrace : WordTrace (prefixWord ++ tailWord_6578798) baseStart_6578798 baseEnd_6578798 := by
    simpa [prefixWord, tailWord_6578798, baseEnd_6578798] using wordTrace_append hprefix tailTrace_6578798
  have hstable : (prefixWord ++ tailWord_6578798).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6578798).length < 2 ^ (prefixWord ++ tailWord_6578798).sum := by decide
  have hdescent : baseEnd_6578798 < baseStart_6578798 := by decide
  rcases family_descends (prefixWord ++ tailWord_6578798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6578857 : List Nat := [1, 2, 1, 1, 1, 1, 2, 4, 2, 3, 5]
def baseStart_6578857 : Nat := 118140960795 + 6578857 * 2 ^ 59
def prefixEnd_6578857 : Nat := 4983230072969 + 3 ^ 40 * 6578857 * 2
def baseEnd_6578857 : Nat := 3378115798196271925431893

theorem tailTrace_6578857 : CollatzResearch.WordTrace tailWord_6578857 prefixEnd_6578857 3378115798196271925431893 := by
  unfold tailWord_6578857
  simp only [CollatzResearch.WordTrace]
  refine ⟨239950627526932143167990825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159967085017954762111993883 239950627526932143167990825)
  ·
    refine ⟨179962970645199107375993119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 239950627526932143167990825 179962970645199107375993119)
    ·
      refine ⟨269944455967798661063989679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179962970645199107375993119 269944455967798661063989679)
      ·
        refine ⟨404916683951697991595984519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 269944455967798661063989679 404916683951697991595984519)
        ·
          refine ⟨607375025927546987393976779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 404916683951697991595984519 607375025927546987393976779)
          ·
            refine ⟨911062538891320481090965169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 607375025927546987393976779 911062538891320481090965169)
            ·
              refine ⟨683296904168490360818223877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 911062538891320481090965169 683296904168490360818223877)
              ·
                refine ⟨128118169531591942653416977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 683296904168490360818223877 128118169531591942653416977)
                ·
                  refine ⟨96088627148693956990062733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 128118169531591942653416977 96088627148693956990062733)
                  ·
                    refine ⟨36033235180760233871273525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 96088627148693956990062733 36033235180760233871273525)
                    ·
                      refine ⟨3378115798196271925431893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36033235180760233871273525 3378115798196271925431893)
                      ·
                        rfl

theorem cell23_6578857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 4, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 4, 2, 3, 5].length) (baseStart_6578857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6578857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6578857 prefixEnd_6578857 := by exact prefixLift 6578857
  have htrace : WordTrace (prefixWord ++ tailWord_6578857) baseStart_6578857 baseEnd_6578857 := by
    simpa [prefixWord, tailWord_6578857, baseEnd_6578857] using wordTrace_append hprefix tailTrace_6578857
  have hstable : (prefixWord ++ tailWord_6578857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6578857).length < 2 ^ (prefixWord ++ tailWord_6578857).sum := by decide
  have hdescent : baseEnd_6578857 < baseStart_6578857 := by decide
  rcases family_descends (prefixWord ++ tailWord_6578857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6578898 : List Nat := [3, 2, 2, 2, 3, 1, 1, 2, 3, 4]
def baseStart_6578898 : Nat := 118140960795 + 6578898 * 2 ^ 59
def prefixEnd_6578898 : Nat := 4983230072969 + 3 ^ 40 * 6578898 * 2
def baseEnd_6578898 : Nat := 1126045616967702088339735

theorem tailTrace_6578898 : CollatzResearch.WordTrace tailWord_6578898 prefixEnd_6578898 1126045616967702088339735 := by
  unfold tailWord_6578898
  simp only [CollatzResearch.WordTrace]
  refine ⟨59988030729945901792558337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 159968081946522404780155565 59988030729945901792558337)
  ·
    refine ⟨44991023047459426344418753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59988030729945901792558337 44991023047459426344418753)
    ·
      refine ⟨33743267285594569758314065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44991023047459426344418753 33743267285594569758314065)
      ·
        refine ⟨25307450464195927318735549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33743267285594569758314065 25307450464195927318735549)
        ·
          refine ⟨9490293924073472744525831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25307450464195927318735549 9490293924073472744525831)
          ·
            refine ⟨14235440886110209116788747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9490293924073472744525831 14235440886110209116788747)
            ·
              refine ⟨21353161329165313675183121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14235440886110209116788747 21353161329165313675183121)
              ·
                refine ⟨16014870996873985256387341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21353161329165313675183121 16014870996873985256387341)
                ·
                  refine ⟨6005576623827744471145253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16014870996873985256387341 6005576623827744471145253)
                  ·
                    refine ⟨1126045616967702088339735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6005576623827744471145253 1126045616967702088339735)
                    ·
                      rfl

theorem cell23_6578898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 1, 2, 3, 4].length) (baseStart_6578898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6578898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6578898 prefixEnd_6578898 := by exact prefixLift 6578898
  have htrace : WordTrace (prefixWord ++ tailWord_6578898) baseStart_6578898 baseEnd_6578898 := by
    simpa [prefixWord, tailWord_6578898, baseEnd_6578898] using wordTrace_append hprefix tailTrace_6578898
  have hstable : (prefixWord ++ tailWord_6578898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6578898).length < 2 ^ (prefixWord ++ tailWord_6578898).sum := by decide
  have hdescent : baseEnd_6578898 < baseStart_6578898 := by decide
  rcases family_descends (prefixWord ++ tailWord_6578898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6578907 : List Nat := [1, 1, 1, 1, 1, 1, 1, 3, 4, 9]
def baseStart_6578907 : Nat := 118140960795 + 6578907 * 2 ^ 59
def prefixEnd_6578907 : Nat := 4983230072969 + 3 ^ 40 * 6578907 * 2
def baseEnd_6578907 : Nat := 1126047157409665576602221

theorem tailTrace_6578907 : CollatzResearch.WordTrace tailWord_6578907 prefixEnd_6578907 1126047157409665576602221 := by
  unfold tailWord_6578907
  simp only [CollatzResearch.WordTrace]
  refine ⟨239952451176751001707310975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159968300784500667804873983 239952451176751001707310975)
  ·
    refine ⟨359928676765126502560966463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 239952451176751001707310975 359928676765126502560966463)
    ·
      refine ⟨539893015147689753841449695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 359928676765126502560966463 539893015147689753841449695)
      ·
        refine ⟨809839522721534630762174543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 539893015147689753841449695 809839522721534630762174543)
        ·
          refine ⟨1214759284082301946143261815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 809839522721534630762174543 1214759284082301946143261815)
          ·
            refine ⟨1822138926123452919214892723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1214759284082301946143261815 1822138926123452919214892723)
            ·
              refine ⟨2733208389185179378822339085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1822138926123452919214892723 2733208389185179378822339085)
              ·
                refine ⟨1024953145944442267058377157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2733208389185179378822339085 1024953145944442267058377157)
                ·
                  refine ⟨192178714864582925073445717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1024953145944442267058377157 192178714864582925073445717)
                  ·
                    refine ⟨1126047157409665576602221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 192178714864582925073445717 1126047157409665576602221)
                    ·
                      rfl

theorem cell23_6578907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 9].length) (baseStart_6578907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6578907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6578907 prefixEnd_6578907 := by exact prefixLift 6578907
  have htrace : WordTrace (prefixWord ++ tailWord_6578907) baseStart_6578907 baseEnd_6578907 := by
    simpa [prefixWord, tailWord_6578907, baseEnd_6578907] using wordTrace_append hprefix tailTrace_6578907
  have hstable : (prefixWord ++ tailWord_6578907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6578907).length < 2 ^ (prefixWord ++ tailWord_6578907).sum := by decide
  have hdescent : baseEnd_6578907 < baseStart_6578907 := by decide
  rcases family_descends (prefixWord ++ tailWord_6578907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6578908 : List Nat := [2, 2, 5, 1, 1, 2, 1, 1, 1, 4, 3]
def baseStart_6578908 : Nat := 118140960795 + 6578908 * 2 ^ 59
def prefixEnd_6578908 : Nat := 4983230072969 + 3 ^ 40 * 6578908 * 2
def baseEnd_6578908 : Nat := 3378141985709651225894159

theorem tailTrace_6578908 : CollatzResearch.WordTrace tailWord_6578908 prefixEnd_6578908 3378141985709651225894159 := by
  unfold tailWord_6578908
  simp only [CollatzResearch.WordTrace]
  refine ⟨119976243824873689439048689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159968325099831585918731585 119976243824873689439048689)
  ·
    refine ⟨89982182868655267079286517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119976243824873689439048689 89982182868655267079286517)
    ·
      refine ⟨8435829643936431288683111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 89982182868655267079286517 8435829643936431288683111)
      ·
        refine ⟨12653744465904646933024667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8435829643936431288683111 12653744465904646933024667)
        ·
          refine ⟨18980616698856970399537001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12653744465904646933024667 18980616698856970399537001)
          ·
            refine ⟨14235462524142727799652751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18980616698856970399537001 14235462524142727799652751)
            ·
              refine ⟨21353193786214091699479127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14235462524142727799652751 21353193786214091699479127)
              ·
                refine ⟨32029790679321137549218691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21353193786214091699479127 32029790679321137549218691)
                ·
                  refine ⟨48044686018981706323828037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32029790679321137549218691 48044686018981706323828037)
                  ·
                    refine ⟨9008378628559069935717757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 48044686018981706323828037 9008378628559069935717757)
                    ·
                      refine ⟨3378141985709651225894159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9008378628559069935717757 3378141985709651225894159)
                      ·
                        rfl

theorem cell23_6578908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 1, 1, 1, 4, 3].length) (baseStart_6578908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6578908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6578908 prefixEnd_6578908 := by exact prefixLift 6578908
  have htrace : WordTrace (prefixWord ++ tailWord_6578908) baseStart_6578908 baseEnd_6578908 := by
    simpa [prefixWord, tailWord_6578908, baseEnd_6578908] using wordTrace_append hprefix tailTrace_6578908
  have hstable : (prefixWord ++ tailWord_6578908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6578908).length < 2 ^ (prefixWord ++ tailWord_6578908).sum := by decide
  have hdescent : baseEnd_6578908 < baseStart_6578908 := by decide
  rcases family_descends (prefixWord ++ tailWord_6578908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6578915 : List Nat := [1, 1, 1, 7, 1, 2, 2, 3, 1, 4]
def baseStart_6578915 : Nat := 118140960795 + 6578915 * 2 ^ 59
def prefixEnd_6578915 : Nat := 4983230072969 + 3 ^ 40 * 6578915 * 2
def baseEnd_6578915 : Nat := 1126048526691410899502209

theorem tailTrace_6578915 : CollatzResearch.WordTrace tailWord_6578915 prefixEnd_6578915 1126048526691410899502209 := by
  unfold tailWord_6578915
  simp only [CollatzResearch.WordTrace]
  refine ⟨239952742960722019073602199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159968495307148012715734799 239952742960722019073602199)
  ·
    refine ⟨359929114441083028610403299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 239952742960722019073602199 359929114441083028610403299)
    ·
      refine ⟨539893671661624542915604949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 359929114441083028610403299 539893671661624542915604949)
      ·
        refine ⟨12653757929569325224584491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 539893671661624542915604949 12653757929569325224584491)
        ·
          refine ⟨18980636894353987836876737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12653757929569325224584491 18980636894353987836876737)
          ·
            refine ⟨14235477670765490877657553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18980636894353987836876737 14235477670765490877657553)
            ·
              refine ⟨10676608253074118158243165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14235477670765490877657553 10676608253074118158243165)
              ·
                refine ⟨4003728094902794309341187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10676608253074118158243165 4003728094902794309341187)
                ·
                  refine ⟨6005592142354191464011781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4003728094902794309341187 6005592142354191464011781)
                  ·
                    refine ⟨1126048526691410899502209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6005592142354191464011781 1126048526691410899502209)
                    ·
                      rfl

theorem cell23_6578915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 2, 3, 1, 4].length) (baseStart_6578915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6578915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6578915 prefixEnd_6578915 := by exact prefixLift 6578915
  have htrace : WordTrace (prefixWord ++ tailWord_6578915) baseStart_6578915 baseEnd_6578915 := by
    simpa [prefixWord, tailWord_6578915, baseEnd_6578915] using wordTrace_append hprefix tailTrace_6578915
  have hstable : (prefixWord ++ tailWord_6578915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6578915).length < 2 ^ (prefixWord ++ tailWord_6578915).sum := by decide
  have hdescent : baseEnd_6578915 < baseStart_6578915 := by decide
  rcases family_descends (prefixWord ++ tailWord_6578915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6578931 : List Nat := [1, 1, 1, 2, 2, 3, 1, 3, 4, 3, 2]
def baseStart_6578931 : Nat := 118140960795 + 6578931 * 2 ^ 59
def prefixEnd_6578931 : Nat := 4983230072969 + 3 ^ 40 * 6578931 * 2
def baseEnd_6578931 : Nat := 3378153795764704635906553

theorem tailTrace_6578931 : CollatzResearch.WordTrace tailWord_6578931 prefixEnd_6578931 3378153795764704635906553 := by
  unfold tailWord_6578931
  simp only [CollatzResearch.WordTrace]
  refine ⟨239953326528664053806184647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159968884352442702537456431 239953326528664053806184647)
  ·
    refine ⟨359929989792996080709276971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 239953326528664053806184647 359929989792996080709276971)
    ·
      refine ⟨539894984689494121063915457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 359929989792996080709276971 539894984689494121063915457)
      ·
        refine ⟨404921238517120590797936593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 539894984689494121063915457 404921238517120590797936593)
        ·
          refine ⟨303690928887840443098452445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 404921238517120590797936593 303690928887840443098452445)
          ·
            refine ⟨113884098332940166161919667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 303690928887840443098452445 113884098332940166161919667)
            ·
              refine ⟨170826147499410249242879501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 113884098332940166161919667 170826147499410249242879501)
              ·
                refine ⟨64059805312278843466079813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 170826147499410249242879501 64059805312278843466079813)
                ·
                  refine ⟨12011213496052283149889965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 64059805312278843466079813 12011213496052283149889965)
                  ·
                    refine ⟨4504205061019606181208737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12011213496052283149889965 4504205061019606181208737)
                    ·
                      refine ⟨3378153795764704635906553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4504205061019606181208737 3378153795764704635906553)
                      ·
                        rfl

theorem cell23_6578931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 3, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 3, 4, 3, 2].length) (baseStart_6578931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6578931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6578931 prefixEnd_6578931 := by exact prefixLift 6578931
  have htrace : WordTrace (prefixWord ++ tailWord_6578931) baseStart_6578931 baseEnd_6578931 := by
    simpa [prefixWord, tailWord_6578931, baseEnd_6578931] using wordTrace_append hprefix tailTrace_6578931
  have hstable : (prefixWord ++ tailWord_6578931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6578931).length < 2 ^ (prefixWord ++ tailWord_6578931).sum := by decide
  have hdescent : baseEnd_6578931 < baseStart_6578931 := by decide
  rcases family_descends (prefixWord ++ tailWord_6578931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6578932 : List Nat := [2, 6, 1, 1, 2, 1, 2, 1, 3, 4]
def baseStart_6578932 : Nat := 118140960795 + 6578932 * 2 ^ 59
def prefixEnd_6578932 : Nat := 4983230072969 + 3 ^ 40 * 6578932 * 2
def baseEnd_6578932 : Nat := 1126051436415119710664683

theorem tailTrace_6578932 : CollatzResearch.WordTrace tailWord_6578932 prefixEnd_6578932 1126051436415119710664683 := by
  unfold tailWord_6578932
  simp only [CollatzResearch.WordTrace]
  refine ⟨119976681500830215488485525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159968908667773620651314033 119976681500830215488485525)
  ·
    refine ⟨5623906945351416351022759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 119976681500830215488485525 5623906945351416351022759)
    ·
      refine ⟨8435860418027124526534139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5623906945351416351022759 8435860418027124526534139)
      ·
        refine ⟨12653790627040686789801209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8435860418027124526534139 12653790627040686789801209)
        ·
          refine ⟨9490342970280515092350907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12653790627040686789801209 9490342970280515092350907)
          ·
            refine ⟨14235514455420772638526361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9490342970280515092350907 14235514455420772638526361)
            ·
              refine ⟨10676635841565579478894771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14235514455420772638526361 10676635841565579478894771)
              ·
                refine ⟨16014953762348369218342157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10676635841565579478894771 16014953762348369218342157)
                ·
                  refine ⟨6005607660880638456878309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16014953762348369218342157 6005607660880638456878309)
                  ·
                    refine ⟨1126051436415119710664683, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6005607660880638456878309 1126051436415119710664683)
                    ·
                      rfl

theorem cell23_6578932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 2, 1, 3, 4].length) (baseStart_6578932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6578932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6578932 prefixEnd_6578932 := by exact prefixLift 6578932
  have htrace : WordTrace (prefixWord ++ tailWord_6578932) baseStart_6578932 baseEnd_6578932 := by
    simpa [prefixWord, tailWord_6578932, baseEnd_6578932] using wordTrace_append hprefix tailTrace_6578932
  have hstable : (prefixWord ++ tailWord_6578932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6578932).length < 2 ^ (prefixWord ++ tailWord_6578932).sum := by decide
  have hdescent : baseEnd_6578932 < baseStart_6578932 := by decide
  rcases family_descends (prefixWord ++ tailWord_6578932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6578961 : List Nat := [1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 4]
def baseStart_6578961 : Nat := 118140960795 + 6578961 * 2 ^ 59
def prefixEnd_6578961 : Nat := 4983230072969 + 3 ^ 40 * 6578961 * 2
def baseEnd_6578961 : Nat := 3378169200184339518531415

theorem tailTrace_6578961 : CollatzResearch.WordTrace tailWord_6578961 prefixEnd_6578961 3378169200184339518531415 := by
  unfold tailWord_6578961
  simp only [CollatzResearch.WordTrace]
  refine ⟨239954420718555368929776737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159969613812370245953184491 239954420718555368929776737)
  ·
    refine ⟨179965815538916526697332553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 239954420718555368929776737 179965815538916526697332553)
    ·
      refine ⟨134974361654187395022999415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 179965815538916526697332553 134974361654187395022999415)
      ·
        refine ⟨202461542481281092534499123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134974361654187395022999415 202461542481281092534499123)
        ·
          refine ⟨303692313721921638801748685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 202461542481281092534499123 303692313721921638801748685)
          ·
            refine ⟨113884617645720614550655757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 303692313721921638801748685 113884617645720614550655757)
            ·
              refine ⟨42706731617145230456495909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 113884617645720614550655757 42706731617145230456495909)
              ·
                refine ⟨8007512178214730710592983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 42706731617145230456495909 8007512178214730710592983)
                ·
                  refine ⟨12011268267322096065889475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8007512178214730710592983 12011268267322096065889475)
                  ·
                    refine ⟨18016902400983144098834213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12011268267322096065889475 18016902400983144098834213)
                    ·
                      refine ⟨3378169200184339518531415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18016902400983144098834213 3378169200184339518531415)
                      ·
                        rfl

theorem cell23_6578961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 4].length) (baseStart_6578961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6578961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6578961 prefixEnd_6578961 := by exact prefixLift 6578961
  have htrace : WordTrace (prefixWord ++ tailWord_6578961) baseStart_6578961 baseEnd_6578961 := by
    simpa [prefixWord, tailWord_6578961, baseEnd_6578961] using wordTrace_append hprefix tailTrace_6578961
  have hstable : (prefixWord ++ tailWord_6578961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6578961).length < 2 ^ (prefixWord ++ tailWord_6578961).sum := by decide
  have hdescent : baseEnd_6578961 < baseStart_6578961 := by decide
  rcases family_descends (prefixWord ++ tailWord_6578961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6578972 : List Nat := [2, 2, 3, 1, 1, 5, 1, 3, 1, 1, 3]
def baseStart_6578972 : Nat := 118140960795 + 6578972 * 2 ^ 59
def prefixEnd_6578972 : Nat := 4983230072969 + 3 ^ 40 * 6578972 * 2
def baseEnd_6578972 : Nat := 3378174848471538975493865

theorem tailTrace_6578972 : CollatzResearch.WordTrace tailWord_6578972 prefixEnd_6578972 3378174848471538975493865 := by
  unfold tailWord_6578972
  simp only [CollatzResearch.WordTrace]
  refine ⟨119977410960757758904213585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159969881281010345205618113 119977410960757758904213585)
  ·
    refine ⟨89983058220568319178160189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119977410960757758904213585 89983058220568319178160189)
    ·
      refine ⟨33743646832713119691810071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 89983058220568319178160189 33743646832713119691810071)
      ·
        refine ⟨50615470249069679537715107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33743646832713119691810071 50615470249069679537715107)
        ·
          refine ⟨75923205373604519306572661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50615470249069679537715107 75923205373604519306572661)
          ·
            refine ⟨7117800503775423684991187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 75923205373604519306572661 7117800503775423684991187)
            ·
              refine ⟨10676700755663135527486781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7117800503775423684991187 10676700755663135527486781)
              ·
                refine ⟨4003762783373675822807543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10676700755663135527486781 4003762783373675822807543)
                ·
                  refine ⟨6005644175060513734211315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4003762783373675822807543 6005644175060513734211315)
                  ·
                    refine ⟨9008466262590770601316973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6005644175060513734211315 9008466262590770601316973)
                    ·
                      refine ⟨3378174848471538975493865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9008466262590770601316973 3378174848471538975493865)
                      ·
                        rfl

theorem cell23_6578972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 5, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 5, 1, 3, 1, 1, 3].length) (baseStart_6578972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6578972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6578972 prefixEnd_6578972 := by exact prefixLift 6578972
  have htrace : WordTrace (prefixWord ++ tailWord_6578972) baseStart_6578972 baseEnd_6578972 := by
    simpa [prefixWord, tailWord_6578972, baseEnd_6578972] using wordTrace_append hprefix tailTrace_6578972
  have hstable : (prefixWord ++ tailWord_6578972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6578972).length < 2 ^ (prefixWord ++ tailWord_6578972).sum := by decide
  have hdescent : baseEnd_6578972 < baseStart_6578972 := by decide
  rcases family_descends (prefixWord ++ tailWord_6578972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6578978 : List Nat := [3, 3, 1, 1, 2, 2, 2, 3, 1, 1, 4]
def baseStart_6578978 : Nat := 118140960795 + 6578978 * 2 ^ 59
def prefixEnd_6578978 : Nat := 4983230072969 + 3 ^ 40 * 6578978 * 2
def baseEnd_6578978 : Nat := 3378177929355465952018837

theorem tailTrace_6578978 : CollatzResearch.WordTrace tailWord_6578978 prefixEnd_6578978 3378177929355465952018837 := by
  unfold tailWord_6578978
  simp only [CollatzResearch.WordTrace]
  refine ⟨59988760189873445208286397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 159970027172995853888763725 59988760189873445208286397)
  ·
    refine ⟨22495785071202541953107399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59988760189873445208286397 22495785071202541953107399)
    ·
      refine ⟨33743677606803812929661099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22495785071202541953107399 33743677606803812929661099)
      ·
        refine ⟨50615516410205719394491649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33743677606803812929661099 50615516410205719394491649)
        ·
          refine ⟨37961637307654289545868737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50615516410205719394491649 37961637307654289545868737)
          ·
            refine ⟨28471227980740717159401553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37961637307654289545868737 28471227980740717159401553)
            ·
              refine ⟨21353420985555537869551165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28471227980740717159401553 21353420985555537869551165)
              ·
                refine ⟨8007532869583326701081687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21353420985555537869551165 8007532869583326701081687)
                ·
                  refine ⟨12011299304374990051622531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8007532869583326701081687 12011299304374990051622531)
                  ·
                    refine ⟨18016948956562485077433797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12011299304374990051622531 18016948956562485077433797)
                    ·
                      refine ⟨3378177929355465952018837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18016948956562485077433797 3378177929355465952018837)
                      ·
                        rfl

theorem cell23_6578978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 2, 3, 1, 1, 4].length) (baseStart_6578978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6578978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6578978 prefixEnd_6578978 := by exact prefixLift 6578978
  have htrace : WordTrace (prefixWord ++ tailWord_6578978) baseStart_6578978 baseEnd_6578978 := by
    simpa [prefixWord, tailWord_6578978, baseEnd_6578978] using wordTrace_append hprefix tailTrace_6578978
  have hstable : (prefixWord ++ tailWord_6578978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6578978).length < 2 ^ (prefixWord ++ tailWord_6578978).sum := by decide
  have hdescent : baseEnd_6578978 < baseStart_6578978 := by decide
  rcases family_descends (prefixWord ++ tailWord_6578978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6578981 : List Nat := [1, 3, 1, 2, 3, 1, 4, 1, 1, 1, 5]
def baseStart_6578981 : Nat := 118140960795 + 6578981 * 2 ^ 59
def prefixEnd_6578981 : Nat := 4983230072969 + 3 ^ 40 * 6578981 * 2
def baseEnd_6578981 : Nat := 3378179469797429440281323

theorem tailTrace_6578981 : CollatzResearch.WordTrace tailWord_6578981 prefixEnd_6578981 3378179469797429440281323 := by
  unfold tailWord_6578981
  simp only [CollatzResearch.WordTrace]
  refine ⟨239955150178482912345504797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159970100118988608230336531 239955150178482912345504797)
  ·
    refine ⟨89983181316931092129564299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 239955150178482912345504797 89983181316931092129564299)
    ·
      refine ⟨134974771975396638194346449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89983181316931092129564299 134974771975396638194346449)
      ·
        refine ⟨101231078981547478645759837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 134974771975396638194346449 101231078981547478645759837)
        ·
          refine ⟨37961654618080304492159939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 101231078981547478645759837 37961654618080304492159939)
          ·
            refine ⟨56942481927120456738239909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37961654618080304492159939 56942481927120456738239909)
            ·
              refine ⟨10676715361335085638419983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 56942481927120456738239909 10676715361335085638419983)
              ·
                refine ⟨16015073042002628457629975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10676715361335085638419983 16015073042002628457629975)
                ·
                  refine ⟨24022609563003942686444963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16015073042002628457629975 24022609563003942686444963)
                  ·
                    refine ⟨36033914344505914029667445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24022609563003942686444963 36033914344505914029667445)
                    ·
                      refine ⟨3378179469797429440281323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36033914344505914029667445 3378179469797429440281323)
                      ·
                        rfl

theorem cell23_6578981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 4, 1, 1, 1, 5].length) (baseStart_6578981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6578981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6578981 prefixEnd_6578981 := by exact prefixLift 6578981
  have htrace : WordTrace (prefixWord ++ tailWord_6578981) baseStart_6578981 baseEnd_6578981 := by
    simpa [prefixWord, tailWord_6578981, baseEnd_6578981] using wordTrace_append hprefix tailTrace_6578981
  have hstable : (prefixWord ++ tailWord_6578981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6578981).length < 2 ^ (prefixWord ++ tailWord_6578981).sum := by decide
  have hdescent : baseEnd_6578981 < baseStart_6578981 := by decide
  rcases family_descends (prefixWord ++ tailWord_6578981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6578989 : List Nat := [1, 5, 3, 2, 1, 2, 1, 1, 3, 1, 3]
def baseStart_6578989 : Nat := 118140960795 + 6578989 * 2 ^ 59
def prefixEnd_6578989 : Nat := 4983230072969 + 3 ^ 40 * 6578989 * 2
def baseEnd_6578989 : Nat := 3378183577642665408981287

theorem tailTrace_6578989 : CollatzResearch.WordTrace tailWord_6578989 prefixEnd_6578989 3378183577642665408981287 := by
  unfold tailWord_6578989
  simp only [CollatzResearch.WordTrace]
  refine ⟨239955441962453929711796021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159970294641635953141197347 239955441962453929711796021)
  ·
    refine ⟨22495822683980055910480877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 239955441962453929711796021 22495822683980055910480877)
    ·
      refine ⟨8435933506492520966430329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22495822683980055910480877 8435933506492520966430329)
      ·
        refine ⟨6326950129869390724822747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8435933506492520966430329 6326950129869390724822747)
        ·
          refine ⟨9490425194804086087234121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6326950129869390724822747 9490425194804086087234121)
          ·
            refine ⟨7117818896103064565425591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9490425194804086087234121 7117818896103064565425591)
            ·
              refine ⟨10676728344154596848138387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7117818896103064565425591 10676728344154596848138387)
              ·
                refine ⟨16015092516231895272207581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10676728344154596848138387 16015092516231895272207581)
                ·
                  refine ⟨6005659693586960727077843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16015092516231895272207581 6005659693586960727077843)
                  ·
                    refine ⟨9008489540380441090616765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6005659693586960727077843 9008489540380441090616765)
                    ·
                      refine ⟨3378183577642665408981287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9008489540380441090616765 3378183577642665408981287)
                      ·
                        rfl

theorem cell23_6578989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 2, 1, 1, 3, 1, 3].length) (baseStart_6578989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6578989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6578989 prefixEnd_6578989 := by exact prefixLift 6578989
  have htrace : WordTrace (prefixWord ++ tailWord_6578989) baseStart_6578989 baseEnd_6578989 := by
    simpa [prefixWord, tailWord_6578989, baseEnd_6578989] using wordTrace_append hprefix tailTrace_6578989
  have hstable : (prefixWord ++ tailWord_6578989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6578989).length < 2 ^ (prefixWord ++ tailWord_6578989).sum := by decide
  have hdescent : baseEnd_6578989 < baseStart_6578989 := by decide
  rcases family_descends (prefixWord ++ tailWord_6578989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6578995 : List Nat := [1, 1, 1, 2, 6, 1, 3, 1, 3, 2, 2]
def baseStart_6578995 : Nat := 118140960795 + 6578995 * 2 ^ 59
def prefixEnd_6578995 : Nat := 4983230072969 + 3 ^ 40 * 6578995 * 2
def baseEnd_6578995 : Nat := 3378186658526592385506259

theorem tailTrace_6578995 : CollatzResearch.WordTrace tailWord_6578995 prefixEnd_6578995 3378186658526592385506259 := by
  unfold tailWord_6578995
  simp only [CollatzResearch.WordTrace]
  refine ⟨239955660800432192736514439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159970440533621461824342959 239955660800432192736514439)
  ·
    refine ⟨359933491200648289104771659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 239955660800432192736514439 359933491200648289104771659)
    ·
      refine ⟨539900236800972433657157489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 359933491200648289104771659 539900236800972433657157489)
      ·
        refine ⟨404925177600729325242868117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 539900236800972433657157489 404925177600729325242868117)
        ·
          refine ⟨18980867700034187120759443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 404925177600729325242868117 18980867700034187120759443)
          ·
            refine ⟨28471301550051280681139165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18980867700034187120759443 28471301550051280681139165)
            ·
              refine ⟨10676738081269230255427187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28471301550051280681139165 10676738081269230255427187)
              ·
                refine ⟨16015107121903845383140781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10676738081269230255427187 16015107121903845383140781)
                ·
                  refine ⟨6005665170713942018677793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16015107121903845383140781 6005665170713942018677793)
                  ·
                    refine ⟨4504248878035456514008345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6005665170713942018677793 4504248878035456514008345)
                    ·
                      refine ⟨3378186658526592385506259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4504248878035456514008345 3378186658526592385506259)
                      ·
                        rfl

theorem cell23_6578995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 3, 1, 3, 2, 2].length) (baseStart_6578995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6578995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6578995 prefixEnd_6578995 := by exact prefixLift 6578995
  have htrace : WordTrace (prefixWord ++ tailWord_6578995) baseStart_6578995 baseEnd_6578995 := by
    simpa [prefixWord, tailWord_6578995, baseEnd_6578995] using wordTrace_append hprefix tailTrace_6578995
  have hstable : (prefixWord ++ tailWord_6578995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6578995).length < 2 ^ (prefixWord ++ tailWord_6578995).sum := by decide
  have hdescent : baseEnd_6578995 < baseStart_6578995 := by decide
  rcases family_descends (prefixWord ++ tailWord_6578995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6579004 : List Nat := [2, 2, 2, 2, 1, 1, 1, 1, 1, 4, 6]
def baseStart_6579004 : Nat := 118140960795 + 6579004 * 2 ^ 59
def prefixEnd_6579004 : Nat := 4983230072969 + 3 ^ 40 * 6579004 * 2
def baseEnd_6579004 : Nat := 3378191279852482850293717

theorem tailTrace_6579004 : CollatzResearch.WordTrace tailWord_6579004 prefixEnd_6579004 3378191279852482850293717 := by
  unfold tailWord_6579004
  simp only [CollatzResearch.WordTrace]
  refine ⟨119977994528699793636796033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159970659371599724849061377 119977994528699793636796033)
  ·
    refine ⟨89983495896524845227597025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119977994528699793636796033 89983495896524845227597025)
    ·
      refine ⟨67487621922393633920697769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89983495896524845227597025 67487621922393633920697769)
      ·
        refine ⟨50615716441795225440523327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67487621922393633920697769 50615716441795225440523327)
        ·
          refine ⟨75923574662692838160784991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50615716441795225440523327 75923574662692838160784991)
          ·
            refine ⟨113885361994039257241177487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75923574662692838160784991 113885361994039257241177487)
            ·
              refine ⟨170828042991058885861766231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 113885361994039257241177487 170828042991058885861766231)
              ·
                refine ⟨256242064486588328792649347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 170828042991058885861766231 256242064486588328792649347)
                ·
                  refine ⟨384363096729882493188974021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 256242064486588328792649347 384363096729882493188974021)
                  ·
                    refine ⟨72068080636852967472932629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 384363096729882493188974021 72068080636852967472932629)
                    ·
                      refine ⟨3378191279852482850293717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 72068080636852967472932629 3378191279852482850293717)
                      ·
                        rfl

theorem cell23_6579004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 1, 1, 4, 6].length) (baseStart_6579004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6579004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6579004 prefixEnd_6579004 := by exact prefixLift 6579004
  have htrace : WordTrace (prefixWord ++ tailWord_6579004) baseStart_6579004 baseEnd_6579004 := by
    simpa [prefixWord, tailWord_6579004, baseEnd_6579004] using wordTrace_append hprefix tailTrace_6579004
  have hstable : (prefixWord ++ tailWord_6579004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6579004).length < 2 ^ (prefixWord ++ tailWord_6579004).sum := by decide
  have hdescent : baseEnd_6579004 < baseStart_6579004 := by decide
  rcases family_descends (prefixWord ++ tailWord_6579004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6579005 : List Nat := [1, 4, 1, 4, 2, 1, 1, 3, 2, 4]
def baseStart_6579005 : Nat := 118140960795 + 6579005 * 2 ^ 59
def prefixEnd_6579005 : Nat := 4983230072969 + 3 ^ 40 * 6579005 * 2
def baseEnd_6579005 : Nat := 1126063931111045782127071

theorem tailTrace_6579005 : CollatzResearch.WordTrace tailWord_6579005 prefixEnd_6579005 1126063931111045782127071 := by
  unfold tailWord_6579005
  simp only [CollatzResearch.WordTrace]
  refine ⟨239956025530395964444378469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159970683686930642962918979 239956025530395964444378469)
  ·
    refine ⟨44991754786949243333320963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 239956025530395964444378469 44991754786949243333320963)
    ·
      refine ⟨67487632180423864999981445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44991754786949243333320963 67487632180423864999981445)
      ·
        refine ⟨12653931033829474687496521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 67487632180423864999981445 12653931033829474687496521)
        ·
          refine ⟨9490448275372106015622391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12653931033829474687496521 9490448275372106015622391)
          ·
            refine ⟨14235672413058159023433587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9490448275372106015622391 14235672413058159023433587)
            ·
              refine ⟨21353508619587238535150381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14235672413058159023433587 21353508619587238535150381)
              ·
                refine ⟨8007565732345214450681393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21353508619587238535150381 8007565732345214450681393)
                ·
                  refine ⟨6005674299258910838011045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8007565732345214450681393 6005674299258910838011045)
                  ·
                    refine ⟨1126063931111045782127071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6005674299258910838011045 1126063931111045782127071)
                    ·
                      rfl

theorem cell23_6579005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 1, 3, 2, 4].length) (baseStart_6579005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6579005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6579005 prefixEnd_6579005 := by exact prefixLift 6579005
  have htrace : WordTrace (prefixWord ++ tailWord_6579005) baseStart_6579005 baseEnd_6579005 := by
    simpa [prefixWord, tailWord_6579005, baseEnd_6579005] using wordTrace_append hprefix tailTrace_6579005
  have hstable : (prefixWord ++ tailWord_6579005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6579005).length < 2 ^ (prefixWord ++ tailWord_6579005).sum := by decide
  have hdescent : baseEnd_6579005 < baseStart_6579005 := by decide
  rcases family_descends (prefixWord ++ tailWord_6579005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6579011 : List Nat := [1, 1, 1, 3, 1, 4, 2, 3, 1, 3, 3]
def baseStart_6579011 : Nat := 118140960795 + 6579011 * 2 ^ 59
def prefixEnd_6579011 : Nat := 4983230072969 + 3 ^ 40 * 6579011 * 2
def baseEnd_6579011 : Nat := 3378194874217064322906185

theorem tailTrace_6579011 : CollatzResearch.WordTrace tailWord_6579011 prefixEnd_6579011 3378194874217064322906185 := by
  unfold tailWord_6579011
  simp only [CollatzResearch.WordTrace]
  refine ⟨239956244368374227469096887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159970829578916151646064591 239956244368374227469096887)
  ·
    refine ⟨359934366552561341203645331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 239956244368374227469096887 359934366552561341203645331)
    ·
      refine ⟨539901549828842011805467997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 359934366552561341203645331 539901549828842011805467997)
      ·
        refine ⟨202463081185815754427050499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 539901549828842011805467997 202463081185815754427050499)
        ·
          refine ⟨303694621778723631640575749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 202463081185815754427050499 303694621778723631640575749)
          ·
            refine ⟨56942741583510680932607953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 303694621778723631640575749 56942741583510680932607953)
            ·
              refine ⟨42707056187633010699455965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56942741583510680932607953 42707056187633010699455965)
              ·
                refine ⟨16015146070362379012295987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42707056187633010699455965 16015146070362379012295987)
                ·
                  refine ⟨24022719105543568518443981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16015146070362379012295987 24022719105543568518443981)
                  ·
                    refine ⟨9008519664578838194416493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24022719105543568518443981 9008519664578838194416493)
                    ·
                      refine ⟨3378194874217064322906185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9008519664578838194416493 3378194874217064322906185)
                      ·
                        rfl

theorem cell23_6579011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 2, 3, 1, 3, 3].length) (baseStart_6579011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6579011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6579011 prefixEnd_6579011 := by exact prefixLift 6579011
  have htrace : WordTrace (prefixWord ++ tailWord_6579011) baseStart_6579011 baseEnd_6579011 := by
    simpa [prefixWord, tailWord_6579011, baseEnd_6579011] using wordTrace_append hprefix tailTrace_6579011
  have hstable : (prefixWord ++ tailWord_6579011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6579011).length < 2 ^ (prefixWord ++ tailWord_6579011).sum := by decide
  have hdescent : baseEnd_6579011 < baseStart_6579011 := by decide
  rcases family_descends (prefixWord ++ tailWord_6579011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6579024 : List Nat := [2, 1, 1, 1, 1, 4, 2, 1, 1, 4, 5]
def baseStart_6579024 : Nat := 118140960795 + 6579024 * 2 ^ 59
def prefixEnd_6579024 : Nat := 4983230072969 + 3 ^ 40 * 6579024 * 2
def baseEnd_6579024 : Nat := 3378201549465572772043625

theorem tailTrace_6579024 : CollatzResearch.WordTrace tailWord_6579024 prefixEnd_6579024 3378201549465572772043625 := by
  unfold tailWord_6579024
  simp only [CollatzResearch.WordTrace]
  refine ⟨119978359258663565344660063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159971145678218087126213417 119978359258663565344660063)
  ·
    refine ⟨179967538887995348016990095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119978359258663565344660063 179967538887995348016990095)
    ·
      refine ⟨269951308331993022025485143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179967538887995348016990095 269951308331993022025485143)
      ·
        refine ⟨404926962497989533038227715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 269951308331993022025485143 404926962497989533038227715)
        ·
          refine ⟨607390443746984299557341573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 404926962497989533038227715 607390443746984299557341573)
          ·
            refine ⟨113885708202559556167001545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 607390443746984299557341573 113885708202559556167001545)
            ·
              refine ⟨85414281151919667125251159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 113885708202559556167001545 85414281151919667125251159)
              ·
                refine ⟨128121421727879500687876739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 85414281151919667125251159 128121421727879500687876739)
                ·
                  refine ⟨192182132591819251031815109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 128121421727879500687876739 192182132591819251031815109)
                  ·
                    refine ⟨36034149860966109568465333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 192182132591819251031815109 36034149860966109568465333)
                    ·
                      refine ⟨3378201549465572772043625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36034149860966109568465333 3378201549465572772043625)
                      ·
                        rfl

theorem cell23_6579024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 1, 1, 4, 5].length) (baseStart_6579024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6579024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6579024 prefixEnd_6579024 := by exact prefixLift 6579024
  have htrace : WordTrace (prefixWord ++ tailWord_6579024) baseStart_6579024 baseEnd_6579024 := by
    simpa [prefixWord, tailWord_6579024, baseEnd_6579024] using wordTrace_append hprefix tailTrace_6579024
  have hstable : (prefixWord ++ tailWord_6579024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6579024).length < 2 ^ (prefixWord ++ tailWord_6579024).sum := by decide
  have hdescent : baseEnd_6579024 < baseStart_6579024 := by decide
  rcases family_descends (prefixWord ++ tailWord_6579024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6579061 : List Nat := [1, 3, 4, 1, 1, 2, 1, 1, 1, 8]
def baseStart_6579061 : Nat := 118140960795 + 6579061 * 2 ^ 59
def prefixEnd_6579061 : Nat := 4983230072969 + 3 ^ 40 * 6579061 * 2
def baseEnd_6579061 : Nat := 1126073516083263042426985

theorem tailTrace_6579061 : CollatzResearch.WordTrace tailWord_6579061 prefixEnd_6579061 1126073516083263042426985 := by
  unfold tailWord_6579061
  simp only [CollatzResearch.WordTrace]
  refine ⟨239958068018193086008417037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159972045345462057338944691 239958068018193086008417037)
  ·
    refine ⟨89984275506822407253156389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 239958068018193086008417037 89984275506822407253156389)
    ·
      refine ⟨16872051657529201359966823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 89984275506822407253156389 16872051657529201359966823)
      ·
        refine ⟨25308077486293802039950235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16872051657529201359966823 25308077486293802039950235)
        ·
          refine ⟨37962116229440703059925353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25308077486293802039950235 37962116229440703059925353)
          ·
            refine ⟨28471587172080527294944015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37962116229440703059925353 28471587172080527294944015)
            ·
              refine ⟨42707380758120790942416023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28471587172080527294944015 42707380758120790942416023)
              ·
                refine ⟨64061071137181186413624035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42707380758120790942416023 64061071137181186413624035)
                ·
                  refine ⟨96091606705771779620436053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 64061071137181186413624035 96091606705771779620436053)
                  ·
                    refine ⟨1126073516083263042426985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 96091606705771779620436053 1126073516083263042426985)
                    ·
                      rfl

theorem cell23_6579061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 1, 1, 1, 8].length) (baseStart_6579061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6579061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6579061 prefixEnd_6579061 := by exact prefixLift 6579061
  have htrace : WordTrace (prefixWord ++ tailWord_6579061) baseStart_6579061 baseEnd_6579061 := by
    simpa [prefixWord, tailWord_6579061, baseEnd_6579061] using wordTrace_append hprefix tailTrace_6579061
  have hstable : (prefixWord ++ tailWord_6579061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6579061).length < 2 ^ (prefixWord ++ tailWord_6579061).sum := by decide
  have hdescent : baseEnd_6579061 < baseStart_6579061 := by decide
  rcases family_descends (prefixWord ++ tailWord_6579061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6579062 : List Nat := [5, 1, 1, 3, 1, 1, 2, 3, 2, 1, 3]
def baseStart_6579062 : Nat := 118140960795 + 6579062 * 2 ^ 59
def prefixEnd_6579062 : Nat := 4983230072969 + 3 ^ 40 * 6579062 * 2
def baseEnd_6579062 : Nat := 3378221061730443623368451

theorem tailTrace_6579062 : CollatzResearch.WordTrace tailWord_6579062 prefixEnd_6579062 3378221061730443623368451 := by
  unfold tailWord_6579062
  simp only [CollatzResearch.WordTrace]
  refine ⟨14997381530699341448700215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 159972069660792975452802293 14997381530699341448700215)
  ·
    refine ⟨22496072296049012173050323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14997381530699341448700215 22496072296049012173050323)
    ·
      refine ⟨33744108444073518259575485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22496072296049012173050323 33744108444073518259575485)
      ·
        refine ⟨12654040666527569347340807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33744108444073518259575485 12654040666527569347340807)
        ·
          refine ⟨18981060999791354021011211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12654040666527569347340807 18981060999791354021011211)
          ·
            refine ⟨28471591499687031031516817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18981060999791354021011211 28471591499687031031516817)
            ·
              refine ⟨21353693624765273273637613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28471591499687031031516817 21353693624765273273637613)
              ·
                refine ⟨8007635109286977477614105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21353693624765273273637613 8007635109286977477614105)
                ·
                  refine ⟨6005726331965233108210579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8007635109286977477614105 6005726331965233108210579)
                  ·
                    refine ⟨9008589497947849662315869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6005726331965233108210579 9008589497947849662315869)
                    ·
                      refine ⟨3378221061730443623368451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9008589497947849662315869 3378221061730443623368451)
                      ·
                        rfl

theorem cell23_6579062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 2, 3, 2, 1, 3].length) (baseStart_6579062 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6579062 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6579062 prefixEnd_6579062 := by exact prefixLift 6579062
  have htrace : WordTrace (prefixWord ++ tailWord_6579062) baseStart_6579062 baseEnd_6579062 := by
    simpa [prefixWord, tailWord_6579062, baseEnd_6579062] using wordTrace_append hprefix tailTrace_6579062
  have hstable : (prefixWord ++ tailWord_6579062).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6579062).length < 2 ^ (prefixWord ++ tailWord_6579062).sum := by decide
  have hdescent : baseEnd_6579062 < baseStart_6579062 := by decide
  rcases family_descends (prefixWord ++ tailWord_6579062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6579108 : List Nat := [2, 3, 1, 2, 1, 2, 1, 6, 5]
def baseStart_6579108 : Nat := 118140960795 + 6579108 * 2 ^ 59
def prefixEnd_6579108 : Nat := 4983230072969 + 3 ^ 40 * 6579108 * 2
def baseEnd_6579108 : Nat := 375360520204505604821471

theorem tailTrace_6579108 : CollatzResearch.WordTrace tailWord_6579108 prefixEnd_6579108 375360520204505604821471 := by
  unfold tailWord_6579108
  simp only [CollatzResearch.WordTrace]
  refine ⟨119979891124511406517688989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159973188166015208690251985 119979891124511406517688989)
  ·
    refine ⟨44992459171691777444133371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 119979891124511406517688989 44992459171691777444133371)
    ·
      refine ⟨67488688757537666166200057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44992459171691777444133371 67488688757537666166200057)
      ·
        refine ⟨50616516568153249624650043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67488688757537666166200057 50616516568153249624650043)
        ·
          refine ⟨75924774852229874436975065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50616516568153249624650043 75924774852229874436975065)
          ·
            refine ⟨56943581139172405827731299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75924774852229874436975065 56943581139172405827731299)
            ·
              refine ⟨85415371708758608741596949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56943581139172405827731299 85415371708758608741596949)
              ·
                refine ⟨4003845548848059784762357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 85415371708758608741596949 4003845548848059784762357)
                ·
                  refine ⟨375360520204505604821471, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4003845548848059784762357 375360520204505604821471)
                  ·
                    rfl

theorem cell23_6579108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 6, 5].length) (baseStart_6579108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6579108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6579108 prefixEnd_6579108 := by exact prefixLift 6579108
  have htrace : WordTrace (prefixWord ++ tailWord_6579108) baseStart_6579108 baseEnd_6579108 := by
    simpa [prefixWord, tailWord_6579108, baseEnd_6579108] using wordTrace_append hprefix tailTrace_6579108
  have hstable : (prefixWord ++ tailWord_6579108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6579108).length < 2 ^ (prefixWord ++ tailWord_6579108).sum := by decide
  have hdescent : baseEnd_6579108 < baseStart_6579108 := by decide
  rcases family_descends (prefixWord ++ tailWord_6579108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6579248 : List Nat := [2, 1, 1, 1, 2, 4, 1, 3, 3, 1, 4]
def baseStart_6579248 : Nat := 118140960795 + 6579248 * 2 ^ 59
def prefixEnd_6579248 : Nat := 4983230072969 + 3 ^ 40 * 6579248 * 2
def baseEnd_6579248 : Nat := 3378316569132179895642595

theorem tailTrace_6579248 : CollatzResearch.WordTrace tailWord_6579248 prefixEnd_6579248 3378316569132179895642595 := by
  unfold tailWord_6579248
  simp only [CollatzResearch.WordTrace]
  refine ⟨119982444234257808472737199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159976592312343744630316265 119982444234257808472737199)
  ·
    refine ⟨179973666351386712709105799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119982444234257808472737199 179973666351386712709105799)
    ·
      refine ⟨269960499527080069063658699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179973666351386712709105799 269960499527080069063658699)
      ·
        refine ⟨404940749290620103595488049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 269960499527080069063658699 404940749290620103595488049)
        ·
          refine ⟨303705561967965077696616037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 404940749290620103595488049 303705561967965077696616037)
          ·
            refine ⟨56944792868993452068115507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 303705561967965077696616037 56944792868993452068115507)
            ·
              refine ⟨85417189303490178102173261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56944792868993452068115507 85417189303490178102173261)
              ·
                refine ⟨32031445988808816788314973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 85417189303490178102173261 32031445988808816788314973)
                ·
                  refine ⟨12011792245803306295618115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32031445988808816788314973 12011792245803306295618115)
                  ·
                    refine ⟨18017688368704959443427173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12011792245803306295618115 18017688368704959443427173)
                    ·
                      refine ⟨3378316569132179895642595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18017688368704959443427173 3378316569132179895642595)
                      ·
                        rfl

theorem cell23_6579248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 3, 3, 1, 4].length) (baseStart_6579248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6579248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6579248 prefixEnd_6579248 := by exact prefixLift 6579248
  have htrace : WordTrace (prefixWord ++ tailWord_6579248) baseStart_6579248 baseEnd_6579248 := by
    simpa [prefixWord, tailWord_6579248, baseEnd_6579248] using wordTrace_append hprefix tailTrace_6579248
  have hstable : (prefixWord ++ tailWord_6579248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6579248).length < 2 ^ (prefixWord ++ tailWord_6579248).sum := by decide
  have hdescent : baseEnd_6579248 < baseStart_6579248 := by decide
  rcases family_descends (prefixWord ++ tailWord_6579248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6579258 : List Nat := [3, 1, 1, 1, 3, 1, 4, 2, 1, 6]
def baseStart_6579258 : Nat := 118140960795 + 6579258 * 2 ^ 59
def prefixEnd_6579258 : Nat := 4983230072969 + 3 ^ 40 * 6579258 * 2
def baseEnd_6579258 : Nat := 1126107234646241618839183

theorem tailTrace_6579258 : CollatzResearch.WordTrace tailWord_6579258 prefixEnd_6579258 1126107234646241618839183 := by
  unfold tailWord_6579258
  simp only [CollatzResearch.WordTrace]
  refine ⟨59991313299619847163334607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 159976835465652925768892285 59991313299619847163334607)
  ·
    refine ⟨89986969949429770745001911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59991313299619847163334607 89986969949429770745001911)
    ·
      refine ⟨134980454924144656117502867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89986969949429770745001911 134980454924144656117502867)
      ·
        refine ⟨202470682386216984176254301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134980454924144656117502867 202470682386216984176254301)
        ·
          refine ⟨75926505894831369066095363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 202470682386216984176254301 75926505894831369066095363)
          ·
            refine ⟨113889758842247053599143045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75926505894831369066095363 113889758842247053599143045)
            ·
              refine ⟨21354329782921322549839321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 113889758842247053599143045 21354329782921322549839321)
              ·
                refine ⟨16015747337190991912379491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21354329782921322549839321 16015747337190991912379491)
                ·
                  refine ⟨24023621005786487868569237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16015747337190991912379491 24023621005786487868569237)
                  ·
                    refine ⟨1126107234646241618839183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24023621005786487868569237 1126107234646241618839183)
                    ·
                      rfl

theorem cell23_6579258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 4, 2, 1, 6].length) (baseStart_6579258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6579258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6579258 prefixEnd_6579258 := by exact prefixLift 6579258
  have htrace : WordTrace (prefixWord ++ tailWord_6579258) baseStart_6579258 baseEnd_6579258 := by
    simpa [prefixWord, tailWord_6579258, baseEnd_6579258] using wordTrace_append hprefix tailTrace_6579258
  have hstable : (prefixWord ++ tailWord_6579258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6579258).length < 2 ^ (prefixWord ++ tailWord_6579258).sum := by decide
  have hdescent : baseEnd_6579258 < baseStart_6579258 := by decide
  rcases family_descends (prefixWord ++ tailWord_6579258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6579262 : List Nat := [4, 2, 1, 3, 1, 2, 1, 3, 1, 5]
def baseStart_6579262 : Nat := 118140960795 + 6579262 * 2 ^ 59
def prefixEnd_6579262 : Nat := 4983230072969 + 3 ^ 40 * 6579262 * 2
def baseEnd_6579262 : Nat := 1126107919287114280289177

theorem tailTrace_6579262 : CollatzResearch.WordTrace tailWord_6579262 prefixEnd_6579262 1126107919287114280289177 := by
  unfold tailWord_6579262
  simp only [CollatzResearch.WordTrace]
  refine ⟨29995674886308112167060505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 159976932726976598224322693 29995674886308112167060505)
  ·
    refine ⟨22496756164731084125295379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29995674886308112167060505 22496756164731084125295379)
    ·
      refine ⟨33745134247096626187943069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22496756164731084125295379 33745134247096626187943069)
      ·
        refine ⟨12654425342661234820478651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33745134247096626187943069 12654425342661234820478651)
        ·
          refine ⟨18981638013991852230717977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12654425342661234820478651 18981638013991852230717977)
          ·
            refine ⟨14236228510493889173038483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18981638013991852230717977 14236228510493889173038483)
            ·
              refine ⟨21354342765740833759557725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14236228510493889173038483 21354342765740833759557725)
              ·
                refine ⟨8007878537152812659834147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21354342765740833759557725 8007878537152812659834147)
                ·
                  refine ⟨12011817805729218989751221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8007878537152812659834147 12011817805729218989751221)
                  ·
                    refine ⟨1126107919287114280289177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12011817805729218989751221 1126107919287114280289177)
                    ·
                      rfl

theorem cell23_6579262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 1, 3, 1, 5].length) (baseStart_6579262 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6579262 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6579262 prefixEnd_6579262 := by exact prefixLift 6579262
  have htrace : WordTrace (prefixWord ++ tailWord_6579262) baseStart_6579262 baseEnd_6579262 := by
    simpa [prefixWord, tailWord_6579262, baseEnd_6579262] using wordTrace_append hprefix tailTrace_6579262
  have hstable : (prefixWord ++ tailWord_6579262).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6579262).length < 2 ^ (prefixWord ++ tailWord_6579262).sum := by decide
  have hdescent : baseEnd_6579262 < baseStart_6579262 := by decide
  rcases family_descends (prefixWord ++ tailWord_6579262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6579278 : List Nat := [4, 1, 1, 1, 1, 3, 2, 2, 1, 1, 6]
def baseStart_6579278 : Nat := 118140960795 + 6579278 * 2 ^ 59
def prefixEnd_6579278 : Nat := 4983230072969 + 3 ^ 40 * 6579278 * 2
def baseEnd_6579278 : Nat := 3378331973551814778267457

theorem tailTrace_6579278 : CollatzResearch.WordTrace tailWord_6579278 prefixEnd_6579278 3378331973551814778267457 := by
  unfold tailWord_6579278
  simp only [CollatzResearch.WordTrace]
  refine ⟨29995747832300866508633311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 159977321772271288046044325 29995747832300866508633311)
  ·
    refine ⟨44993621748451299762949967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29995747832300866508633311 44993621748451299762949967)
    ·
      refine ⟨67490432622676949644424951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44993621748451299762949967 67490432622676949644424951)
      ·
        refine ⟨101235648934015424466637427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67490432622676949644424951 101235648934015424466637427)
        ·
          refine ⟨151853473401023136699956141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101235648934015424466637427 151853473401023136699956141)
          ·
            refine ⟨56945052525383676262483553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 151853473401023136699956141 56945052525383676262483553)
            ·
              refine ⟨42708789394037757196862665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56945052525383676262483553 42708789394037757196862665)
              ·
                refine ⟨32031592045528317897646999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42708789394037757196862665 32031592045528317897646999)
                ·
                  refine ⟨48047388068292476846470499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32031592045528317897646999 48047388068292476846470499)
                  ·
                    refine ⟨72071082102438715269705749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 48047388068292476846470499 72071082102438715269705749)
                    ·
                      refine ⟨3378331973551814778267457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 72071082102438715269705749 3378331973551814778267457)
                      ·
                        rfl

theorem cell23_6579278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 2, 2, 1, 1, 6].length) (baseStart_6579278 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6579278 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6579278 prefixEnd_6579278 := by exact prefixLift 6579278
  have htrace : WordTrace (prefixWord ++ tailWord_6579278) baseStart_6579278 baseEnd_6579278 := by
    simpa [prefixWord, tailWord_6579278, baseEnd_6579278] using wordTrace_append hprefix tailTrace_6579278
  have hstable : (prefixWord ++ tailWord_6579278).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6579278).length < 2 ^ (prefixWord ++ tailWord_6579278).sum := by decide
  have hdescent : baseEnd_6579278 < baseStart_6579278 := by decide
  rcases family_descends (prefixWord ++ tailWord_6579278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6579305 : List Nat := [1, 2, 1, 1, 1, 8, 2, 7]
def baseStart_6579305 : Nat := 118140960795 + 6579305 * 2 ^ 59
def prefixEnd_6579305 : Nat := 4983230072969 + 3 ^ 40 * 6579305 * 2
def baseEnd_6579305 : Nat := 125123919908499487875179

theorem tailTrace_6579305 : CollatzResearch.WordTrace tailWord_6579305 prefixEnd_6579305 125123919908499487875179 := by
  unfold tailWord_6579305
  simp only [CollatzResearch.WordTrace]
  refine ⟨239966967429309115680299369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159977978286206077120199579 239966967429309115680299369)
  ·
    refine ⟨179975225571981836760224527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 239966967429309115680299369 179975225571981836760224527)
    ·
      refine ⟨269962838357972755140336791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179975225571981836760224527 269962838357972755140336791)
      ·
        refine ⟨404944257536959132710505187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 269962838357972755140336791 404944257536959132710505187)
        ·
          refine ⟨607416386305438699065757781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 404944257536959132710505187 607416386305438699065757781)
          ·
            refine ⟨7118160777016859754676849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 607416386305438699065757781 7118160777016859754676849)
            ·
              refine ⟨5338620582762644816007637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7118160777016859754676849 5338620582762644816007637)
              ·
                refine ⟨125123919908499487875179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5338620582762644816007637 125123919908499487875179)
                ·
                  rfl

theorem cell23_6579305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 8, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 8, 2, 7].length) (baseStart_6579305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6579305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6579305 prefixEnd_6579305 := by exact prefixLift 6579305
  have htrace : WordTrace (prefixWord ++ tailWord_6579305) baseStart_6579305 baseEnd_6579305 := by
    simpa [prefixWord, tailWord_6579305, baseEnd_6579305] using wordTrace_append hprefix tailTrace_6579305
  have hstable : (prefixWord ++ tailWord_6579305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6579305).length < 2 ^ (prefixWord ++ tailWord_6579305).sum := by decide
  have hdescent : baseEnd_6579305 < baseStart_6579305 := by decide
  rcases family_descends (prefixWord ++ tailWord_6579305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6579332 : List Nat := [2, 3, 2, 1, 2, 2, 2, 1, 4, 1, 3]
def baseStart_6579332 : Nat := 118140960795 + 6579332 * 2 ^ 59
def prefixEnd_6579332 : Nat := 4983230072969 + 3 ^ 40 * 6579332 * 2
def baseEnd_6579332 : Nat := 3378359701507157566992209

theorem tailTrace_6579332 : CollatzResearch.WordTrace tailWord_6579332 prefixEnd_6579332 3378359701507157566992209 := by
  unfold tailWord_6579332
  simp only [CollatzResearch.WordTrace]
  refine ⟨119983976100105649645766125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159978634800140866194354833 119983976100105649645766125)
  ·
    refine ⟨44993991037539618617162297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 119983976100105649645766125 44993991037539618617162297)
    ·
      refine ⟨33745493278154713962871723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44993991037539618617162297 33745493278154713962871723)
      ·
        refine ⟨50618239917232070944307585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33745493278154713962871723 50618239917232070944307585)
        ·
          refine ⟨37963679937924053208230689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50618239917232070944307585 37963679937924053208230689)
          ·
            refine ⟨28472759953443039906173017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37963679937924053208230689 28472759953443039906173017)
            ·
              refine ⟨21354569965082279929629763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28472759953443039906173017 21354569965082279929629763)
              ·
                refine ⟨32031854947623419894444645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21354569965082279929629763 32031854947623419894444645)
                ·
                  refine ⟨6005972802679391230208371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32031854947623419894444645 6005972802679391230208371)
                  ·
                    refine ⟨9008959204019086845312557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6005972802679391230208371 9008959204019086845312557)
                    ·
                      refine ⟨3378359701507157566992209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9008959204019086845312557 3378359701507157566992209)
                      ·
                        rfl

theorem cell23_6579332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 2, 1, 4, 1, 3].length) (baseStart_6579332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6579332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6579332 prefixEnd_6579332 := by exact prefixLift 6579332
  have htrace : WordTrace (prefixWord ++ tailWord_6579332) baseStart_6579332 baseEnd_6579332 := by
    simpa [prefixWord, tailWord_6579332, baseEnd_6579332] using wordTrace_append hprefix tailTrace_6579332
  have hstable : (prefixWord ++ tailWord_6579332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6579332).length < 2 ^ (prefixWord ++ tailWord_6579332).sum := by decide
  have hdescent : baseEnd_6579332 < baseStart_6579332 := by decide
  rcases family_descends (prefixWord ++ tailWord_6579332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6579333 : List Nat := [1, 3, 1, 1, 6, 1, 3, 2, 1, 2, 2]
def baseStart_6579333 : Nat := 118140960795 + 6579333 * 2 ^ 59
def prefixEnd_6579333 : Nat := 4983230072969 + 3 ^ 40 * 6579333 * 2
def baseEnd_6579333 : Nat := 3378360214987812063079705

theorem tailTrace_6579333 : CollatzResearch.WordTrace tailWord_6579333 prefixEnd_6579333 3378360214987812063079705 := by
  unfold tailWord_6579333
  simp only [CollatzResearch.WordTrace]
  refine ⟨239967988673207676462318653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159978659115471784308212435 239967988673207676462318653)
  ·
    refine ⟨89987995752452878673369495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 239967988673207676462318653 89987995752452878673369495)
    ·
      refine ⟨134981993628679318010054243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89987995752452878673369495 134981993628679318010054243)
      ·
        refine ⟨202472990443018977015081365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134981993628679318010054243 202472990443018977015081365)
        ·
          refine ⟨9490921427016514547581939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 202472990443018977015081365 9490921427016514547581939)
          ·
            refine ⟨14236382140524771821372909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9490921427016514547581939 14236382140524771821372909)
            ·
              refine ⟨5338643302696789433014841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14236382140524771821372909 5338643302696789433014841)
              ·
                refine ⟨4003982477022592074761131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5338643302696789433014841 4003982477022592074761131)
                ·
                  refine ⟨6005973715533888112141697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4003982477022592074761131 6005973715533888112141697)
                  ·
                    refine ⟨4504480286650416084106273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6005973715533888112141697 4504480286650416084106273)
                    ·
                      refine ⟨3378360214987812063079705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4504480286650416084106273 3378360214987812063079705)
                      ·
                        rfl

theorem cell23_6579333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 3, 2, 1, 2, 2].length) (baseStart_6579333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6579333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6579333 prefixEnd_6579333 := by exact prefixLift 6579333
  have htrace : WordTrace (prefixWord ++ tailWord_6579333) baseStart_6579333 baseEnd_6579333 := by
    simpa [prefixWord, tailWord_6579333, baseEnd_6579333] using wordTrace_append hprefix tailTrace_6579333
  have hstable : (prefixWord ++ tailWord_6579333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6579333).length < 2 ^ (prefixWord ++ tailWord_6579333).sum := by decide
  have hdescent : baseEnd_6579333 < baseStart_6579333 := by decide
  rcases family_descends (prefixWord ++ tailWord_6579333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6579359 : List Nat := [1, 1, 2, 6, 2, 1, 1, 1, 3, 3, 2]
def baseStart_6579359 : Nat := 118140960795 + 6579359 * 2 ^ 59
def prefixEnd_6579359 : Nat := 4983230072969 + 3 ^ 40 * 6579359 * 2
def baseEnd_6579359 : Nat := 3378373565484828961354585

theorem tailTrace_6579359 : CollatzResearch.WordTrace tailWord_6579359 prefixEnd_6579359 3378373565484828961354585 := by
  unfold tailWord_6579359
  simp only [CollatzResearch.WordTrace]
  refine ⟨239968936971113482902765131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159979291314075655268510087 239968936971113482902765131)
  ·
    refine ⟨359953405456670224354147697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 239968936971113482902765131 359953405456670224354147697)
    ·
      refine ⟨269965054092502668265610773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 359953405456670224354147697 269965054092502668265610773)
      ·
        refine ⟨12654611910586062574950505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 269965054092502668265610773 12654611910586062574950505)
        ·
          refine ⟨9490958932939546931212879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12654611910586062574950505 9490958932939546931212879)
          ·
            refine ⟨14236438399409320396819319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9490958932939546931212879 14236438399409320396819319)
            ·
              refine ⟨21354657599113980595228979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14236438399409320396819319 21354657599113980595228979)
              ·
                refine ⟨32031986398670970892843469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21354657599113980595228979 32031986398670970892843469)
                ·
                  refine ⟨12011994899501614084816301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32031986398670970892843469 12011994899501614084816301)
                  ·
                    refine ⟨4504498087313105281806113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12011994899501614084816301 4504498087313105281806113)
                    ·
                      refine ⟨3378373565484828961354585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4504498087313105281806113 3378373565484828961354585)
                      ·
                        rfl

theorem cell23_6579359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 1, 1, 3, 3, 2].length) (baseStart_6579359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6579359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6579359 prefixEnd_6579359 := by exact prefixLift 6579359
  have htrace : WordTrace (prefixWord ++ tailWord_6579359) baseStart_6579359 baseEnd_6579359 := by
    simpa [prefixWord, tailWord_6579359, baseEnd_6579359] using wordTrace_append hprefix tailTrace_6579359
  have hstable : (prefixWord ++ tailWord_6579359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6579359).length < 2 ^ (prefixWord ++ tailWord_6579359).sum := by decide
  have hdescent : baseEnd_6579359 < baseStart_6579359 := by decide
  rcases family_descends (prefixWord ++ tailWord_6579359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6579372 : List Nat := [2, 2, 1, 1, 1, 1, 1, 6, 4, 2, 2]
def baseStart_6579372 : Nat := 118140960795 + 6579372 * 2 ^ 59
def prefixEnd_6579372 : Nat := 4983230072969 + 3 ^ 40 * 6579372 * 2
def baseEnd_6579372 : Nat := 3378380240733337410492025

theorem tailTrace_6579372 : CollatzResearch.WordTrace tailWord_6579372 prefixEnd_6579372 3378380240733337410492025 := by
  unfold tailWord_6579372
  simp only [CollatzResearch.WordTrace]
  refine ⟨119984705560033193061494185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159979607413377590748658913 119984705560033193061494185)
  ·
    refine ⟨89988529170024894796120639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119984705560033193061494185 89988529170024894796120639)
    ·
      refine ⟨134982793755037342194180959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89988529170024894796120639 134982793755037342194180959)
      ·
        refine ⟨202474190632556013291271439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134982793755037342194180959 202474190632556013291271439)
        ·
          refine ⟨303711285948834019936907159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 202474190632556013291271439 303711285948834019936907159)
          ·
            refine ⟨455566928923251029905360739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 303711285948834019936907159 455566928923251029905360739)
            ·
              refine ⟨683350393384876544858041109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 455566928923251029905360739 683350393384876544858041109)
              ·
                refine ⟨32032049689916088040220677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 683350393384876544858041109 32032049689916088040220677)
                ·
                  refine ⟨6006009316859266507541377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32032049689916088040220677 6006009316859266507541377)
                  ·
                    refine ⟨4504506987644449880656033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6006009316859266507541377 4504506987644449880656033)
                    ·
                      refine ⟨3378380240733337410492025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4504506987644449880656033 3378380240733337410492025)
                      ·
                        rfl

theorem cell23_6579372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 4, 2, 2].length) (baseStart_6579372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6579372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6579372 prefixEnd_6579372 := by exact prefixLift 6579372
  have htrace : WordTrace (prefixWord ++ tailWord_6579372) baseStart_6579372 baseEnd_6579372 := by
    simpa [prefixWord, tailWord_6579372, baseEnd_6579372] using wordTrace_append hprefix tailTrace_6579372
  have hstable : (prefixWord ++ tailWord_6579372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6579372).length < 2 ^ (prefixWord ++ tailWord_6579372).sum := by decide
  have hdescent : baseEnd_6579372 < baseStart_6579372 := by decide
  rcases family_descends (prefixWord ++ tailWord_6579372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6579389 : List Nat := [1, 4, 1, 2, 1, 1, 3, 4, 2, 2, 2]
def baseStart_6579389 : Nat := 118140960795 + 6579389 * 2 ^ 59
def prefixEnd_6579389 : Nat := 4983230072969 + 3 ^ 40 * 6579389 * 2
def baseEnd_6579389 : Nat := 3378388969904463843979447

theorem tailTrace_6579389 : CollatzResearch.WordTrace tailWord_6579389 prefixEnd_6579389 3378388969904463843979447 := by
  unfold tailWord_6579389
  simp only [CollatzResearch.WordTrace]
  refine ⟨239970031161004798026357221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159980020774003198684238147 239970031161004798026357221)
  ·
    refine ⟨44994380842688399629941979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 239970031161004798026357221 44994380842688399629941979)
    ·
      refine ⟨67491571264032599444912969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44994380842688399629941979 67491571264032599444912969)
      ·
        refine ⟨50618678448024449583684727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67491571264032599444912969 50618678448024449583684727)
        ·
          refine ⟨75928017672036674375527091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50618678448024449583684727 75928017672036674375527091)
          ·
            refine ⟨113892026508055011563290637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75928017672036674375527091 113892026508055011563290637)
            ·
              refine ⟨42709509940520629336233989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 113892026508055011563290637 42709509940520629336233989)
              ·
                refine ⟨8008033113847618000543873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 42709509940520629336233989 8008033113847618000543873)
                ·
                  refine ⟨6006024835385713500407905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8008033113847618000543873 6006024835385713500407905)
                  ·
                    refine ⟨4504518626539285125305929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6006024835385713500407905 4504518626539285125305929)
                    ·
                      refine ⟨3378388969904463843979447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4504518626539285125305929 3378388969904463843979447)
                      ·
                        rfl

theorem cell23_6579389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 3, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 3, 4, 2, 2, 2].length) (baseStart_6579389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6579389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6579389 prefixEnd_6579389 := by exact prefixLift 6579389
  have htrace : WordTrace (prefixWord ++ tailWord_6579389) baseStart_6579389 baseEnd_6579389 := by
    simpa [prefixWord, tailWord_6579389, baseEnd_6579389] using wordTrace_append hprefix tailTrace_6579389
  have hstable : (prefixWord ++ tailWord_6579389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6579389).length < 2 ^ (prefixWord ++ tailWord_6579389).sum := by decide
  have hdescent : baseEnd_6579389 < baseStart_6579389 := by decide
  rcases family_descends (prefixWord ++ tailWord_6579389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6579425 : List Nat := [1, 2, 3, 1, 3, 3, 1, 1, 1, 7]
def baseStart_6579425 : Nat := 118140960795 + 6579425 * 2 ^ 59
def prefixEnd_6579425 : Nat := 4983230072969 + 3 ^ 40 * 6579425 * 2
def baseEnd_6579425 : Nat := 1126135818402675234376427

theorem tailTrace_6579425 : CollatzResearch.WordTrace tailWord_6579425 prefixEnd_6579425 1126135818402675234376427 := by
  unfold tailWord_6579425
  simp only [CollatzResearch.WordTrace]
  refine ⟨239971344188874376174667729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159980896125916250783111819 239971344188874376174667729)
  ·
    refine ⟨179978508141655782131000797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 239971344188874376174667729 179978508141655782131000797)
    ·
      refine ⟨67491940553120918299125299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 179978508141655782131000797 67491940553120918299125299)
      ·
        refine ⟨101237910829681377448687949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67491940553120918299125299 101237910829681377448687949)
        ·
          refine ⟨37964216561130516543257981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 101237910829681377448687949 37964216561130516543257981)
          ·
            refine ⟨14236581210423943703721743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37964216561130516543257981 14236581210423943703721743)
            ·
              refine ⟨21354871815635915555582615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14236581210423943703721743 21354871815635915555582615)
              ·
                refine ⟨32032307723453873333373923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21354871815635915555582615 32032307723453873333373923)
                ·
                  refine ⟨48048461585180810000060885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32032307723453873333373923 48048461585180810000060885)
                  ·
                    refine ⟨1126135818402675234376427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 48048461585180810000060885 1126135818402675234376427)
                    ·
                      rfl

theorem cell23_6579425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 1, 1, 1, 7].length) (baseStart_6579425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6579425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6579425 prefixEnd_6579425 := by exact prefixLift 6579425
  have htrace : WordTrace (prefixWord ++ tailWord_6579425) baseStart_6579425 baseEnd_6579425 := by
    simpa [prefixWord, tailWord_6579425, baseEnd_6579425] using wordTrace_append hprefix tailTrace_6579425
  have hstable : (prefixWord ++ tailWord_6579425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6579425).length < 2 ^ (prefixWord ++ tailWord_6579425).sum := by decide
  have hdescent : baseEnd_6579425 < baseStart_6579425 := by decide
  rcases family_descends (prefixWord ++ tailWord_6579425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6579429 : List Nat := [1, 3, 1, 4, 3, 1, 2, 3, 5]
def baseStart_6579429 : Nat := 118140960795 + 6579429 * 2 ^ 59
def prefixEnd_6579429 : Nat := 4983230072969 + 3 ^ 40 * 6579429 * 2
def baseEnd_6579429 : Nat := 375378834347849298608807

theorem tailTrace_6579429 : CollatzResearch.WordTrace tailWord_6579429 prefixEnd_6579429 375378834347849298608807 := by
  unfold tailWord_6579429
  simp only [CollatzResearch.WordTrace]
  refine ⟨239971490080859884857813341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159980993387239923238542227 239971490080859884857813341)
  ·
    refine ⟨89989308780322456821680003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 239971490080859884857813341 89989308780322456821680003)
    ·
      refine ⟨134983963170483685232520005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89989308780322456821680003 134983963170483685232520005)
      ·
        refine ⟨25309493094465690981097501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 134983963170483685232520005 25309493094465690981097501)
        ·
          refine ⟨9491059910424634117911563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25309493094465690981097501 9491059910424634117911563)
          ·
            refine ⟨14236589865636951176867345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9491059910424634117911563 14236589865636951176867345)
            ·
              refine ⟨10677442399227713382650509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14236589865636951176867345 10677442399227713382650509)
              ·
                refine ⟨4004040899710392518493941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10677442399227713382650509 4004040899710392518493941)
                ·
                  refine ⟨375378834347849298608807, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4004040899710392518493941 375378834347849298608807)
                  ·
                    rfl

theorem cell23_6579429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 2, 3, 5].length) (baseStart_6579429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6579429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6579429 prefixEnd_6579429 := by exact prefixLift 6579429
  have htrace : WordTrace (prefixWord ++ tailWord_6579429) baseStart_6579429 baseEnd_6579429 := by
    simpa [prefixWord, tailWord_6579429, baseEnd_6579429] using wordTrace_append hprefix tailTrace_6579429
  have hstable : (prefixWord ++ tailWord_6579429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6579429).length < 2 ^ (prefixWord ++ tailWord_6579429).sum := by decide
  have hdescent : baseEnd_6579429 < baseStart_6579429 := by decide
  rcases family_descends (prefixWord ++ tailWord_6579429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6579465 : List Nat := [1, 2, 1, 1, 3, 3, 1, 1, 3, 4, 3]
def baseStart_6579465 : Nat := 118140960795 + 6579465 * 2 ^ 59
def prefixEnd_6579465 : Nat := 4983230072969 + 3 ^ 40 * 6579465 * 2
def baseEnd_6579465 : Nat := 3378427994434205546629097

theorem tailTrace_6579465 : CollatzResearch.WordTrace tailWord_6579465 prefixEnd_6579465 3378427994434205546629097 := by
  unfold tailWord_6579465
  simp only [CollatzResearch.WordTrace]
  refine ⟨239972803108729463006123849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159981868739152975337415899 239972803108729463006123849)
  ·
    refine ⟨179979602331547097254592887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 239972803108729463006123849 179979602331547097254592887)
    ·
      refine ⟨269969403497320645881889331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179979602331547097254592887 269969403497320645881889331)
      ·
        refine ⟨404954105245980968822833997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 269969403497320645881889331 404954105245980968822833997)
        ·
          refine ⟨151857789467242863308562749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 404954105245980968822833997 151857789467242863308562749)
          ·
            refine ⟨56946671050216073740711031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 151857789467242863308562749 56946671050216073740711031)
            ·
              refine ⟨85420006575324110611066547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56946671050216073740711031 85420006575324110611066547)
              ·
                refine ⟨128130009862986165916599821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 85420006575324110611066547 128130009862986165916599821)
                ·
                  refine ⟨48048753698619812218724933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 128130009862986165916599821 48048753698619812218724933)
                  ·
                    refine ⟨9009141318491214791010925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 48048753698619812218724933 9009141318491214791010925)
                    ·
                      refine ⟨3378427994434205546629097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9009141318491214791010925 3378427994434205546629097)
                      ·
                        rfl

theorem cell23_6579465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 1, 3, 4, 3].length) (baseStart_6579465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6579465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6579465 prefixEnd_6579465 := by exact prefixLift 6579465
  have htrace : WordTrace (prefixWord ++ tailWord_6579465) baseStart_6579465 baseEnd_6579465 := by
    simpa [prefixWord, tailWord_6579465, baseEnd_6579465] using wordTrace_append hprefix tailTrace_6579465
  have hstable : (prefixWord ++ tailWord_6579465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6579465).length < 2 ^ (prefixWord ++ tailWord_6579465).sum := by decide
  have hdescent : baseEnd_6579465 < baseStart_6579465 := by decide
  rcases family_descends (prefixWord ++ tailWord_6579465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6579482 : List Nat := [3, 1, 1, 3, 3, 1, 2, 1, 1, 4, 3]
def baseStart_6579482 : Nat := 118140960795 + 6579482 * 2 ^ 59
def prefixEnd_6579482 : Nat := 4983230072969 + 3 ^ 40 * 6579482 * 2
def baseEnd_6579482 : Nat := 3378436723605331980116519

theorem tailTrace_6579482 : CollatzResearch.WordTrace tailWord_6579482 prefixEnd_6579482 3378436723605331980116519 := by
  unfold tailWord_6579482
  simp only [CollatzResearch.WordTrace]
  refine ⟨59993355787416968727373175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 159982282099778583272995133 59993355787416968727373175)
  ·
    refine ⟨89990033681125453091059763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59993355787416968727373175 89990033681125453091059763)
    ·
      refine ⟨134985050521688179636589645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89990033681125453091059763 134985050521688179636589645)
      ·
        refine ⟨50619393945633067363721117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 134985050521688179636589645 50619393945633067363721117)
        ·
          refine ⟨18982272729612400261395419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50619393945633067363721117 18982272729612400261395419)
          ·
            refine ⟨28473409094418600392093129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18982272729612400261395419 28473409094418600392093129)
            ·
              refine ⟨21355056820813950294069847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28473409094418600392093129 21355056820813950294069847)
              ·
                refine ⟨32032585231220925441104771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21355056820813950294069847 32032585231220925441104771)
                ·
                  refine ⟨48048877846831388161657157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32032585231220925441104771 48048877846831388161657157)
                  ·
                    refine ⟨9009164596280885280310717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 48048877846831388161657157 9009164596280885280310717)
                    ·
                      refine ⟨3378436723605331980116519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9009164596280885280310717 3378436723605331980116519)
                      ·
                        rfl

theorem cell23_6579482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 2, 1, 1, 4, 3].length) (baseStart_6579482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6579482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6579482 prefixEnd_6579482 := by exact prefixLift 6579482
  have htrace : WordTrace (prefixWord ++ tailWord_6579482) baseStart_6579482 baseEnd_6579482 := by
    simpa [prefixWord, tailWord_6579482, baseEnd_6579482] using wordTrace_append hprefix tailTrace_6579482
  have hstable : (prefixWord ++ tailWord_6579482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6579482).length < 2 ^ (prefixWord ++ tailWord_6579482).sum := by decide
  have hdescent : baseEnd_6579482 < baseStart_6579482 := by decide
  rcases family_descends (prefixWord ++ tailWord_6579482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6579519 : List Nat := [1, 1, 2, 2, 4, 4, 2, 1, 6]
def baseStart_6579519 : Nat := 118140960795 + 6579519 * 2 ^ 59
def prefixEnd_6579519 : Nat := 4983230072969 + 3 ^ 40 * 6579519 * 2
def baseEnd_6579519 : Nat := 375383969154394259483761

theorem tailTrace_6579519 : CollatzResearch.WordTrace tailWord_6579519 prefixEnd_6579519 375383969154394259483761 := by
  unfold tailWord_6579519
  simp only [CollatzResearch.WordTrace]
  refine ⟨239974772650533830228589611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159983181767022553485726407 239974772650533830228589611)
  ·
    refine ⟨359962158975800745342884417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 239974772650533830228589611 359962158975800745342884417)
    ·
      refine ⟨269971619231850559007163313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 359962158975800745342884417 269971619231850559007163313)
      ·
        refine ⟨202478714423887919255372485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 269971619231850559007163313 202478714423887919255372485)
        ·
          refine ⟨37964758954478984860382341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 202478714423887919255372485 37964758954478984860382341)
          ·
            refine ⟨7118392303964809661321689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37964758954478984860382341 7118392303964809661321689)
            ·
              refine ⟨5338794227973607245991267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7118392303964809661321689 5338794227973607245991267)
              ·
                refine ⟨8008191341960410868986901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5338794227973607245991267 8008191341960410868986901)
                ·
                  refine ⟨375383969154394259483761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8008191341960410868986901 375383969154394259483761)
                  ·
                    rfl

theorem cell23_6579519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 4, 2, 1, 6].length) (baseStart_6579519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6579519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6579519 prefixEnd_6579519 := by exact prefixLift 6579519
  have htrace : WordTrace (prefixWord ++ tailWord_6579519) baseStart_6579519 baseEnd_6579519 := by
    simpa [prefixWord, tailWord_6579519, baseEnd_6579519] using wordTrace_append hprefix tailTrace_6579519
  have hstable : (prefixWord ++ tailWord_6579519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6579519).length < 2 ^ (prefixWord ++ tailWord_6579519).sum := by decide
  have hdescent : baseEnd_6579519 < baseStart_6579519 := by decide
  rcases family_descends (prefixWord ++ tailWord_6579519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6579532 : List Nat := [2, 2, 1, 3, 2, 3, 1, 1, 3, 5]
def baseStart_6579532 : Nat := 118140960795 + 6579532 * 2 ^ 59
def prefixEnd_6579532 : Nat := 4983230072969 + 3 ^ 40 * 6579532 * 2
def baseEnd_6579532 : Nat := 1126154132546018928163763

theorem tailTrace_6579532 : CollatzResearch.WordTrace tailWord_6579532 prefixEnd_6579532 1126154132546018928163763 := by
  unfold tailWord_6579532
  simp only [CollatzResearch.WordTrace]
  refine ⟨119987623399743366724406425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159983497866324488965875233 119987623399743366724406425)
  ·
    refine ⟨89990717549807525043304819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119987623399743366724406425 89990717549807525043304819)
    ·
      refine ⟨134986076324711287564957229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89990717549807525043304819 134986076324711287564957229)
      ·
        refine ⟨50619778621766732836858961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 134986076324711287564957229 50619778621766732836858961)
        ·
          refine ⟨37964833966325049627644221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50619778621766732836858961 37964833966325049627644221)
          ·
            refine ⟨14236812737371893610366583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37964833966325049627644221 14236812737371893610366583)
            ·
              refine ⟨21355219106057840415549875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14236812737371893610366583 21355219106057840415549875)
              ·
                refine ⟨32032828659086760623324813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21355219106057840415549875 32032828659086760623324813)
                ·
                  refine ⟨12012310747157535233746805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32032828659086760623324813 12012310747157535233746805)
                  ·
                    refine ⟨1126154132546018928163763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12012310747157535233746805 1126154132546018928163763)
                    ·
                      rfl

theorem cell23_6579532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 1, 1, 3, 5].length) (baseStart_6579532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6579532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6579532 prefixEnd_6579532 := by exact prefixLift 6579532
  have htrace : WordTrace (prefixWord ++ tailWord_6579532) baseStart_6579532 baseEnd_6579532 := by
    simpa [prefixWord, tailWord_6579532, baseEnd_6579532] using wordTrace_append hprefix tailTrace_6579532
  have hstable : (prefixWord ++ tailWord_6579532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6579532).length < 2 ^ (prefixWord ++ tailWord_6579532).sum := by decide
  have hdescent : baseEnd_6579532 < baseStart_6579532 := by decide
  rcases family_descends (prefixWord ++ tailWord_6579532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6579533 : List Nat := [1, 6, 1, 3, 1, 1, 2, 1, 2, 2, 3]
def baseStart_6579533 : Nat := 118140960795 + 6579533 * 2 ^ 59
def prefixEnd_6579533 : Nat := 4983230072969 + 3 ^ 40 * 6579533 * 2
def baseEnd_6579533 : Nat := 3378462911118711280578785

theorem tailTrace_6579533 : CollatzResearch.WordTrace tailWord_6579533 prefixEnd_6579533 3378462911118711280578785 := by
  unfold tailWord_6579533
  simp only [CollatzResearch.WordTrace]
  refine ⟨239975283272483110619599253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159983522181655407079732835 239975283272483110619599253)
  ·
    refine ⟨11248841403397645810293715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 239975283272483110619599253 11248841403397645810293715)
    ·
      refine ⟨16873262105096468715440573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11248841403397645810293715 16873262105096468715440573)
      ·
        refine ⟨6327473289411175768290215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16873262105096468715440573 6327473289411175768290215)
        ·
          refine ⟨9491209934116763652435323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6327473289411175768290215 9491209934116763652435323)
          ·
            refine ⟨14236814901175145478652985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9491209934116763652435323 14236814901175145478652985)
            ·
              refine ⟨10677611175881359108989739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14236814901175145478652985 10677611175881359108989739)
              ·
                refine ⟨16016416763822038663484609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10677611175881359108989739 16016416763822038663484609)
                ·
                  refine ⟨12012312572866528997613457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16016416763822038663484609 12012312572866528997613457)
                  ·
                    refine ⟨9009234429649896748210093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12012312572866528997613457 9009234429649896748210093)
                    ·
                      refine ⟨3378462911118711280578785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9009234429649896748210093 3378462911118711280578785)
                      ·
                        rfl

theorem cell23_6579533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 2, 1, 2, 2, 3].length) (baseStart_6579533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6579533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6579533 prefixEnd_6579533 := by exact prefixLift 6579533
  have htrace : WordTrace (prefixWord ++ tailWord_6579533) baseStart_6579533 baseEnd_6579533 := by
    simpa [prefixWord, tailWord_6579533, baseEnd_6579533] using wordTrace_append hprefix tailTrace_6579533
  have hstable : (prefixWord ++ tailWord_6579533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6579533).length < 2 ^ (prefixWord ++ tailWord_6579533).sum := by decide
  have hdescent : baseEnd_6579533 < baseStart_6579533 := by decide
  rcases family_descends (prefixWord ++ tailWord_6579533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6579539 : List Nat := [1, 1, 1, 2, 1, 1, 8, 1, 2, 3, 2]
def baseStart_6579539 : Nat := 118140960795 + 6579539 * 2 ^ 59
def prefixEnd_6579539 : Nat := 4983230072969 + 3 ^ 40 * 6579539 * 2
def baseEnd_6579539 : Nat := 3378465992002638257103757

theorem tailTrace_6579539 : CollatzResearch.WordTrace tailWord_6579539 prefixEnd_6579539 3378465992002638257103757 := by
  unfold tailWord_6579539
  simp only [CollatzResearch.WordTrace]
  refine ⟨239975502110461373644317671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159983668073640915762878447 239975502110461373644317671)
  ·
    refine ⟨359963253165692060466476507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 239975502110461373644317671 359963253165692060466476507)
    ·
      refine ⟨539944879748538090699714761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 359963253165692060466476507 539944879748538090699714761)
      ·
        refine ⟨404958659811403568024786071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 539944879748538090699714761 404958659811403568024786071)
        ·
          refine ⟨607437989717105352037179107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 404958659811403568024786071 607437989717105352037179107)
          ·
            refine ⟨911156984575658028055768661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 607437989717105352037179107 911156984575658028055768661)
            ·
              refine ⟨10677620912995992516278539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 911156984575658028055768661 10677620912995992516278539)
              ·
                refine ⟨16016431369493988774417809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10677620912995992516278539 16016431369493988774417809)
                ·
                  refine ⟨12012323527120491580813357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16016431369493988774417809 12012323527120491580813357)
                  ·
                    refine ⟨4504621322670184342805009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12012323527120491580813357 4504621322670184342805009)
                    ·
                      refine ⟨3378465992002638257103757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4504621322670184342805009 3378465992002638257103757)
                      ·
                        rfl

theorem cell23_6579539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 8, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 8, 1, 2, 3, 2].length) (baseStart_6579539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6579539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6579539 prefixEnd_6579539 := by exact prefixLift 6579539
  have htrace : WordTrace (prefixWord ++ tailWord_6579539) baseStart_6579539 baseEnd_6579539 := by
    simpa [prefixWord, tailWord_6579539, baseEnd_6579539] using wordTrace_append hprefix tailTrace_6579539
  have hstable : (prefixWord ++ tailWord_6579539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6579539).length < 2 ^ (prefixWord ++ tailWord_6579539).sum := by decide
  have hdescent : baseEnd_6579539 < baseStart_6579539 := by decide
  rcases family_descends (prefixWord ++ tailWord_6579539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6579545 : List Nat := [1, 2, 1, 2, 2, 2, 3, 1, 3, 6]
def baseStart_6579545 : Nat := 118140960795 + 6579545 * 2 ^ 59
def prefixEnd_6579545 : Nat := 4983230072969 + 3 ^ 40 * 6579545 * 2
def baseEnd_6579545 : Nat := 1126156357628855077876243

theorem tailTrace_6579545 : CollatzResearch.WordTrace tailWord_6579545 prefixEnd_6579545 1126156357628855077876243 := by
  unfold tailWord_6579545
  simp only [CollatzResearch.WordTrace]
  refine ⟨239975720948439636669036089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159983813965626424446024059 239975720948439636669036089)
  ·
    refine ⟨179981790711329727501777067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 239975720948439636669036089 179981790711329727501777067)
    ·
      refine ⟨269972686066994591252665601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179981790711329727501777067 269972686066994591252665601)
      ·
        refine ⟨202479514550245943439499201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 269972686066994591252665601 202479514550245943439499201)
        ·
          refine ⟨151859635912684457579624401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 202479514550245943439499201 151859635912684457579624401)
          ·
            refine ⟨113894726934513343184718301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 151859635912684457579624401 113894726934513343184718301)
            ·
              refine ⟨42710522600442503694269363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 113894726934513343184718301 42710522600442503694269363)
              ·
                refine ⟨64065783900663755541404045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42710522600442503694269363 64065783900663755541404045)
                ·
                  refine ⟨24024668962748908328026517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 64065783900663755541404045 24024668962748908328026517)
                  ·
                    refine ⟨1126156357628855077876243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24024668962748908328026517 1126156357628855077876243)
                    ·
                      rfl

theorem cell23_6579545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 3, 1, 3, 6].length) (baseStart_6579545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6579545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6579545 prefixEnd_6579545 := by exact prefixLift 6579545
  have htrace : WordTrace (prefixWord ++ tailWord_6579545) baseStart_6579545 baseEnd_6579545 := by
    simpa [prefixWord, tailWord_6579545, baseEnd_6579545] using wordTrace_append hprefix tailTrace_6579545
  have hstable : (prefixWord ++ tailWord_6579545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6579545).length < 2 ^ (prefixWord ++ tailWord_6579545).sum := by decide
  have hdescent : baseEnd_6579545 < baseStart_6579545 := by decide
  rcases family_descends (prefixWord ++ tailWord_6579545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
