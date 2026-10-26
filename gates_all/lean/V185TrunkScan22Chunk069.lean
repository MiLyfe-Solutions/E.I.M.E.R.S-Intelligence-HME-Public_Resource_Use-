import V185TrunkScan22Chunk068

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_620345 : List Nat := [1, 2, 1, 7, 1, 1, 2, 1, 2, 4]
def baseStart_620345 : Nat := 118140960795 + 620345 * 2 ^ 59
def prefixEnd_620345 : Nat := 4983230072969 + 3 ^ 40 * 620345 * 2
def baseEnd_620345 : Nat := 212356771075653754023061

theorem tailTrace_620345 : CollatzResearch.WordTrace tailWord_620345 prefixEnd_620345 212356771075653754023061 := by
  unfold tailWord_620345
  simp only [CollatzResearch.WordTrace]
  refine ⟨22625840937603486336278489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15083893958402324224185659 22625840937603486336278489)
  ·
    refine ⟨16969380703202614752208867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22625840937603486336278489 16969380703202614752208867)
    ·
      refine ⟨25454071054803922128313301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16969380703202614752208867 25454071054803922128313301)
      ·
        refine ⟨596579790346966924882343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 25454071054803922128313301 596579790346966924882343)
        ·
          refine ⟨894869685520450387323515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 596579790346966924882343 894869685520450387323515)
          ·
            refine ⟨1342304528280675580985273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 894869685520450387323515 1342304528280675580985273)
            ·
              refine ⟨1006728396210506685738955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1342304528280675580985273 1006728396210506685738955)
              ·
                refine ⟨1510092594315760028608433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1006728396210506685738955 1510092594315760028608433)
                ·
                  refine ⟨1132569445736820021456325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1510092594315760028608433 1132569445736820021456325)
                  ·
                    refine ⟨212356771075653754023061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1132569445736820021456325 212356771075653754023061)
                    ·
                      rfl

theorem cell22_620345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 2, 1, 2, 4].length) (baseStart_620345 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_620345 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_620345 prefixEnd_620345 := by exact prefixLift 620345
  have htrace : WordTrace (prefixWord ++ tailWord_620345) baseStart_620345 baseEnd_620345 := by
    simpa [prefixWord, tailWord_620345, baseEnd_620345] using wordTrace_append hprefix tailTrace_620345
  have hstable : (prefixWord ++ tailWord_620345).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_620345).length < 2 ^ (prefixWord ++ tailWord_620345).sum := by decide
  have hdescent : baseEnd_620345 < baseStart_620345 := by decide
  rcases family_descends (prefixWord ++ tailWord_620345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_620401 : List Nat := [1, 2, 2, 2, 1, 3, 1, 3, 3, 4]
def baseStart_620401 : Nat := 118140960795 + 620401 * 2 ^ 59
def prefixEnd_620401 : Nat := 4983230072969 + 3 ^ 40 * 620401 * 2
def baseEnd_620401 : Nat := 212375941020088274622889

theorem tailTrace_620401 : CollatzResearch.WordTrace tailWord_620401 prefixEnd_620401 212375941020088274622889 := by
  unfold tailWord_620401
  simp only [CollatzResearch.WordTrace]
  refine ⟨22627883425400607900317057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15085255616933738600211371 22627883425400607900317057)
  ·
    refine ⟨16970912569050455925237793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22627883425400607900317057 16970912569050455925237793)
    ·
      refine ⟨12728184426787841943928345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16970912569050455925237793 12728184426787841943928345)
      ·
        refine ⟨9546138320090881457946259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12728184426787841943928345 9546138320090881457946259)
        ·
          refine ⟨14319207480136322186919389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9546138320090881457946259 14319207480136322186919389)
          ·
            refine ⟨5369702805051120820094771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14319207480136322186919389 5369702805051120820094771)
            ·
              refine ⟨8054554207576681230142157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5369702805051120820094771 8054554207576681230142157)
              ·
                refine ⟨3020457827841255461303309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8054554207576681230142157 3020457827841255461303309)
                ·
                  refine ⟨1132671685440470797988741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3020457827841255461303309 1132671685440470797988741)
                  ·
                    refine ⟨212375941020088274622889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1132671685440470797988741 212375941020088274622889)
                    ·
                      rfl

theorem cell22_620401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 3, 3, 4].length) (baseStart_620401 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_620401 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_620401 prefixEnd_620401 := by exact prefixLift 620401
  have htrace : WordTrace (prefixWord ++ tailWord_620401) baseStart_620401 baseEnd_620401 := by
    simpa [prefixWord, tailWord_620401, baseEnd_620401] using wordTrace_append hprefix tailTrace_620401
  have hstable : (prefixWord ++ tailWord_620401).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_620401).length < 2 ^ (prefixWord ++ tailWord_620401).sum := by decide
  have hdescent : baseEnd_620401 < baseStart_620401 := by decide
  rcases family_descends (prefixWord ++ tailWord_620401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_620433 : List Nat := [1, 2, 2, 1, 1, 1, 6, 4, 4]
def baseStart_620433 : Nat := 118140960795 + 620433 * 2 ^ 59
def prefixEnd_620433 : Nat := 4983230072969 + 3 ^ 40 * 620433 * 2
def baseEnd_620433 : Nat := 70795631758016952607597

theorem tailTrace_620433 : CollatzResearch.WordTrace tailWord_620433 prefixEnd_620433 70795631758016952607597 := by
  unfold tailWord_620433
  simp only [CollatzResearch.WordTrace]
  refine ⟨22629050561284677365481953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15086033707523118243654635 22629050561284677365481953)
  ·
    refine ⟨16971787920963508024111465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22629050561284677365481953 16971787920963508024111465)
    ·
      refine ⟨12728840940722631018083599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16971787920963508024111465 12728840940722631018083599)
      ·
        refine ⟨19093261411083946527125399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12728840940722631018083599 19093261411083946527125399)
        ·
          refine ⟨28639892116625919790688099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19093261411083946527125399 28639892116625919790688099)
          ·
            refine ⟨42959838174938879686032149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28639892116625919790688099 42959838174938879686032149)
            ·
              refine ⟨2013742414450259985282757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 42959838174938879686032149 2013742414450259985282757)
              ·
                refine ⟨377576702709423747240517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2013742414450259985282757 377576702709423747240517)
                ·
                  refine ⟨70795631758016952607597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 377576702709423747240517 70795631758016952607597)
                  ·
                    rfl

theorem cell22_620433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 6, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 6, 4, 4].length) (baseStart_620433 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_620433 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_620433 prefixEnd_620433 := by exact prefixLift 620433
  have htrace : WordTrace (prefixWord ++ tailWord_620433) baseStart_620433 baseEnd_620433 := by
    simpa [prefixWord, tailWord_620433, baseEnd_620433] using wordTrace_append hprefix tailTrace_620433
  have hstable : (prefixWord ++ tailWord_620433).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_620433).length < 2 ^ (prefixWord ++ tailWord_620433).sum := by decide
  have hdescent : baseEnd_620433 < baseStart_620433 := by decide
  rcases family_descends (prefixWord ++ tailWord_620433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_620478 : List Nat := [4, 2, 1, 1, 1, 5, 8]
def baseStart_620478 : Nat := 118140960795 + 620478 * 2 ^ 59
def prefixEnd_620478 : Nat := 4983230072969 + 3 ^ 40 * 620478 * 2
def baseEnd_620478 : Nat := 7866751840506879275839

theorem tailTrace_620478 : CollatzResearch.WordTrace tailWord_620478 prefixEnd_620478 7866751840506879275839 := by
  unfold tailWord_620478
  simp only [CollatzResearch.WordTrace]
  refine ⟨2828836480765206256358761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15087127897414433367246725 2828836480765206256358761)
  ·
    refine ⟨2121627360573904692269071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2828836480765206256358761 2121627360573904692269071)
    ·
      refine ⟨3182441040860857038403607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2121627360573904692269071 3182441040860857038403607)
      ·
        refine ⟨4773661561291285557605411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3182441040860857038403607 4773661561291285557605411)
        ·
          refine ⟨7160492341936928336408117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4773661561291285557605411 7160492341936928336408117)
          ·
            refine ⟨671296157056587031538261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 7160492341936928336408117 671296157056587031538261)
            ·
              refine ⟨7866751840506879275839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 671296157056587031538261 7866751840506879275839)
              ·
                rfl

theorem cell22_620478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 5, 8].length) (baseStart_620478 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_620478 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_620478 prefixEnd_620478 := by exact prefixLift 620478
  have htrace : WordTrace (prefixWord ++ tailWord_620478) baseStart_620478 baseEnd_620478 := by
    simpa [prefixWord, tailWord_620478, baseEnd_620478] using wordTrace_append hprefix tailTrace_620478
  have hstable : (prefixWord ++ tailWord_620478).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_620478).length < 2 ^ (prefixWord ++ tailWord_620478).sum := by decide
  have hdescent : baseEnd_620478 < baseStart_620478 := by decide
  rcases family_descends (prefixWord ++ tailWord_620478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_620491 : List Nat := [1, 1, 1, 1, 3, 4, 2, 1, 2, 6]
def baseStart_620491 : Nat := 118140960795 + 620491 * 2 ^ 59
def prefixEnd_620491 : Nat := 4983230072969 + 3 ^ 40 * 620491 * 2
def baseEnd_620491 : Nat := 212406749859358039872613

theorem tailTrace_620491 : CollatzResearch.WordTrace tailWord_620491 prefixEnd_620491 212406749859358039872613 := by
  unfold tailWord_620491
  simp only [CollatzResearch.WordTrace]
  refine ⟨22631165995074553271093327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15087443996716368847395551 22631165995074553271093327)
  ·
    refine ⟨33946748992611829906639991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22631165995074553271093327 33946748992611829906639991)
    ·
      refine ⟨50920123488917744859959987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33946748992611829906639991 50920123488917744859959987)
      ·
        refine ⟨76380185233376617289939981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50920123488917744859959987 76380185233376617289939981)
        ·
          refine ⟨28642569462516231483727493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 76380185233376617289939981 28642569462516231483727493)
          ·
            refine ⟨5370481774221793403198905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28642569462516231483727493 5370481774221793403198905)
            ·
              refine ⟨4027861330666345052399179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5370481774221793403198905 4027861330666345052399179)
              ·
                refine ⟨6041791995999517578598769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4027861330666345052399179 6041791995999517578598769)
                ·
                  refine ⟨4531343996999638183949077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6041791995999517578598769 4531343996999638183949077)
                  ·
                    refine ⟨212406749859358039872613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4531343996999638183949077 212406749859358039872613)
                    ·
                      rfl

theorem cell22_620491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 2, 1, 2, 6].length) (baseStart_620491 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_620491 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_620491 prefixEnd_620491 := by exact prefixLift 620491
  have htrace : WordTrace (prefixWord ++ tailWord_620491) baseStart_620491 baseEnd_620491 := by
    simpa [prefixWord, tailWord_620491, baseEnd_620491] using wordTrace_append hprefix tailTrace_620491
  have hstable : (prefixWord ++ tailWord_620491).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_620491).length < 2 ^ (prefixWord ++ tailWord_620491).sum := by decide
  have hdescent : baseEnd_620491 < baseStart_620491 := by decide
  rcases family_descends (prefixWord ++ tailWord_620491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_620568 : List Nat := [2, 1, 2, 3, 2, 1, 3, 2, 6]
def baseStart_620568 : Nat := 118140960795 + 620568 * 2 ^ 59
def prefixEnd_620568 : Nat := 4983230072969 + 3 ^ 40 * 620568 * 2
def baseEnd_620568 : Nat := 70811036177651835232459

theorem tailTrace_620568 : CollatzResearch.WordTrace tailWord_620568 prefixEnd_620568 70811036177651835232459 := by
  unfold tailWord_620568
  simp only [CollatzResearch.WordTrace]
  refine ⟨11316987207897797710823179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15089316277197063614430905 11316987207897797710823179)
  ·
    refine ⟨16975480811846696566234769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11316987207897797710823179 16975480811846696566234769)
    ·
      refine ⟨12731610608885022424676077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16975480811846696566234769 12731610608885022424676077)
      ·
        refine ⟨4774353978331883409253529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12731610608885022424676077 4774353978331883409253529)
        ·
          refine ⟨3580765483748912556940147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4774353978331883409253529 3580765483748912556940147)
          ·
            refine ⟨5371148225623368835410221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3580765483748912556940147 5371148225623368835410221)
            ·
              refine ⟨2014180584608763313278833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5371148225623368835410221 2014180584608763313278833)
              ·
                refine ⟨1510635438456572484959125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2014180584608763313278833 1510635438456572484959125)
                ·
                  refine ⟨70811036177651835232459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1510635438456572484959125 70811036177651835232459)
                  ·
                    rfl

theorem cell22_620568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 3, 2, 6].length) (baseStart_620568 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_620568 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_620568 prefixEnd_620568 := by exact prefixLift 620568
  have htrace : WordTrace (prefixWord ++ tailWord_620568) baseStart_620568 baseEnd_620568 := by
    simpa [prefixWord, tailWord_620568, baseEnd_620568] using wordTrace_append hprefix tailTrace_620568
  have hstable : (prefixWord ++ tailWord_620568).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_620568).length < 2 ^ (prefixWord ++ tailWord_620568).sum := by decide
  have hdescent : baseEnd_620568 < baseStart_620568 := by decide
  rcases family_descends (prefixWord ++ tailWord_620568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_620617 : List Nat := [1, 2, 1, 1, 2, 2, 7, 1, 2, 3]
def baseStart_620617 : Nat := 118140960795 + 620617 * 2 ^ 59
def prefixEnd_620617 : Nat := 4983230072969 + 3 ^ 40 * 620617 * 2
def baseEnd_620617 : Nat := 212449882234335711222227

theorem tailTrace_620617 : CollatzResearch.WordTrace tailWord_620617 prefixEnd_620617 212449882234335711222227 := by
  unfold tailWord_620617
  simp only [CollatzResearch.WordTrace]
  refine ⟨22635761592618076790180105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15090507728412051193453403 22635761592618076790180105)
  ·
    refine ⟨16976821194463557592635079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22635761592618076790180105 16976821194463557592635079)
    ·
      refine ⟨25465231791695336388952619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16976821194463557592635079 25465231791695336388952619)
      ·
        refine ⟨38197847687543004583428929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25465231791695336388952619 38197847687543004583428929)
        ·
          refine ⟨28648385765657253437571697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38197847687543004583428929 28648385765657253437571697)
          ·
            refine ⟨21486289324242940078178773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28648385765657253437571697 21486289324242940078178773)
            ·
              refine ⟨503584906036943908082315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 21486289324242940078178773 503584906036943908082315)
              ·
                refine ⟨755377359055415862123473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 503584906036943908082315 755377359055415862123473)
                ·
                  refine ⟨566533019291561896592605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 755377359055415862123473 566533019291561896592605)
                  ·
                    refine ⟨212449882234335711222227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 566533019291561896592605 212449882234335711222227)
                    ·
                      rfl

theorem cell22_620617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 7, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 7, 1, 2, 3].length) (baseStart_620617 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_620617 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_620617 prefixEnd_620617 := by exact prefixLift 620617
  have htrace : WordTrace (prefixWord ++ tailWord_620617) baseStart_620617 baseEnd_620617 := by
    simpa [prefixWord, tailWord_620617, baseEnd_620617] using wordTrace_append hprefix tailTrace_620617
  have hstable : (prefixWord ++ tailWord_620617).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_620617).length < 2 ^ (prefixWord ++ tailWord_620617).sum := by decide
  have hdescent : baseEnd_620617 < baseStart_620617 := by decide
  rcases family_descends (prefixWord ++ tailWord_620617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_620628 : List Nat := [2, 4, 1, 1, 1, 1, 1, 1, 1, 9]
def baseStart_620628 : Nat := 118140960795 + 620628 * 2 ^ 59
def prefixEnd_620628 : Nat := 4983230072969 + 3 ^ 40 * 620628 * 2
def baseEnd_620628 : Nat := 212453647759135349197193

theorem tailTrace_620628 : CollatzResearch.WordTrace tailWord_620628 prefixEnd_620628 212453647759135349197193 := by
  unfold tailWord_620628
  simp only [CollatzResearch.WordTrace]
  refine ⟨11318081397789112834415269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15090775197052150445887025 11318081397789112834415269)
  ·
    refine ⟨2122140262085458656452863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11318081397789112834415269 2122140262085458656452863)
    ·
      refine ⟨3183210393128187984679295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2122140262085458656452863 3183210393128187984679295)
      ·
        refine ⟨4774815589692281977018943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3183210393128187984679295 4774815589692281977018943)
        ·
          refine ⟨7162223384538422965528415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4774815589692281977018943 7162223384538422965528415)
          ·
            refine ⟨10743335076807634448292623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7162223384538422965528415 10743335076807634448292623)
            ·
              refine ⟨16115002615211451672438935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10743335076807634448292623 16115002615211451672438935)
              ·
                refine ⟨24172503922817177508658403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16115002615211451672438935 24172503922817177508658403)
                ·
                  refine ⟨36258755884225766262987605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24172503922817177508658403 36258755884225766262987605)
                  ·
                    refine ⟨212453647759135349197193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 36258755884225766262987605 212453647759135349197193)
                    ·
                      rfl

theorem cell22_620628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 1, 1, 9].length) (baseStart_620628 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_620628 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_620628 prefixEnd_620628 := by exact prefixLift 620628
  have htrace : WordTrace (prefixWord ++ tailWord_620628) baseStart_620628 baseEnd_620628 := by
    simpa [prefixWord, tailWord_620628, baseEnd_620628] using wordTrace_append hprefix tailTrace_620628
  have hstable : (prefixWord ++ tailWord_620628).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_620628).length < 2 ^ (prefixWord ++ tailWord_620628).sum := by decide
  have hdescent : baseEnd_620628 < baseStart_620628 := by decide
  rcases family_descends (prefixWord ++ tailWord_620628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_620675 : List Nat := [1, 1, 1, 3, 3, 4, 1, 3, 5]
def baseStart_620675 : Nat := 118140960795 + 620675 * 2 ^ 59
def prefixEnd_620675 : Nat := 4983230072969 + 3 ^ 40 * 620675 * 2
def baseEnd_620675 : Nat := 70823245606547631090683

theorem tailTrace_620675 : CollatzResearch.WordTrace tailWord_620675 prefixEnd_620675 70823245606547631090683 := by
  unfold tailWord_620675
  simp only [CollatzResearch.WordTrace]
  refine ⟨22637877026407952695791479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15091918017605301797194319 22637877026407952695791479)
  ·
    refine ⟨33956815539611929043687219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22637877026407952695791479 33956815539611929043687219)
    ·
      refine ⟨50935223309417893565530829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33956815539611929043687219 50935223309417893565530829)
      ·
        refine ⟨19100708741031710087074061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50935223309417893565530829 19100708741031710087074061)
        ·
          refine ⟨7162765777886891282652773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19100708741031710087074061 7162765777886891282652773)
          ·
            refine ⟨1343018583353792115497395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7162765777886891282652773 1343018583353792115497395)
            ·
              refine ⟨2014527875030688173246093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1343018583353792115497395 2014527875030688173246093)
              ·
                refine ⟨755447953136508064967285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2014527875030688173246093 755447953136508064967285)
                ·
                  refine ⟨70823245606547631090683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 755447953136508064967285 70823245606547631090683)
                  ·
                    rfl

theorem cell22_620675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 1, 3, 5].length) (baseStart_620675 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_620675 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_620675 prefixEnd_620675 := by exact prefixLift 620675
  have htrace : WordTrace (prefixWord ++ tailWord_620675) baseStart_620675 baseEnd_620675 := by
    simpa [prefixWord, tailWord_620675, baseEnd_620675] using wordTrace_append hprefix tailTrace_620675
  have hstable : (prefixWord ++ tailWord_620675).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_620675).length < 2 ^ (prefixWord ++ tailWord_620675).sum := by decide
  have hdescent : baseEnd_620675 < baseStart_620675 := by decide
  rcases family_descends (prefixWord ++ tailWord_620675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_620735 : List Nat := [1, 1, 2, 2, 2, 2, 1, 2, 6, 3]
def baseStart_620735 : Nat := 118140960795 + 620735 * 2 ^ 59
def prefixEnd_620735 : Nat := 4983230072969 + 3 ^ 40 * 620735 * 2
def baseEnd_620735 : Nat := 212490276045822736771865

theorem tailTrace_620735 : CollatzResearch.WordTrace tailWord_620735 prefixEnd_620735 212490276045822736771865 := by
  unfold tailWord_620735
  simp only [CollatzResearch.WordTrace]
  refine ⟨22640065406190582942975659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15093376937460388628650439 22640065406190582942975659)
  ·
    refine ⟨33960098109285874414463489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22640065406190582942975659 33960098109285874414463489)
    ·
      refine ⟨25470073581964405810847617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33960098109285874414463489 25470073581964405810847617)
      ·
        refine ⟨19102555186473304358135713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25470073581964405810847617 19102555186473304358135713)
        ·
          refine ⟨14326916389854978268601785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19102555186473304358135713 14326916389854978268601785)
          ·
            refine ⟨10745187292391233701451339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14326916389854978268601785 10745187292391233701451339)
            ·
              refine ⟨16117780938586850552177009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10745187292391233701451339 16117780938586850552177009)
              ·
                refine ⟨12088335703940137914132757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16117780938586850552177009 12088335703940137914132757)
                ·
                  refine ⟨566640736122193964724973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 12088335703940137914132757 566640736122193964724973)
                  ·
                    refine ⟨212490276045822736771865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 566640736122193964724973 212490276045822736771865)
                    ·
                      rfl

theorem cell22_620735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 2, 6, 3].length) (baseStart_620735 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_620735 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_620735 prefixEnd_620735 := by exact prefixLift 620735
  have htrace : WordTrace (prefixWord ++ tailWord_620735) baseStart_620735 baseEnd_620735 := by
    simpa [prefixWord, tailWord_620735, baseEnd_620735] using wordTrace_append hprefix tailTrace_620735
  have hstable : (prefixWord ++ tailWord_620735).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_620735).length < 2 ^ (prefixWord ++ tailWord_620735).sum := by decide
  have hdescent : baseEnd_620735 < baseStart_620735 := by decide
  rcases family_descends (prefixWord ++ tailWord_620735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_620754 : List Nat := [3, 2, 2, 2, 1, 3, 2, 3, 4]
def baseStart_620754 : Nat := 118140960795 + 620754 * 2 ^ 59
def prefixEnd_620754 : Nat := 4983230072969 + 3 ^ 40 * 620754 * 2
def baseEnd_620754 : Nat := 70832260044704340182269

theorem tailTrace_620754 : CollatzResearch.WordTrace tailWord_620754 prefixEnd_620754 70832260044704340182269 := by
  unfold tailWord_620754
  simp only [CollatzResearch.WordTrace]
  refine ⟨5660189598280437296979329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15093838928747832791944877 5660189598280437296979329)
  ·
    refine ⟨4245142198710327972734497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5660189598280437296979329 4245142198710327972734497)
    ·
      refine ⟨3183856649032745979550873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4245142198710327972734497 3183856649032745979550873)
      ·
        refine ⟨2387892486774559484663155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3183856649032745979550873 2387892486774559484663155)
        ·
          refine ⟨3581838730161839226994733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2387892486774559484663155 3581838730161839226994733)
          ·
            refine ⟨1343189523810689710123025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3581838730161839226994733 1343189523810689710123025)
            ·
              refine ⟨1007392142858017282592269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1343189523810689710123025 1007392142858017282592269)
              ·
                refine ⟨377772053571756480972101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1007392142858017282592269 377772053571756480972101)
                ·
                  refine ⟨70832260044704340182269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 377772053571756480972101 70832260044704340182269)
                  ·
                    rfl

theorem cell22_620754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 2, 3, 4].length) (baseStart_620754 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_620754 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_620754 prefixEnd_620754 := by exact prefixLift 620754
  have htrace : WordTrace (prefixWord ++ tailWord_620754) baseStart_620754 baseEnd_620754 := by
    simpa [prefixWord, tailWord_620754, baseEnd_620754] using wordTrace_append hprefix tailTrace_620754
  have hstable : (prefixWord ++ tailWord_620754).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_620754).length < 2 ^ (prefixWord ++ tailWord_620754).sum := by decide
  have hdescent : baseEnd_620754 < baseStart_620754 := by decide
  rcases family_descends (prefixWord ++ tailWord_620754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_620786 : List Nat := [3, 2, 1, 3, 2, 2, 3, 1, 2, 3]
def baseStart_620786 : Nat := 118140960795 + 620786 * 2 ^ 59
def prefixEnd_620786 : Nat := 4983230072969 + 3 ^ 40 * 620786 * 2
def baseEnd_620786 : Nat := 212507734388075603746709

theorem tailTrace_620786 : CollatzResearch.WordTrace tailWord_620786 prefixEnd_620786 212507734388075603746709 := by
  unfold tailWord_620786
  simp only [CollatzResearch.WordTrace]
  refine ⟨5660481382251454663270553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15094617019337212435388141 5660481382251454663270553)
  ·
    refine ⟨4245361036688590997452915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5660481382251454663270553 4245361036688590997452915)
    ·
      refine ⟨6368041555032886496179373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4245361036688590997452915 6368041555032886496179373)
      ·
        refine ⟨2388015583137332436067265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6368041555032886496179373 2388015583137332436067265)
        ·
          refine ⟨1791011687352999327050449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2388015583137332436067265 1791011687352999327050449)
          ·
            refine ⟨1343258765514749495287837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1791011687352999327050449 1343258765514749495287837)
            ·
              refine ⟨503722037068031060732939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1343258765514749495287837 503722037068031060732939)
              ·
                refine ⟨755583055602046591099409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 503722037068031060732939 755583055602046591099409)
                ·
                  refine ⟨566687291701534943324557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 755583055602046591099409 566687291701534943324557)
                  ·
                    refine ⟨212507734388075603746709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 566687291701534943324557 212507734388075603746709)
                    ·
                      rfl

theorem cell22_620786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 3, 1, 2, 3].length) (baseStart_620786 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_620786 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_620786 prefixEnd_620786 := by exact prefixLift 620786
  have htrace : WordTrace (prefixWord ++ tailWord_620786) baseStart_620786 baseEnd_620786 := by
    simpa [prefixWord, tailWord_620786, baseEnd_620786] using wordTrace_append hprefix tailTrace_620786
  have hstable : (prefixWord ++ tailWord_620786).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_620786).length < 2 ^ (prefixWord ++ tailWord_620786).sum := by decide
  have hdescent : baseEnd_620786 < baseStart_620786 := by decide
  rcases family_descends (prefixWord ++ tailWord_620786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_620810 : List Nat := [3, 1, 2, 2, 1, 1, 3, 2, 7]
def baseStart_620810 : Nat := 118140960795 + 620810 * 2 ^ 59
def prefixEnd_620810 : Nat := 4983230072969 + 3 ^ 40 * 620810 * 2
def baseEnd_620810 : Nat := 70838650026182513715545

theorem tailTrace_620810 : CollatzResearch.WordTrace tailWord_620810 prefixEnd_620810 70838650026182513715545 := by
  unfold tailWord_620810
  simp only [CollatzResearch.WordTrace]
  refine ⟨5660700220229717687988971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15095200587279247167970589 5660700220229717687988971)
  ·
    refine ⟨8491050330344576531983457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5660700220229717687988971 8491050330344576531983457)
    ·
      refine ⟨6368287747758432398987593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8491050330344576531983457 6368287747758432398987593)
      ·
        refine ⟨4776215810818824299240695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6368287747758432398987593 4776215810818824299240695)
        ·
          refine ⟨7164323716228236448861043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4776215810818824299240695 7164323716228236448861043)
          ·
            refine ⟨10746485574342354673291565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7164323716228236448861043 10746485574342354673291565)
            ·
              refine ⟨4029932090378383002484337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10746485574342354673291565 4029932090378383002484337)
              ·
                refine ⟨3022449067783787251863253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4029932090378383002484337 3022449067783787251863253)
                ·
                  refine ⟨70838650026182513715545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3022449067783787251863253 70838650026182513715545)
                  ·
                    rfl

theorem cell22_620810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 3, 2, 7].length) (baseStart_620810 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_620810 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_620810 prefixEnd_620810 := by exact prefixLift 620810
  have htrace : WordTrace (prefixWord ++ tailWord_620810) baseStart_620810 baseEnd_620810 := by
    simpa [prefixWord, tailWord_620810, baseEnd_620810] using wordTrace_append hprefix tailTrace_620810
  have hstable : (prefixWord ++ tailWord_620810).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_620810).length < 2 ^ (prefixWord ++ tailWord_620810).sum := by decide
  have hdescent : baseEnd_620810 < baseStart_620810 := by decide
  rcases family_descends (prefixWord ++ tailWord_620810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_620855 : List Nat := [1, 1, 3, 1, 2, 1, 1, 6, 6]
def baseStart_620855 : Nat := 118140960795 + 620855 * 2 ^ 59
def prefixEnd_620855 : Nat := 4983230072969 + 3 ^ 40 * 620855 * 2
def baseEnd_620855 : Nat := 70843784832727474590499

theorem tailTrace_620855 : CollatzResearch.WordTrace tailWord_620855 prefixEnd_620855 70843784832727474590499 := by
  unfold tailWord_620855
  simp only [CollatzResearch.WordTrace]
  refine ⟨22644442165755843437344019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15096294777170562291562679 22644442165755843437344019)
  ·
    refine ⟨33966663248633765156016029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22644442165755843437344019 33966663248633765156016029)
    ·
      refine ⟨12737498718237661933506011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33966663248633765156016029 12737498718237661933506011)
      ·
        refine ⟨19106248077356492900259017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12737498718237661933506011 19106248077356492900259017)
        ·
          refine ⟨14329686058017369675194263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19106248077356492900259017 14329686058017369675194263)
          ·
            refine ⟨21494529087026054512791395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14329686058017369675194263 21494529087026054512791395)
            ·
              refine ⟨32241793630539081769187093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21494529087026054512791395 32241793630539081769187093)
              ·
                refine ⟨1511334076431519457930645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 32241793630539081769187093 1511334076431519457930645)
                ·
                  refine ⟨70843784832727474590499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1511334076431519457930645 70843784832727474590499)
                  ·
                    rfl

theorem cell22_620855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 6, 6].length) (baseStart_620855 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_620855 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_620855 prefixEnd_620855 := by exact prefixLift 620855
  have htrace : WordTrace (prefixWord ++ tailWord_620855) baseStart_620855 baseEnd_620855 := by
    simpa [prefixWord, tailWord_620855, baseEnd_620855] using wordTrace_append hprefix tailTrace_620855
  have hstable : (prefixWord ++ tailWord_620855).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_620855).length < 2 ^ (prefixWord ++ tailWord_620855).sum := by decide
  have hdescent : baseEnd_620855 < baseStart_620855 := by decide
  rcases family_descends (prefixWord ++ tailWord_620855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_620904 : List Nat := [2, 1, 4, 2, 2, 2, 2, 1, 1, 5]
def baseStart_620904 : Nat := 118140960795 + 620904 * 2 ^ 59
def prefixEnd_620904 : Nat := 4983230072969 + 3 ^ 40 * 620904 * 2
def baseEnd_620904 : Nat := 212548128199562629296347

theorem tailTrace_620904 : CollatzResearch.WordTrace tailWord_620904 prefixEnd_620904 212548128199562629296347 := by
  unfold tailWord_620904
  simp only [CollatzResearch.WordTrace]
  refine ⟨11323114671289162402938883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15097486228385549870585177 11323114671289162402938883)
  ·
    refine ⟨16984672006933743604408325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11323114671289162402938883 16984672006933743604408325)
    ·
      refine ⟨3184626001300076925826561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16984672006933743604408325 3184626001300076925826561)
      ·
        refine ⟨2388469500975057694369921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3184626001300076925826561 2388469500975057694369921)
        ·
          refine ⟨1791352125731293270777441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2388469500975057694369921 1791352125731293270777441)
          ·
            refine ⟨1343514094298469953083081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1791352125731293270777441 1343514094298469953083081)
            ·
              refine ⟨1007635570723852464812311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1343514094298469953083081 1007635570723852464812311)
              ·
                refine ⟨1511453356085778697218467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1007635570723852464812311 1511453356085778697218467)
                ·
                  refine ⟨2267180034128668045827701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1511453356085778697218467 2267180034128668045827701)
                  ·
                    refine ⟨212548128199562629296347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2267180034128668045827701 212548128199562629296347)
                    ·
                      rfl

theorem cell22_620904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 2, 1, 1, 5].length) (baseStart_620904 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_620904 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_620904 prefixEnd_620904 := by exact prefixLift 620904
  have htrace : WordTrace (prefixWord ++ tailWord_620904) baseStart_620904 baseEnd_620904 := by
    simpa [prefixWord, tailWord_620904, baseEnd_620904] using wordTrace_append hprefix tailTrace_620904
  have hstable : (prefixWord ++ tailWord_620904).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_620904).length < 2 ^ (prefixWord ++ tailWord_620904).sum := by decide
  have hdescent : baseEnd_620904 < baseStart_620904 := by decide
  rcases family_descends (prefixWord ++ tailWord_620904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_620915 : List Nat := [1, 1, 1, 2, 2, 1, 2, 3, 2, 7]
def baseStart_620915 : Nat := 118140960795 + 620915 * 2 ^ 59
def prefixEnd_620915 : Nat := 4983230072969 + 3 ^ 40 * 620915 * 2
def baseEnd_620915 : Nat := 212551893724362267271313

theorem tailTrace_620915 : CollatzResearch.WordTrace tailWord_620915 prefixEnd_620915 212551893724362267271313 := by
  unfold tailWord_620915
  simp only [CollatzResearch.WordTrace]
  refine ⟨22646630545538473684528199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15097753697025649123018799 22646630545538473684528199)
  ·
    refine ⟨33969945818307710526792299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22646630545538473684528199 33969945818307710526792299)
    ·
      refine ⟨50954918727461565790188449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33969945818307710526792299 50954918727461565790188449)
      ·
        refine ⟨38216189045596174342641337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50954918727461565790188449 38216189045596174342641337)
        ·
          refine ⟨28662141784197130756981003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38216189045596174342641337 28662141784197130756981003)
          ·
            refine ⟨42993212676295696135471505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28662141784197130756981003 42993212676295696135471505)
            ·
              refine ⟨32244909507221772101603629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42993212676295696135471505 32244909507221772101603629)
              ·
                refine ⟨12091841065208164538101361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32244909507221772101603629 12091841065208164538101361)
                ·
                  refine ⟨9068880798906123403576021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12091841065208164538101361 9068880798906123403576021)
                  ·
                    refine ⟨212551893724362267271313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 9068880798906123403576021 212551893724362267271313)
                    ·
                      rfl

theorem cell22_620915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 3, 2, 7].length) (baseStart_620915 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_620915 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_620915 prefixEnd_620915 := by exact prefixLift 620915
  have htrace : WordTrace (prefixWord ++ tailWord_620915) baseStart_620915 baseEnd_620915 := by
    simpa [prefixWord, tailWord_620915, baseEnd_620915] using wordTrace_append hprefix tailTrace_620915
  have hstable : (prefixWord ++ tailWord_620915).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_620915).length < 2 ^ (prefixWord ++ tailWord_620915).sum := by decide
  have hdescent : baseEnd_620915 < baseStart_620915 := by decide
  rcases family_descends (prefixWord ++ tailWord_620915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_620983 : List Nat := [1, 1, 3, 1, 3, 5, 1, 3, 1, 3]
def baseStart_620983 : Nat := 118140960795 + 620983 * 2 ^ 59
def prefixEnd_620983 : Nat := 4983230072969 + 3 ^ 40 * 620983 * 2
def baseEnd_620983 : Nat := 212575171514032756571105

theorem tailTrace_620983 : CollatzResearch.WordTrace tailWord_620983 prefixEnd_620983 212575171514032756571105 := by
  unfold tailWord_620983
  simp only [CollatzResearch.WordTrace]
  refine ⟨22649110709292121298003603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15099407139528080865335735 22649110709292121298003603)
  ·
    refine ⟨33973666063938181947005405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22649110709292121298003603 33973666063938181947005405)
    ·
      refine ⟨12740124773976818230127027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33973666063938181947005405 12740124773976818230127027)
      ·
        refine ⟨19110187160965227345190541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12740124773976818230127027 19110187160965227345190541)
        ·
          refine ⟨7166320185361960254446453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19110187160965227345190541 7166320185361960254446453)
          ·
            refine ⟨671842517377683773854355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 7166320185361960254446453 671842517377683773854355)
            ·
              refine ⟨1007763776066525660781533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 671842517377683773854355 1007763776066525660781533)
              ·
                refine ⟨377911416024947122793075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1007763776066525660781533 377911416024947122793075)
                ·
                  refine ⟨566867124037420684189613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 377911416024947122793075 566867124037420684189613)
                  ·
                    refine ⟨212575171514032756571105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 566867124037420684189613 212575171514032756571105)
                    ·
                      rfl

theorem cell22_620983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 5, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 5, 1, 3, 1, 3].length) (baseStart_620983 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_620983 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_620983 prefixEnd_620983 := by exact prefixLift 620983
  have htrace : WordTrace (prefixWord ++ tailWord_620983) baseStart_620983 baseEnd_620983 := by
    simpa [prefixWord, tailWord_620983, baseEnd_620983] using wordTrace_append hprefix tailTrace_620983
  have hstable : (prefixWord ++ tailWord_620983).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_620983).length < 2 ^ (prefixWord ++ tailWord_620983).sum := by decide
  have hdescent : baseEnd_620983 < baseStart_620983 := by decide
  rcases family_descends (prefixWord ++ tailWord_620983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_620992 : List Nat := [2, 1, 1, 2, 3, 1, 1, 2, 5, 4]
def baseStart_620992 : Nat := 118140960795 + 620992 * 2 ^ 59
def prefixEnd_620992 : Nat := 4983230072969 + 3 ^ 40 * 620992 * 2
def baseEnd_620992 : Nat := 212578252397959733096077

theorem tailTrace_620992 : CollatzResearch.WordTrace tailWord_620992 prefixEnd_620992 212578252397959733096077 := by
  unfold tailWord_620992
  simp only [CollatzResearch.WordTrace]
  refine ⟨11324719483129757917540615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15099625977506343890054153 11324719483129757917540615)
  ·
    refine ⟨16987079224694636876310923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11324719483129757917540615 16987079224694636876310923)
    ·
      refine ⟨25480618837041955314466385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16987079224694636876310923 25480618837041955314466385)
      ·
        refine ⟨19110464127781466485849789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25480618837041955314466385 19110464127781466485849789)
        ·
          refine ⟨7166424047918049932193671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19110464127781466485849789 7166424047918049932193671)
          ·
            refine ⟨10749636071877074898290507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7166424047918049932193671 10749636071877074898290507)
            ·
              refine ⟨16124454107815612347435761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10749636071877074898290507 16124454107815612347435761)
              ·
                refine ⟨12093340580861709260576821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16124454107815612347435761 12093340580861709260576821)
                ·
                  refine ⟨1133750679455785243179077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 12093340580861709260576821 1133750679455785243179077)
                  ·
                    refine ⟨212578252397959733096077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1133750679455785243179077 212578252397959733096077)
                    ·
                      rfl

theorem cell22_620992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 2, 5, 4].length) (baseStart_620992 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_620992 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_620992 prefixEnd_620992 := by exact prefixLift 620992
  have htrace : WordTrace (prefixWord ++ tailWord_620992) baseStart_620992 baseEnd_620992 := by
    simpa [prefixWord, tailWord_620992, baseEnd_620992] using wordTrace_append hprefix tailTrace_620992
  have hstable : (prefixWord ++ tailWord_620992).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_620992).length < 2 ^ (prefixWord ++ tailWord_620992).sum := by decide
  have hdescent : baseEnd_620992 < baseStart_620992 := by decide
  rcases family_descends (prefixWord ++ tailWord_620992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_621088 : List Nat := [2, 1, 1, 6, 2, 2, 1, 1, 2, 4]
def baseStart_621088 : Nat := 118140960795 + 621088 * 2 ^ 59
def prefixEnd_621088 : Nat := 4983230072969 + 3 ^ 40 * 621088 * 2
def baseEnd_621088 : Nat := 212611115159847482695783

theorem tailTrace_621088 : CollatzResearch.WordTrace tailWord_621088 prefixEnd_621088 212611115159847482695783 := by
  unfold tailWord_621088
  simp only [CollatzResearch.WordTrace]
  refine ⟨11326470186955862115287959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15101960249274482820383945 11326470186955862115287959)
  ·
    refine ⟨16989705280433793172931939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11326470186955862115287959 16989705280433793172931939)
    ·
      refine ⟨25484557920650689759397909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16989705280433793172931939 25484557920650689759397909)
      ·
        refine ⟨1194588652530501082471777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 25484557920650689759397909 1194588652530501082471777)
        ·
          refine ⟨895941489397875811853833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1194588652530501082471777 895941489397875811853833)
          ·
            refine ⟨671956117048406858890375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 895941489397875811853833 671956117048406858890375)
            ·
              refine ⟨1007934175572610288335563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 671956117048406858890375 1007934175572610288335563)
              ·
                refine ⟨1511901263358915432503345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1007934175572610288335563 1511901263358915432503345)
                ·
                  refine ⟨1133925947519186574377509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1511901263358915432503345 1133925947519186574377509)
                  ·
                    refine ⟨212611115159847482695783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1133925947519186574377509 212611115159847482695783)
                    ·
                      rfl

theorem cell22_621088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 2, 1, 1, 2, 4].length) (baseStart_621088 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_621088 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_621088 prefixEnd_621088 := by exact prefixLift 621088
  have htrace : WordTrace (prefixWord ++ tailWord_621088) baseStart_621088 baseEnd_621088 := by
    simpa [prefixWord, tailWord_621088, baseEnd_621088] using wordTrace_append hprefix tailTrace_621088
  have hstable : (prefixWord ++ tailWord_621088).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_621088).length < 2 ^ (prefixWord ++ tailWord_621088).sum := by decide
  have hdescent : baseEnd_621088 < baseStart_621088 := by decide
  rcases family_descends (prefixWord ++ tailWord_621088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_621114 : List Nat := [3, 1, 1, 1, 3, 4, 1, 1, 7]
def baseStart_621114 : Nat := 118140960795 + 621114 * 2 ^ 59
def prefixEnd_621114 : Nat := 4983230072969 + 3 ^ 40 * 621114 * 2
def baseEnd_621114 : Nat := 70873338497064027181901

theorem tailTrace_621114 : CollatzResearch.WordTrace tailWord_621114 prefixEnd_621114 70873338497064027181901 := by
  unfold tailWord_621114
  simp only [CollatzResearch.WordTrace]
  refine ⟨5663472167954382667755599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15102592447878353780681597 5663472167954382667755599)
  ·
    refine ⟨8495208251931574001633399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5663472167954382667755599 8495208251931574001633399)
    ·
      refine ⟨12742812377897361002450099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8495208251931574001633399 12742812377897361002450099)
      ·
        refine ⟨19114218566846041503675149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12742812377897361002450099 19114218566846041503675149)
        ·
          refine ⟨7167831962567265563878181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19114218566846041503675149 7167831962567265563878181)
          ·
            refine ⟨1343968492981362293227159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7167831962567265563878181 1343968492981362293227159)
            ·
              refine ⟨2015952739472043439840739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1343968492981362293227159 2015952739472043439840739)
              ·
                refine ⟨3023929109208065159761109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2015952739472043439840739 3023929109208065159761109)
                ·
                  refine ⟨70873338497064027181901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3023929109208065159761109 70873338497064027181901)
                  ·
                    rfl

theorem cell22_621114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 1, 1, 7].length) (baseStart_621114 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_621114 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_621114 prefixEnd_621114 := by exact prefixLift 621114
  have htrace : WordTrace (prefixWord ++ tailWord_621114) baseStart_621114 baseEnd_621114 := by
    simpa [prefixWord, tailWord_621114, baseEnd_621114] using wordTrace_append hprefix tailTrace_621114
  have hstable : (prefixWord ++ tailWord_621114).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_621114).length < 2 ^ (prefixWord ++ tailWord_621114).sum := by decide
  have hdescent : baseEnd_621114 < baseStart_621114 := by decide
  rcases family_descends (prefixWord ++ tailWord_621114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_621124 : List Nat := [2, 3, 5, 1, 1, 1, 3, 1, 2, 3]
def baseStart_621124 : Nat := 118140960795 + 621124 * 2 ^ 59
def prefixEnd_621124 : Nat := 4983230072969 + 3 ^ 40 * 621124 * 2
def baseEnd_621124 : Nat := 212623438695555388795673

theorem tailTrace_621124 : CollatzResearch.WordTrace tailWord_621124 prefixEnd_621124 212623438695555388795673 := by
  unfold tailWord_621124
  simp only [CollatzResearch.WordTrace]
  refine ⟨11327126700890651189443213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15102835601187534919257617 11327126700890651189443213)
  ·
    refine ⟨4247672512833994196041205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11327126700890651189443213 4247672512833994196041205)
    ·
      refine ⟨398219298078186955878863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 4247672512833994196041205 398219298078186955878863)
      ·
        refine ⟨597328947117280433818295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 398219298078186955878863 597328947117280433818295)
        ·
          refine ⟨895993420675920650727443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 597328947117280433818295 895993420675920650727443)
          ·
            refine ⟨1343990131013880976091165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 895993420675920650727443 1343990131013880976091165)
            ·
              refine ⟨503996299130205366034187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1343990131013880976091165 503996299130205366034187)
              ·
                refine ⟨755994448695308049051281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 503996299130205366034187 755994448695308049051281)
                ·
                  refine ⟨566995836521481036788461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 755994448695308049051281 566995836521481036788461)
                  ·
                    refine ⟨212623438695555388795673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 566995836521481036788461 212623438695555388795673)
                    ·
                      rfl

theorem cell22_621124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 3, 1, 2, 3].length) (baseStart_621124 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_621124 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_621124 prefixEnd_621124 := by exact prefixLift 621124
  have htrace : WordTrace (prefixWord ++ tailWord_621124) baseStart_621124 baseEnd_621124 := by
    simpa [prefixWord, tailWord_621124, baseEnd_621124] using wordTrace_append hprefix tailTrace_621124
  have hstable : (prefixWord ++ tailWord_621124).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_621124).length < 2 ^ (prefixWord ++ tailWord_621124).sum := by decide
  have hdescent : baseEnd_621124 < baseStart_621124 := by decide
  rcases family_descends (prefixWord ++ tailWord_621124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_621144 : List Nat := [2, 1, 2, 2, 1, 2, 2, 3, 3, 4]
def baseStart_621144 : Nat := 118140960795 + 621144 * 2 ^ 59
def prefixEnd_621144 : Nat := 4983230072969 + 3 ^ 40 * 621144 * 2
def baseEnd_621144 : Nat := 212630285104282003295611

theorem tailTrace_621144 : CollatzResearch.WordTrace tailWord_621144 prefixEnd_621144 212630285104282003295611 := by
  unfold tailWord_621144
  simp only [CollatzResearch.WordTrace]
  refine ⟨11327491430854422897307243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15103321907805897196409657 11327491430854422897307243)
  ·
    refine ⟨16991237146281634345960865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11327491430854422897307243 16991237146281634345960865)
    ·
      refine ⟨12743427859711225759470649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16991237146281634345960865 12743427859711225759470649)
      ·
        refine ⟨9557570894783419319602987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12743427859711225759470649 9557570894783419319602987)
        ·
          refine ⟨14336356342175128979404481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9557570894783419319602987 14336356342175128979404481)
          ·
            refine ⟨10752267256631346734553361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14336356342175128979404481 10752267256631346734553361)
            ·
              refine ⟨8064200442473510050915021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10752267256631346734553361 8064200442473510050915021)
              ·
                refine ⟨3024075165927566269093133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8064200442473510050915021 3024075165927566269093133)
                ·
                  refine ⟨1134028187222837350909925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3024075165927566269093133 1134028187222837350909925)
                  ·
                    refine ⟨212630285104282003295611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1134028187222837350909925 212630285104282003295611)
                    ·
                      rfl

theorem cell22_621144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 3, 3, 4].length) (baseStart_621144 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_621144 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_621144 prefixEnd_621144 := by exact prefixLift 621144
  have htrace : WordTrace (prefixWord ++ tailWord_621144) baseStart_621144 baseEnd_621144 := by
    simpa [prefixWord, tailWord_621144, baseEnd_621144] using wordTrace_append hprefix tailTrace_621144
  have hstable : (prefixWord ++ tailWord_621144).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_621144).length < 2 ^ (prefixWord ++ tailWord_621144).sum := by decide
  have hdescent : baseEnd_621144 < baseStart_621144 := by decide
  rcases family_descends (prefixWord ++ tailWord_621144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_621281 : List Nat := [1, 2, 3, 1, 4, 1, 1, 2, 2, 5]
def baseStart_621281 : Nat := 118140960795 + 621281 * 2 ^ 59
def prefixEnd_621281 : Nat := 4983230072969 + 3 ^ 40 * 621281 * 2
def baseEnd_621281 : Nat := 212677183004059312620191

theorem tailTrace_621281 : CollatzResearch.WordTrace tailWord_621281 prefixEnd_621281 212677183004059312620191 := by
  unfold tailWord_621281
  simp only [CollatzResearch.WordTrace]
  refine ⟨22659979662212518192351697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15106653108141678794901131 22659979662212518192351697)
  ·
    refine ⟨16994984746659388644263773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22659979662212518192351697 16994984746659388644263773)
    ·
      refine ⟨6373119279997270741598915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16994984746659388644263773 6373119279997270741598915)
      ·
        refine ⟨9559678919995906112398373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6373119279997270741598915 9559678919995906112398373)
        ·
          refine ⟨1792439797499232396074695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9559678919995906112398373 1792439797499232396074695)
          ·
            refine ⟨2688659696248848594112043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1792439797499232396074695 2688659696248848594112043)
            ·
              refine ⟨4032989544373272891168065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2688659696248848594112043 4032989544373272891168065)
              ·
                refine ⟨3024742158279954668376049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4032989544373272891168065 3024742158279954668376049)
                ·
                  refine ⟨2268556618709966001282037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3024742158279954668376049 2268556618709966001282037)
                  ·
                    refine ⟨212677183004059312620191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2268556618709966001282037 212677183004059312620191)
                    ·
                      rfl

theorem cell22_621281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 1, 2, 2, 5].length) (baseStart_621281 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_621281 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_621281 prefixEnd_621281 := by exact prefixLift 621281
  have htrace : WordTrace (prefixWord ++ tailWord_621281) baseStart_621281 baseEnd_621281 := by
    simpa [prefixWord, tailWord_621281, baseEnd_621281] using wordTrace_append hprefix tailTrace_621281
  have hstable : (prefixWord ++ tailWord_621281).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_621281).length < 2 ^ (prefixWord ++ tailWord_621281).sum := by decide
  have hdescent : baseEnd_621281 < baseStart_621281 := by decide
  rcases family_descends (prefixWord ++ tailWord_621281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_621283 : List Nat := [1, 1, 1, 7, 1, 1, 3, 2, 5]
def baseStart_621283 : Nat := 118140960795 + 621283 * 2 ^ 59
def prefixEnd_621283 : Nat := 4983230072969 + 3 ^ 40 * 621283 * 2
def baseEnd_621283 : Nat := 70892622548310658023395

theorem tailTrace_621283 : CollatzResearch.WordTrace tailWord_621283 prefixEnd_621283 70892622548310658023395 := by
  unfold tailWord_621283
  simp only [CollatzResearch.WordTrace]
  refine ⟨22660052608205272533924503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15106701738803515022616335 22660052608205272533924503)
  ·
    refine ⟨33990078912307908800886755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22660052608205272533924503 33990078912307908800886755)
    ·
      refine ⟨50985118368461863201330133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33990078912307908800886755 50985118368461863201330133)
      ·
        refine ⟨1194963711760824918781175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 50985118368461863201330133 1194963711760824918781175)
        ·
          refine ⟨1792445567641237378171763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1194963711760824918781175 1792445567641237378171763)
          ·
            refine ⟨2688668351461856067257645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1792445567641237378171763 2688668351461856067257645)
            ·
              refine ⟨1008250631798196025221617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2688668351461856067257645 1008250631798196025221617)
              ·
                refine ⟨756187973848647018916213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1008250631798196025221617 756187973848647018916213)
                ·
                  refine ⟨70892622548310658023395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 756187973848647018916213 70892622548310658023395)
                  ·
                    rfl

theorem cell22_621283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 3, 2, 5].length) (baseStart_621283 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_621283 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_621283 prefixEnd_621283 := by exact prefixLift 621283
  have htrace : WordTrace (prefixWord ++ tailWord_621283) baseStart_621283 baseEnd_621283 := by
    simpa [prefixWord, tailWord_621283, baseEnd_621283] using wordTrace_append hprefix tailTrace_621283
  have hstable : (prefixWord ++ tailWord_621283).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_621283).length < 2 ^ (prefixWord ++ tailWord_621283).sum := by decide
  have hdescent : baseEnd_621283 < baseStart_621283 := by decide
  rcases family_descends (prefixWord ++ tailWord_621283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_621326 : List Nat := [4, 1, 1, 2, 1, 1, 1, 3, 3, 5]
def baseStart_621326 : Nat := 118140960795 + 621326 * 2 ^ 59
def prefixEnd_621326 : Nat := 4983230072969 + 3 ^ 40 * 621326 * 2
def baseEnd_621326 : Nat := 212692587423694195245053

theorem tailTrace_621326 : CollatzResearch.WordTrace tailWord_621326 prefixEnd_621326 212692587423694195245053 := by
  unfold tailWord_621326
  simp only [CollatzResearch.WordTrace]
  refine ⟨2832702618381186359717479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15107747298032993918493221 2832702618381186359717479)
  ·
    refine ⟨4249053927571779539576219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2832702618381186359717479 4249053927571779539576219)
    ·
      refine ⟨6373580891357669309364329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4249053927571779539576219 6373580891357669309364329)
      ·
        refine ⟨4780185668518251982023247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6373580891357669309364329 4780185668518251982023247)
        ·
          refine ⟨7170278502777377973034871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4780185668518251982023247 7170278502777377973034871)
          ·
            refine ⟨10755417754166066959552307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7170278502777377973034871 10755417754166066959552307)
            ·
              refine ⟨16133126631249100439328461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10755417754166066959552307 16133126631249100439328461)
              ·
                refine ⟨6049922486718412664748173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16133126631249100439328461 6049922486718412664748173)
                ·
                  refine ⟨2268720932519404749280565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6049922486718412664748173 2268720932519404749280565)
                  ·
                    refine ⟨212692587423694195245053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2268720932519404749280565 212692587423694195245053)
                    ·
                      rfl

theorem cell22_621326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 3, 3, 5].length) (baseStart_621326 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_621326 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_621326 prefixEnd_621326 := by exact prefixLift 621326
  have htrace : WordTrace (prefixWord ++ tailWord_621326) baseStart_621326 baseEnd_621326 := by
    simpa [prefixWord, tailWord_621326, baseEnd_621326] using wordTrace_append hprefix tailTrace_621326
  have hstable : (prefixWord ++ tailWord_621326).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_621326).length < 2 ^ (prefixWord ++ tailWord_621326).sum := by decide
  have hdescent : baseEnd_621326 < baseStart_621326 := by decide
  rcases family_descends (prefixWord ++ tailWord_621326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_621343 : List Nat := [1, 1, 2, 4, 2, 2, 2, 1, 4, 3]
def baseStart_621343 : Nat := 118140960795 + 621343 * 2 ^ 59
def prefixEnd_621343 : Nat := 4983230072969 + 3 ^ 40 * 621343 * 2
def baseEnd_621343 : Nat := 212698406871111817570001

theorem tailTrace_621343 : CollatzResearch.WordTrace tailWord_621343 prefixEnd_621343 212698406871111817570001 := by
  unfold tailWord_621343
  simp only [CollatzResearch.WordTrace]
  refine ⟨22662240987987902781108683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15108160658658601854072455 22662240987987902781108683)
  ·
    refine ⟨33993361481981854171663025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22662240987987902781108683 33993361481981854171663025)
    ·
      refine ⟨25495021111486390628747269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33993361481981854171663025 25495021111486390628747269)
      ·
        refine ⟨4780316458403698242890113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25495021111486390628747269 4780316458403698242890113)
        ·
          refine ⟨3585237343802773682167585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4780316458403698242890113 3585237343802773682167585)
          ·
            refine ⟨2688928007852080261625689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3585237343802773682167585 2688928007852080261625689)
            ·
              refine ⟨2016696005889060196219267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2688928007852080261625689 2016696005889060196219267)
              ·
                refine ⟨3025044008833590294328901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2016696005889060196219267 3025044008833590294328901)
                ·
                  refine ⟨567195751656298180186669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3025044008833590294328901 567195751656298180186669)
                  ·
                    refine ⟨212698406871111817570001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 567195751656298180186669 212698406871111817570001)
                    ·
                      rfl

theorem cell22_621343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 2, 1, 4, 3].length) (baseStart_621343 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_621343 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_621343 prefixEnd_621343 := by exact prefixLift 621343
  have htrace : WordTrace (prefixWord ++ tailWord_621343) baseStart_621343 baseEnd_621343 := by
    simpa [prefixWord, tailWord_621343, baseEnd_621343] using wordTrace_append hprefix tailTrace_621343
  have hstable : (prefixWord ++ tailWord_621343).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_621343).length < 2 ^ (prefixWord ++ tailWord_621343).sum := by decide
  have hdescent : baseEnd_621343 < baseStart_621343 := by decide
  rcases family_descends (prefixWord ++ tailWord_621343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_621345 : List Nat := [1, 2, 3, 2, 1, 2, 5, 2, 4]
def baseStart_621345 : Nat := 118140960795 + 621345 * 2 ^ 59
def prefixEnd_621345 : Nat := 4983230072969 + 3 ^ 40 * 621345 * 2
def baseEnd_621345 : Nat := 70899697170661493006665

theorem tailTrace_621345 : CollatzResearch.WordTrace tailWord_621345 prefixEnd_621345 70899697170661493006665 := by
  unfold tailWord_621345
  simp only [CollatzResearch.WordTrace]
  refine ⟨22662313933980657122681489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15108209289320438081787659 22662313933980657122681489)
  ·
    refine ⟨16996735450485492842011117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22662313933980657122681489 16996735450485492842011117)
    ·
      refine ⟨6373775793932059815754169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16996735450485492842011117 6373775793932059815754169)
      ·
        refine ⟨4780331845449044861815627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6373775793932059815754169 4780331845449044861815627)
        ·
          refine ⟨7170497768173567292723441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4780331845449044861815627 7170497768173567292723441)
          ·
            refine ⟨5377873326130175469542581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7170497768173567292723441 5377873326130175469542581)
            ·
              refine ⟨504175624324703950269617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5377873326130175469542581 504175624324703950269617)
              ·
                refine ⟨378131718243527962702213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 504175624324703950269617 378131718243527962702213)
                ·
                  refine ⟨70899697170661493006665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 378131718243527962702213 70899697170661493006665)
                  ·
                    rfl

theorem cell22_621345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 5, 2, 4].length) (baseStart_621345 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_621345 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_621345 prefixEnd_621345 := by exact prefixLift 621345
  have htrace : WordTrace (prefixWord ++ tailWord_621345) baseStart_621345 baseEnd_621345 := by
    simpa [prefixWord, tailWord_621345, baseEnd_621345] using wordTrace_append hprefix tailTrace_621345
  have hstable : (prefixWord ++ tailWord_621345).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_621345).length < 2 ^ (prefixWord ++ tailWord_621345).sum := by decide
  have hdescent : baseEnd_621345 < baseStart_621345 := by decide
  rcases family_descends (prefixWord ++ tailWord_621345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_621356 : List Nat := [2, 2, 1, 1, 1, 4, 4, 7]
def baseStart_621356 : Nat := 118140960795 + 621356 * 2 ^ 59
def prefixEnd_621356 : Nat := 4983230072969 + 3 ^ 40 * 621356 * 2
def baseEnd_621356 : Nat := 23633650781864901888329

theorem tailTrace_621356 : CollatzResearch.WordTrace tailWord_621356 prefixEnd_621356 23633650781864901888329 := by
  unfold tailWord_621356
  simp only [CollatzResearch.WordTrace]
  refine ⟨11331357568470403000665961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15108476757960537334221281 11331357568470403000665961)
  ·
    refine ⟨8498518176352802250499471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11331357568470403000665961 8498518176352802250499471)
    ·
      refine ⟨12747777264529203375749207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8498518176352802250499471 12747777264529203375749207)
      ·
        refine ⟨19121665896793805063623811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12747777264529203375749207 19121665896793805063623811)
        ·
          refine ⟨28682498845190707595435717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19121665896793805063623811 28682498845190707595435717)
          ·
            refine ⟨5377968533473257674144197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28682498845190707595435717 5377968533473257674144197)
            ·
              refine ⟨1008369100026235813902037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5377968533473257674144197 1008369100026235813902037)
              ·
                refine ⟨23633650781864901888329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1008369100026235813902037 23633650781864901888329)
                ·
                  rfl

theorem cell22_621356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 4, 7].length) (baseStart_621356 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_621356 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_621356 prefixEnd_621356 := by exact prefixLift 621356
  have htrace : WordTrace (prefixWord ++ tailWord_621356) baseStart_621356 baseEnd_621356 := by
    simpa [prefixWord, tailWord_621356, baseEnd_621356] using wordTrace_append hprefix tailTrace_621356
  have hstable : (prefixWord ++ tailWord_621356).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_621356).length < 2 ^ (prefixWord ++ tailWord_621356).sum := by decide
  have hdescent : baseEnd_621356 < baseStart_621356 := by decide
  rcases family_descends (prefixWord ++ tailWord_621356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_621364 : List Nat := [2, 5, 1, 1, 4, 1, 1, 2, 1, 4]
def baseStart_621364 : Nat := 118140960795 + 621364 * 2 ^ 59
def prefixEnd_621364 : Nat := 4983230072969 + 3 ^ 40 * 621364 * 2
def baseEnd_621364 : Nat := 212705595600274762794937

theorem tailTrace_621364 : CollatzResearch.WordTrace tailWord_621364 prefixEnd_621364 212705595600274762794937 := by
  unfold tailWord_621364
  simp only [CollatzResearch.WordTrace]
  refine ⟨11331503460455911683811573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15108671280607882245082097 11331503460455911683811573)
  ·
    refine ⟨1062328449417741720357335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 11331503460455911683811573 1062328449417741720357335)
    ·
      refine ⟨1593492674126612580536003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1062328449417741720357335 1593492674126612580536003)
      ·
        refine ⟨2390239011189918870804005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1593492674126612580536003 2390239011189918870804005)
        ·
          refine ⟨448169814598109788275751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2390239011189918870804005 448169814598109788275751)
          ·
            refine ⟨672254721897164682413627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 448169814598109788275751 672254721897164682413627)
            ·
              refine ⟨1008382082845747023620441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 672254721897164682413627 1008382082845747023620441)
              ·
                refine ⟨756286562134310267715331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1008382082845747023620441 756286562134310267715331)
                ·
                  refine ⟨1134429843201465401572997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 756286562134310267715331 1134429843201465401572997)
                  ·
                    refine ⟨212705595600274762794937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1134429843201465401572997 212705595600274762794937)
                    ·
                      rfl

theorem cell22_621364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 4, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 4, 1, 1, 2, 1, 4].length) (baseStart_621364 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_621364 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_621364 prefixEnd_621364 := by exact prefixLift 621364
  have htrace : WordTrace (prefixWord ++ tailWord_621364) baseStart_621364 baseEnd_621364 := by
    simpa [prefixWord, tailWord_621364, baseEnd_621364] using wordTrace_append hprefix tailTrace_621364
  have hstable : (prefixWord ++ tailWord_621364).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_621364).length < 2 ^ (prefixWord ++ tailWord_621364).sum := by decide
  have hdescent : baseEnd_621364 < baseStart_621364 := by decide
  rcases family_descends (prefixWord ++ tailWord_621364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_621422 : List Nat := [4, 1, 2, 3, 2, 1, 1, 2, 3, 3]
def baseStart_621422 : Nat := 118140960795 + 621422 * 2 ^ 59
def prefixEnd_621422 : Nat := 4983230072969 + 3 ^ 40 * 621422 * 2
def baseEnd_621422 : Nat := 212725450185581944844759

theorem tailTrace_621422 : CollatzResearch.WordTrace tailWord_621422 prefixEnd_621422 212725450185581944844759 := by
  unfold tailWord_621422
  simp only [CollatzResearch.WordTrace]
  refine ⟨2833140294337712409154315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15110081569801132848823013 2833140294337712409154315)
  ·
    refine ⟨4249710441506568613731473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2833140294337712409154315 4249710441506568613731473)
    ·
      refine ⟨3187282831129926460298605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4249710441506568613731473 3187282831129926460298605)
      ·
        refine ⟨1195231061673722422611977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3187282831129926460298605 1195231061673722422611977)
        ·
          refine ⟨896423296255291816958983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1195231061673722422611977 896423296255291816958983)
          ·
            refine ⟨1344634944382937725438475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 896423296255291816958983 1344634944382937725438475)
            ·
              refine ⟨2016952416574406588157713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1344634944382937725438475 2016952416574406588157713)
              ·
                refine ⟨1512714312430804941118285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2016952416574406588157713 1512714312430804941118285)
                ·
                  refine ⟨567267867161551852919357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1512714312430804941118285 567267867161551852919357)
                  ·
                    refine ⟨212725450185581944844759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 567267867161551852919357 212725450185581944844759)
                    ·
                      rfl

theorem cell22_621422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 1, 2, 3, 3].length) (baseStart_621422 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_621422 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_621422 prefixEnd_621422 := by exact prefixLift 621422
  have htrace : WordTrace (prefixWord ++ tailWord_621422) baseStart_621422 baseEnd_621422 := by
    simpa [prefixWord, tailWord_621422, baseEnd_621422] using wordTrace_append hprefix tailTrace_621422
  have hstable : (prefixWord ++ tailWord_621422).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_621422).length < 2 ^ (prefixWord ++ tailWord_621422).sum := by decide
  have hdescent : baseEnd_621422 < baseStart_621422 := by decide
  rcases family_descends (prefixWord ++ tailWord_621422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_621463 : List Nat := [1, 1, 3, 3, 1, 2, 4, 1, 6]
def baseStart_621463 : Nat := 118140960795 + 621463 * 2 ^ 59
def prefixEnd_621463 : Nat := 4983230072969 + 3 ^ 40 * 621463 * 2
def baseEnd_621463 : Nat := 70913161774490501523211

theorem tailTrace_621463 : CollatzResearch.WordTrace tailWord_621463 prefixEnd_621463 70913161774490501523211 := by
  unfold tailWord_621463
  simp only [CollatzResearch.WordTrace]
  refine ⟨22666617747553163275477043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15111078498368775516984695 22666617747553163275477043)
  ·
    refine ⟨33999926621329744913215565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22666617747553163275477043 33999926621329744913215565)
    ·
      refine ⟨12749972482998654342455837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33999926621329744913215565 12749972482998654342455837)
      ·
        refine ⟨4781239681124495378420939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12749972482998654342455837 4781239681124495378420939)
        ·
          refine ⟨7171859521686743067631409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4781239681124495378420939 7171859521686743067631409)
          ·
            refine ⟨5378894641265057300723557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7171859521686743067631409 5378894641265057300723557)
            ·
              refine ⟨1008542745237198243885667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5378894641265057300723557 1008542745237198243885667)
              ·
                refine ⟨1512814117855797365828501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1008542745237198243885667 1512814117855797365828501)
                ·
                  refine ⟨70913161774490501523211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1512814117855797365828501 70913161774490501523211)
                  ·
                    rfl

theorem cell22_621463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 4, 1, 6].length) (baseStart_621463 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_621463 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_621463 prefixEnd_621463 := by exact prefixLift 621463
  have htrace : WordTrace (prefixWord ++ tailWord_621463) baseStart_621463 baseEnd_621463 := by
    simpa [prefixWord, tailWord_621463, baseEnd_621463] using wordTrace_append hprefix tailTrace_621463
  have hstable : (prefixWord ++ tailWord_621463).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_621463).length < 2 ^ (prefixWord ++ tailWord_621463).sum := by decide
  have hdescent : baseEnd_621463 < baseStart_621463 := by decide
  rcases family_descends (prefixWord ++ tailWord_621463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_621493 : List Nat := [1, 3, 3, 2, 1, 1, 1, 3, 1, 6]
def baseStart_621493 : Nat := 118140960795 + 621493 * 2 ^ 59
def prefixEnd_621493 : Nat := 4983230072969 + 3 ^ 40 * 621493 * 2
def baseEnd_621493 : Nat := 212749754936561426319541

theorem tailTrace_621493 : CollatzResearch.WordTrace tailWord_621493 prefixEnd_621493 212749754936561426319541 := by
  unfold tailWord_621493
  simp only [CollatzResearch.WordTrace]
  refine ⟨22667711937444478399069133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15111807958296318932712755 22667711937444478399069133)
  ·
    refine ⟨8500391976541679399650925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22667711937444478399069133 8500391976541679399650925)
    ·
      refine ⟨3187646991203129774869097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8500391976541679399650925 3187646991203129774869097)
      ·
        refine ⟨2390735243402347331151823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3187646991203129774869097 2390735243402347331151823)
        ·
          refine ⟨3586102865103520996727735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2390735243402347331151823 3586102865103520996727735)
          ·
            refine ⟨5379154297655281495091603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3586102865103520996727735 5379154297655281495091603)
            ·
              refine ⟨8068731446482922242637405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5379154297655281495091603 8068731446482922242637405)
              ·
                refine ⟨3025774292431095840989027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8068731446482922242637405 3025774292431095840989027)
                ·
                  refine ⟨4538661438646643761483541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3025774292431095840989027 4538661438646643761483541)
                  ·
                    refine ⟨212749754936561426319541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4538661438646643761483541 212749754936561426319541)
                    ·
                      rfl

theorem cell22_621493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 3, 1, 6].length) (baseStart_621493 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_621493 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_621493 prefixEnd_621493 := by exact prefixLift 621493
  have htrace : WordTrace (prefixWord ++ tailWord_621493) baseStart_621493 baseEnd_621493 := by
    simpa [prefixWord, tailWord_621493, baseEnd_621493] using wordTrace_append hprefix tailTrace_621493
  have hstable : (prefixWord ++ tailWord_621493).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_621493).length < 2 ^ (prefixWord ++ tailWord_621493).sum := by decide
  have hdescent : baseEnd_621493 < baseStart_621493 := by decide
  rcases family_descends (prefixWord ++ tailWord_621493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_621497 : List Nat := [1, 2, 1, 4, 2, 4, 1, 3, 4]
def baseStart_621497 : Nat := 118140960795 + 621497 * 2 ^ 59
def prefixEnd_621497 : Nat := 4983230072969 + 3 ^ 40 * 621497 * 2
def baseEnd_621497 : Nat := 70917041406102249739843

theorem tailTrace_621497 : CollatzResearch.WordTrace tailWord_621497 prefixEnd_621497 70917041406102249739843 := by
  unfold tailWord_621497
  simp only [CollatzResearch.WordTrace]
  refine ⟨22667857829429987082214745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15111905219619991388143163 22667857829429987082214745)
  ·
    refine ⟨17000893372072490311661059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22667857829429987082214745 17000893372072490311661059)
    ·
      refine ⟨25501340058108735467491589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17000893372072490311661059 25501340058108735467491589)
      ·
        refine ⟨4781501260895387900154673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25501340058108735467491589 4781501260895387900154673)
        ·
          refine ⟨3586125945671540925116005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4781501260895387900154673 3586125945671540925116005)
          ·
            refine ⟨672398614813413923459251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3586125945671540925116005 672398614813413923459251)
            ·
              refine ⟨1008597922220120885188877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 672398614813413923459251 1008597922220120885188877)
              ·
                refine ⟨378224220832545331945829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1008597922220120885188877 378224220832545331945829)
                ·
                  refine ⟨70917041406102249739843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 378224220832545331945829 70917041406102249739843)
                  ·
                    rfl

theorem cell22_621497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 4, 1, 3, 4].length) (baseStart_621497 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_621497 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_621497 prefixEnd_621497 := by exact prefixLift 621497
  have htrace : WordTrace (prefixWord ++ tailWord_621497) baseStart_621497 baseEnd_621497 := by
    simpa [prefixWord, tailWord_621497, baseEnd_621497] using wordTrace_append hprefix tailTrace_621497
  have hstable : (prefixWord ++ tailWord_621497).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_621497).length < 2 ^ (prefixWord ++ tailWord_621497).sum := by decide
  have hdescent : baseEnd_621497 < baseStart_621497 := by decide
  rcases family_descends (prefixWord ++ tailWord_621497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_621525 : List Nat := [1, 3, 2, 3, 3, 1, 2, 7]
def baseStart_621525 : Nat := 118140960795 + 621525 * 2 ^ 59
def prefixEnd_621525 : Nat := 4983230072969 + 3 ^ 40 * 621525 * 2
def baseEnd_621525 : Nat := 23640078798947112168827

theorem tailTrace_621525 : CollatzResearch.WordTrace tailWord_621525 prefixEnd_621525 23640078798947112168827 := by
  unfold tailWord_621525
  simp only [CollatzResearch.WordTrace]
  refine ⟨22668879073328547864234029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15112586048885698576156019 22668879073328547864234029)
  ·
    refine ⟨8500829652498205449087761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22668879073328547864234029 8500829652498205449087761)
    ·
      refine ⟨6375622239373654086815821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8500829652498205449087761 6375622239373654086815821)
      ·
        refine ⟨2390858339765120282555933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6375622239373654086815821 2390858339765120282555933)
        ·
          refine ⟨896571877411920105958475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2390858339765120282555933 896571877411920105958475)
          ·
            refine ⟨1344857816117880158937713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 896571877411920105958475 1344857816117880158937713)
            ·
              refine ⟨1008643362088410119203285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1344857816117880158937713 1008643362088410119203285)
              ·
                refine ⟨23640078798947112168827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1008643362088410119203285 23640078798947112168827)
                ·
                  rfl

theorem cell22_621525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 2, 7].length) (baseStart_621525 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_621525 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_621525 prefixEnd_621525 := by exact prefixLift 621525
  have htrace : WordTrace (prefixWord ++ tailWord_621525) baseStart_621525 baseEnd_621525 := by
    simpa [prefixWord, tailWord_621525, baseEnd_621525] using wordTrace_append hprefix tailTrace_621525
  have hstable : (prefixWord ++ tailWord_621525).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_621525).length < 2 ^ (prefixWord ++ tailWord_621525).sum := by decide
  have hdescent : baseEnd_621525 < baseStart_621525 := by decide
  rcases family_descends (prefixWord ++ tailWord_621525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_621529 : List Nat := [1, 2, 1, 2, 5, 3, 2, 1, 2, 3]
def baseStart_621529 : Nat := 118140960795 + 621529 * 2 ^ 59
def prefixEnd_621529 : Nat := 4983230072969 + 3 ^ 40 * 621529 * 2
def baseEnd_621529 : Nat := 212762078472269332419431

theorem tailTrace_621529 : CollatzResearch.WordTrace tailWord_621529 prefixEnd_621529 212762078472269332419431 := by
  unfold tailWord_621529
  simp only [CollatzResearch.WordTrace]
  refine ⟨22669024965314056547379641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15112683310209371031586427 22669024965314056547379641)
  ·
    refine ⟨17001768723985542410534731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22669024965314056547379641 17001768723985542410534731)
    ·
      refine ⟨25502653085978313615802097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17001768723985542410534731 25502653085978313615802097)
      ·
        refine ⟨19126989814483735211851573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25502653085978313615802097 19126989814483735211851573)
        ·
          refine ⟨1793155295107850176111085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 19126989814483735211851573 1793155295107850176111085)
          ·
            refine ⟨672433235665443816041657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1793155295107850176111085 672433235665443816041657)
            ·
              refine ⟨504324926749082862031243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 672433235665443816041657 504324926749082862031243)
              ·
                refine ⟨756487390123624293046865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 504324926749082862031243 756487390123624293046865)
                ·
                  refine ⟨567365542592718219785149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 756487390123624293046865 567365542592718219785149)
                  ·
                    refine ⟨212762078472269332419431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 567365542592718219785149 212762078472269332419431)
                    ·
                      rfl

theorem cell22_621529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 3, 2, 1, 2, 3].length) (baseStart_621529 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_621529 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_621529 prefixEnd_621529 := by exact prefixLift 621529
  have htrace : WordTrace (prefixWord ++ tailWord_621529) baseStart_621529 baseEnd_621529 := by
    simpa [prefixWord, tailWord_621529, baseEnd_621529] using wordTrace_append hprefix tailTrace_621529
  have hstable : (prefixWord ++ tailWord_621529).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_621529).length < 2 ^ (prefixWord ++ tailWord_621529).sum := by decide
  have hdescent : baseEnd_621529 < baseStart_621529 := by decide
  rcases family_descends (prefixWord ++ tailWord_621529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_621660 : List Nat := [2, 2, 4, 1, 1, 1, 3, 8]
def baseStart_621660 : Nat := 118140960795 + 621660 * 2 ^ 59
def prefixEnd_621660 : Nat := 4983230072969 + 3 ^ 40 * 621660 * 2
def baseEnd_621660 : Nat := 23645213605492073043781

theorem tailTrace_621660 : CollatzResearch.WordTrace tailWord_621660 prefixEnd_621660 23645213605492073043781 := by
  unfold tailWord_621660
  simp only [CollatzResearch.WordTrace]
  refine ⟨11336901463919732960199217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15115868618559643946932289 11336901463919732960199217)
  ·
    refine ⟨8502676097939799720149413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11336901463919732960199217 8502676097939799720149413)
    ·
      refine ⟨1594251768363712447528015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8502676097939799720149413 1594251768363712447528015)
      ·
        refine ⟨2391377652545568671292023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1594251768363712447528015 2391377652545568671292023)
        ·
          refine ⟨3587066478818353006938035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2391377652545568671292023 3587066478818353006938035)
          ·
            refine ⟨5380599718227529510407053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3587066478818353006938035 5380599718227529510407053)
            ·
              refine ⟨2017724894335323566402645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5380599718227529510407053 2017724894335323566402645)
              ·
                refine ⟨23645213605492073043781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2017724894335323566402645 23645213605492073043781)
                ·
                  rfl

theorem cell22_621660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 3, 8].length) (baseStart_621660 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_621660 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_621660 prefixEnd_621660 := by exact prefixLift 621660
  have htrace : WordTrace (prefixWord ++ tailWord_621660) baseStart_621660 baseEnd_621660 := by
    simpa [prefixWord, tailWord_621660, baseEnd_621660] using wordTrace_append hprefix tailTrace_621660
  have hstable : (prefixWord ++ tailWord_621660).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_621660).length < 2 ^ (prefixWord ++ tailWord_621660).sum := by decide
  have hdescent : baseEnd_621660 < baseStart_621660 := by decide
  rcases family_descends (prefixWord ++ tailWord_621660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_621666 : List Nat := [3, 3, 2, 2, 1, 3, 1, 3, 4]
def baseStart_621666 : Nat := 118140960795 + 621666 * 2 ^ 59
def prefixEnd_621666 : Nat := 4983230072969 + 3 ^ 40 * 621666 * 2
def baseEnd_621666 : Nat := 70936325457348880581337

theorem tailTrace_621666 : CollatzResearch.WordTrace tailWord_621666 prefixEnd_621666 70936325457348880581337 := by
  unfold tailWord_621666
  simp only [CollatzResearch.WordTrace]
  refine ⟨5668505441454432236279213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15116014510545152630077901 5668505441454432236279213)
  ·
    refine ⟨2125689540545412088604705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5668505441454432236279213 2125689540545412088604705)
    ·
      refine ⟨1594267155409059066453529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2125689540545412088604705 1594267155409059066453529)
      ·
        refine ⟨1195700366556794299840147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1594267155409059066453529 1195700366556794299840147)
        ·
          refine ⟨1793550549835191449760221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1195700366556794299840147 1793550549835191449760221)
          ·
            refine ⟨672581456188196793660083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1793550549835191449760221 672581456188196793660083)
            ·
              refine ⟨1008872184282295190490125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 672581456188196793660083 1008872184282295190490125)
              ·
                refine ⟨378327069105860696433797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1008872184282295190490125 378327069105860696433797)
                ·
                  refine ⟨70936325457348880581337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 378327069105860696433797 70936325457348880581337)
                  ·
                    rfl

theorem cell22_621666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 3, 1, 3, 4].length) (baseStart_621666 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_621666 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_621666 prefixEnd_621666 := by exact prefixLift 621666
  have htrace : WordTrace (prefixWord ++ tailWord_621666) baseStart_621666 baseEnd_621666 := by
    simpa [prefixWord, tailWord_621666, baseEnd_621666] using wordTrace_append hprefix tailTrace_621666
  have hstable : (prefixWord ++ tailWord_621666).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_621666).length < 2 ^ (prefixWord ++ tailWord_621666).sum := by decide
  have hdescent : baseEnd_621666 < baseStart_621666 := by decide
  rcases family_descends (prefixWord ++ tailWord_621666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_621857 : List Nat := [1, 2, 3, 2, 1, 1, 1, 6, 5]
def baseStart_621857 : Nat := 118140960795 + 621857 * 2 ^ 59
def prefixEnd_621857 : Nat := 4983230072969 + 3 ^ 40 * 621857 * 2
def baseEnd_621857 : Nat := 70958119858461936739475

theorem tailTrace_621857 : CollatzResearch.WordTrace tailWord_621857 prefixEnd_621857 70958119858461936739475 := by
  unfold tailWord_621857
  simp only [CollatzResearch.WordTrace]
  refine ⟨22680988108125768565319825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15120658738750512376879883 22680988108125768565319825)
  ·
    refine ⟨17010741081094326423989869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22680988108125768565319825 17010741081094326423989869)
    ·
      refine ⟨6379027905410372408996201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17010741081094326423989869 6379027905410372408996201)
      ·
        refine ⟨4784270929057779306747151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6379027905410372408996201 4784270929057779306747151)
        ·
          refine ⟨7176406393586668960120727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4784270929057779306747151 7176406393586668960120727)
          ·
            refine ⟨10764609590380003440181091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7176406393586668960120727 10764609590380003440181091)
            ·
              refine ⟨16146914385570005160271637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10764609590380003440181091 16146914385570005160271637)
              ·
                refine ⟨756886611823593991887733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 16146914385570005160271637 756886611823593991887733)
                ·
                  refine ⟨70958119858461936739475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 756886611823593991887733 70958119858461936739475)
                  ·
                    rfl

theorem cell22_621857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 6, 5].length) (baseStart_621857 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_621857 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_621857 prefixEnd_621857 := by exact prefixLift 621857
  have htrace : WordTrace (prefixWord ++ tailWord_621857) baseStart_621857 baseEnd_621857 := by
    simpa [prefixWord, tailWord_621857, baseEnd_621857] using wordTrace_append hprefix tailTrace_621857
  have hstable : (prefixWord ++ tailWord_621857).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_621857).length < 2 ^ (prefixWord ++ tailWord_621857).sum := by decide
  have hdescent : baseEnd_621857 < baseStart_621857 := by decide
  rcases family_descends (prefixWord ++ tailWord_621857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_621861 : List Nat := [1, 3, 1, 2, 4, 3, 1, 1, 3, 3]
def baseStart_621861 : Nat := 118140960795 + 621861 * 2 ^ 59
def prefixEnd_621861 : Nat := 4983230072969 + 3 ^ 40 * 621861 * 2
def baseEnd_621861 : Nat := 212875728857131133118413

theorem tailTrace_621861 : CollatzResearch.WordTrace tailWord_621861 prefixEnd_621861 212875728857131133118413 := by
  unfold tailWord_621861
  simp only [CollatzResearch.WordTrace]
  refine ⟨22681134000111277248465437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15120756000074184832310291 22681134000111277248465437)
  ·
    refine ⟨8505425250041728968174539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22681134000111277248465437 8505425250041728968174539)
    ·
      refine ⟨12758137875062593452261809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8505425250041728968174539 12758137875062593452261809)
      ·
        refine ⟨9568603406296945089196357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12758137875062593452261809 9568603406296945089196357)
        ·
          refine ⟨1794113138680677204224317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9568603406296945089196357 1794113138680677204224317)
          ·
            refine ⟨672792427005253951584119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1794113138680677204224317 672792427005253951584119)
            ·
              refine ⟨1009188640507880927376179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 672792427005253951584119 1009188640507880927376179)
              ·
                refine ⟨1513782960761821391064269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1009188640507880927376179 1513782960761821391064269)
                ·
                  refine ⟨567668610285683021649101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1513782960761821391064269 567668610285683021649101)
                  ·
                    refine ⟨212875728857131133118413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 567668610285683021649101 212875728857131133118413)
                    ·
                      rfl

theorem cell22_621861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 3, 1, 1, 3, 3].length) (baseStart_621861 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_621861 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_621861 prefixEnd_621861 := by exact prefixLift 621861
  have htrace : WordTrace (prefixWord ++ tailWord_621861) baseStart_621861 baseEnd_621861 := by
    simpa [prefixWord, tailWord_621861, baseEnd_621861] using wordTrace_append hprefix tailTrace_621861
  have hstable : (prefixWord ++ tailWord_621861).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_621861).length < 2 ^ (prefixWord ++ tailWord_621861).sum := by decide
  have hdescent : baseEnd_621861 < baseStart_621861 := by decide
  rcases family_descends (prefixWord ++ tailWord_621861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_621874 : List Nat := [3, 2, 1, 1, 4, 2, 1, 3, 5]
def baseStart_621874 : Nat := 118140960795 + 621874 * 2 ^ 59
def prefixEnd_621874 : Nat := 4983230072969 + 3 ^ 40 * 621874 * 2
def baseEnd_621874 : Nat := 70960059674267810847791

theorem tailTrace_621874 : CollatzResearch.WordTrace tailWord_621874 prefixEnd_621874 70960059674267810847791 := by
  unfold tailWord_621874
  simp only [CollatzResearch.WordTrace]
  refine ⟨5670402037266045117172169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15121072099376120312459117 5670402037266045117172169)
  ·
    refine ⟨4252801527949533837879127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5670402037266045117172169 4252801527949533837879127)
    ·
      refine ⟨6379202291924300756818691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4252801527949533837879127 6379202291924300756818691)
      ·
        refine ⟨9568803437886451135228037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6379202291924300756818691 9568803437886451135228037)
        ·
          refine ⟨1794150644603709587855257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9568803437886451135228037 1794150644603709587855257)
          ·
            refine ⟨1345612983452782190891443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1794150644603709587855257 1345612983452782190891443)
            ·
              refine ⟨2018419475179173286337165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1345612983452782190891443 2018419475179173286337165)
              ·
                refine ⟨756907303192189982376437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2018419475179173286337165 756907303192189982376437)
                ·
                  refine ⟨70960059674267810847791, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 756907303192189982376437 70960059674267810847791)
                  ·
                    rfl

theorem cell22_621874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 1, 3, 5].length) (baseStart_621874 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_621874 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_621874 prefixEnd_621874 := by exact prefixLift 621874
  have htrace : WordTrace (prefixWord ++ tailWord_621874) baseStart_621874 baseEnd_621874 := by
    simpa [prefixWord, tailWord_621874, baseEnd_621874] using wordTrace_append hprefix tailTrace_621874
  have hstable : (prefixWord ++ tailWord_621874).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_621874).length < 2 ^ (prefixWord ++ tailWord_621874).sum := by decide
  have hdescent : baseEnd_621874 < baseStart_621874 := by decide
  rcases family_descends (prefixWord ++ tailWord_621874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_621953 : List Nat := [1, 2, 4, 3, 2, 1, 2, 3, 4]
def baseStart_621953 : Nat := 118140960795 + 621953 * 2 ^ 59
def prefixEnd_621953 : Nat := 4983230072969 + 3 ^ 40 * 621953 * 2
def baseEnd_621953 : Nat := 70969074112424519939377

theorem tailTrace_621953 : CollatzResearch.WordTrace tailWord_621953 prefixEnd_621953 70969074112424519939377 := by
  unfold tailWord_621953
  simp only [CollatzResearch.WordTrace]
  refine ⟨22684489515777976960814513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15122993010518651307209675 22684489515777976960814513)
  ·
    refine ⟨17013367136833482720610885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22684489515777976960814513 17013367136833482720610885)
    ·
      refine ⟨3190006338156278010114541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17013367136833482720610885 3190006338156278010114541)
      ·
        refine ⟨1196252376808604253792953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3190006338156278010114541 1196252376808604253792953)
        ·
          refine ⟨897189282606453190344715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1196252376808604253792953 897189282606453190344715)
          ·
            refine ⟨1345783923909679785517073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 897189282606453190344715 1345783923909679785517073)
            ·
              refine ⟨1009337942932259839137805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1345783923909679785517073 1009337942932259839137805)
              ·
                refine ⟨378501728599597439676677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1009337942932259839137805 378501728599597439676677)
                ·
                  refine ⟨70969074112424519939377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 378501728599597439676677 70969074112424519939377)
                  ·
                    rfl

theorem cell22_621953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 2, 3, 4].length) (baseStart_621953 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_621953 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_621953 prefixEnd_621953 := by exact prefixLift 621953
  have htrace : WordTrace (prefixWord ++ tailWord_621953) baseStart_621953 baseEnd_621953 := by
    simpa [prefixWord, tailWord_621953, baseEnd_621953] using wordTrace_append hprefix tailTrace_621953
  have hstable : (prefixWord ++ tailWord_621953).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_621953).length < 2 ^ (prefixWord ++ tailWord_621953).sum := by decide
  have hdescent : baseEnd_621953 < baseStart_621953 := by decide
  rcases family_descends (prefixWord ++ tailWord_621953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_622088 : List Nat := [2, 1, 3, 2, 1, 1, 6, 2, 4]
def baseStart_622088 : Nat := 118140960795 + 622088 * 2 ^ 59
def prefixEnd_622088 : Nat := 4983230072969 + 3 ^ 40 * 622088 * 2
def baseEnd_622088 : Nat := 70984478532059402564239

theorem tailTrace_622088 : CollatzResearch.WordTrace tailWord_622088 prefixEnd_622088 70984478532059402564239 := by
  unfold tailWord_622088
  simp only [CollatzResearch.WordTrace]
  refine ⟨11344706685144447508489459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15126275580192596677985945 11344706685144447508489459)
  ·
    refine ⟨17017060027716671262734189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11344706685144447508489459 17017060027716671262734189)
    ·
      refine ⟨6381397510393751723525321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17017060027716671262734189 6381397510393751723525321)
      ·
        refine ⟨4786048132795313792643991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6381397510393751723525321 4786048132795313792643991)
        ·
          refine ⟨7179072199192970688965987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4786048132795313792643991 7179072199192970688965987)
          ·
            refine ⟨10768608298789456033448981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7179072199192970688965987 10768608298789456033448981)
            ·
              refine ⟨504778514005755751567921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 10768608298789456033448981 504778514005755751567921)
              ·
                refine ⟨378583885504316813675941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 504778514005755751567921 378583885504316813675941)
                ·
                  refine ⟨70984478532059402564239, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 378583885504316813675941 70984478532059402564239)
                  ·
                    rfl

theorem cell22_622088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 6, 2, 4].length) (baseStart_622088 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_622088 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_622088 prefixEnd_622088 := by exact prefixLift 622088
  have htrace : WordTrace (prefixWord ++ tailWord_622088) baseStart_622088 baseEnd_622088 := by
    simpa [prefixWord, tailWord_622088, baseEnd_622088] using wordTrace_append hprefix tailTrace_622088
  have hstable : (prefixWord ++ tailWord_622088).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_622088).length < 2 ^ (prefixWord ++ tailWord_622088).sum := by decide
  have hdescent : baseEnd_622088 < baseStart_622088 := by decide
  rcases family_descends (prefixWord ++ tailWord_622088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_622099 : List Nat := [1, 1, 1, 2, 1, 6, 3, 7]
def baseStart_622099 : Nat := 118140960795 + 622099 * 2 ^ 59
def prefixEnd_622099 : Nat := 4983230072969 + 3 ^ 40 * 622099 * 2
def baseEnd_622099 : Nat := 23661911235664205074187

theorem tailTrace_622099 : CollatzResearch.WordTrace tailWord_622099 prefixEnd_622099 23661911235664205074187 := by
  unfold tailWord_622099
  simp only [CollatzResearch.WordTrace]
  refine ⟨22689814573249043895629351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15126543048832695930419567 22689814573249043895629351)
  ·
    refine ⟨34034721859873565843444027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22689814573249043895629351 34034721859873565843444027)
    ·
      refine ⟨51052082789810348765166041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34034721859873565843444027 51052082789810348765166041)
      ·
        refine ⟨38289062092357761573874531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51052082789810348765166041 38289062092357761573874531)
        ·
          refine ⟨57433593138536642360811797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38289062092357761573874531 57433593138536642360811797)
          ·
            refine ⟨2692199678368905110663053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 57433593138536642360811797 2692199678368905110663053)
            ·
              refine ⟨1009574879388339416498645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2692199678368905110663053 1009574879388339416498645)
              ·
                refine ⟨23661911235664205074187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1009574879388339416498645 23661911235664205074187)
                ·
                  rfl

theorem cell22_622099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 3, 7].length) (baseStart_622099 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_622099 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_622099 prefixEnd_622099 := by exact prefixLift 622099
  have htrace : WordTrace (prefixWord ++ tailWord_622099) baseStart_622099 baseEnd_622099 := by
    simpa [prefixWord, tailWord_622099, baseEnd_622099] using wordTrace_append hprefix tailTrace_622099
  have hstable : (prefixWord ++ tailWord_622099).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_622099).length < 2 ^ (prefixWord ++ tailWord_622099).sum := by decide
  have hdescent : baseEnd_622099 < baseStart_622099 := by decide
  rcases family_descends (prefixWord ++ tailWord_622099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_622212 : List Nat := [2, 3, 2, 1, 5, 1, 2, 1, 5]
def baseStart_622212 : Nat := 118140960795 + 622212 * 2 ^ 59
def prefixEnd_622212 : Nat := 4983230072969 + 3 ^ 40 * 622212 * 2
def baseEnd_622212 : Nat := 70998627776761072530779

theorem tailTrace_622212 : CollatzResearch.WordTrace tailWord_622212 prefixEnd_622212 70998627776761072530779 := by
  unfold tailWord_622212
  simp only [CollatzResearch.WordTrace]
  refine ⟨11346968010919832097246445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15129290681226442796328593 11346968010919832097246445)
  ·
    refine ⟨4255113004094937036467417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11346968010919832097246445 4255113004094937036467417)
    ·
      refine ⟨3191334753071202777350563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4255113004094937036467417 3191334753071202777350563)
      ·
        refine ⟨4787002129606804166025845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3191334753071202777350563 4787002129606804166025845)
        ·
          refine ⟨448781449650637890564923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 4787002129606804166025845 448781449650637890564923)
          ·
            refine ⟨673172174475956835847385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 448781449650637890564923 673172174475956835847385)
            ·
              refine ⟨504879130856967626885539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 673172174475956835847385 504879130856967626885539)
              ·
                refine ⟨757318696285451440328309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 504879130856967626885539 757318696285451440328309)
                ·
                  refine ⟨70998627776761072530779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 757318696285451440328309 70998627776761072530779)
                  ·
                    rfl

theorem cell22_622212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 5, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 5, 1, 2, 1, 5].length) (baseStart_622212 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_622212 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_622212 prefixEnd_622212 := by exact prefixLift 622212
  have htrace : WordTrace (prefixWord ++ tailWord_622212) baseStart_622212 baseEnd_622212 := by
    simpa [prefixWord, tailWord_622212, baseEnd_622212] using wordTrace_append hprefix tailTrace_622212
  have hstable : (prefixWord ++ tailWord_622212).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_622212).length < 2 ^ (prefixWord ++ tailWord_622212).sum := by decide
  have hdescent : baseEnd_622212 < baseStart_622212 := by decide
  rcases family_descends (prefixWord ++ tailWord_622212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_622238 : List Nat := [4, 3, 1, 1, 1, 2, 1, 1, 3, 5]
def baseStart_622238 : Nat := 118140960795 + 622238 * 2 ^ 59
def prefixEnd_622238 : Nat := 4983230072969 + 3 ^ 40 * 622238 * 2
def baseEnd_622238 : Nat := 213004783661627816442257

theorem tailTrace_622238 : CollatzResearch.WordTrace tailWord_622238 prefixEnd_622238 213004783661627816442257 := by
  unfold tailWord_622238
  simp only [CollatzResearch.WordTrace]
  refine ⟨2836860539968183829367421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15129922879830313756626245 2836860539968183829367421)
  ·
    refine ⟨1063822702488068936012783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2836860539968183829367421 1063822702488068936012783)
    ·
      refine ⟨1595734053732103404019175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1063822702488068936012783 1595734053732103404019175)
      ·
        refine ⟨2393601080598155106028763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1595734053732103404019175 2393601080598155106028763)
        ·
          refine ⟨3590401620897232659043145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2393601080598155106028763 3590401620897232659043145)
          ·
            refine ⟨2692801215672924494282359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3590401620897232659043145 2692801215672924494282359)
            ·
              refine ⟨4039201823509386741423539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2692801215672924494282359 4039201823509386741423539)
              ·
                refine ⟨6058802735264080112135309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4039201823509386741423539 6058802735264080112135309)
                ·
                  refine ⟨2272051025724030042050741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6058802735264080112135309 2272051025724030042050741)
                  ·
                    refine ⟨213004783661627816442257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2272051025724030042050741 213004783661627816442257)
                    ·
                      rfl

theorem cell22_622238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 1, 1, 3, 5].length) (baseStart_622238 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_622238 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_622238 prefixEnd_622238 := by exact prefixLift 622238
  have htrace : WordTrace (prefixWord ++ tailWord_622238) baseStart_622238 baseEnd_622238 := by
    simpa [prefixWord, tailWord_622238, baseEnd_622238] using wordTrace_append hprefix tailTrace_622238
  have hstable : (prefixWord ++ tailWord_622238).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_622238).length < 2 ^ (prefixWord ++ tailWord_622238).sum := by decide
  have hdescent : baseEnd_622238 < baseStart_622238 := by decide
  rcases family_descends (prefixWord ++ tailWord_622238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_622253 : List Nat := [1, 5, 2, 1, 1, 1, 1, 4, 2, 4]
def baseStart_622253 : Nat := 118140960795 + 622253 * 2 ^ 59
def prefixEnd_622253 : Nat := 4983230072969 + 3 ^ 40 * 622253 * 2
def baseEnd_622253 : Nat := 213009918468172777317211

theorem tailTrace_622253 : CollatzResearch.WordTrace tailWord_622253 prefixEnd_622253 213009918468172777317211 := by
  unfold tailWord_622253
  simp only [CollatzResearch.WordTrace]
  refine ⟨22695431414691128196735413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15130287609794085464490275 22695431414691128196735413)
  ·
    refine ⟨2127696695127293268443945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 22695431414691128196735413 2127696695127293268443945)
    ·
      refine ⟨1595772521345469951332959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2127696695127293268443945 1595772521345469951332959)
      ·
        refine ⟨2393658782018204926999439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1595772521345469951332959 2393658782018204926999439)
        ·
          refine ⟨3590488173027307390499159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2393658782018204926999439 3590488173027307390499159)
          ·
            refine ⟨5385732259540961085748739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3590488173027307390499159 5385732259540961085748739)
            ·
              refine ⟨8078598389311441628623109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5385732259540961085748739 8078598389311441628623109)
              ·
                refine ⟨1514737197995895305366833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8078598389311441628623109 1514737197995895305366833)
                ·
                  refine ⟨1136052898496921479025125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1514737197995895305366833 1136052898496921479025125)
                  ·
                    refine ⟨213009918468172777317211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1136052898496921479025125 213009918468172777317211)
                    ·
                      rfl

theorem cell22_622253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 4, 2, 4].length) (baseStart_622253 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_622253 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_622253 prefixEnd_622253 := by exact prefixLift 622253
  have htrace : WordTrace (prefixWord ++ tailWord_622253) baseStart_622253 baseEnd_622253 := by
    simpa [prefixWord, tailWord_622253, baseEnd_622253] using wordTrace_append hprefix tailTrace_622253
  have hstable : (prefixWord ++ tailWord_622253).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_622253).length < 2 ^ (prefixWord ++ tailWord_622253).sum := by decide
  have hdescent : baseEnd_622253 < baseStart_622253 := by decide
  rcases family_descends (prefixWord ++ tailWord_622253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_622268 : List Nat := [2, 2, 2, 3, 1, 4, 1, 7]
def baseStart_622268 : Nat := 118140960795 + 622268 * 2 ^ 59
def prefixEnd_622268 : Nat := 4983230072969 + 3 ^ 40 * 622268 * 2
def baseEnd_622268 : Nat := 23668339252746415354685

theorem tailTrace_622268 : CollatzResearch.WordTrace tailWord_622268 prefixEnd_622268 23668339252746415354685 := by
  unfold tailWord_622268
  simp only [CollatzResearch.WordTrace]
  refine ⟨11347989254818392879265729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15130652339757857172354305 11347989254818392879265729)
  ·
    refine ⟨8510991941113794659449297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11347989254818392879265729 8510991941113794659449297)
    ·
      refine ⟨6383243955835345994586973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8510991941113794659449297 6383243955835345994586973)
      ·
        refine ⟨2393716483438254747970115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6383243955835345994586973 2393716483438254747970115)
        ·
          refine ⟨3590574725157382121955173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2393716483438254747970115 3590574725157382121955173)
          ·
            refine ⟨673232760967009147866595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3590574725157382121955173 673232760967009147866595)
            ·
              refine ⟨1009849141450513721799893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 673232760967009147866595 1009849141450513721799893)
              ·
                refine ⟨23668339252746415354685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1009849141450513721799893 23668339252746415354685)
                ·
                  rfl

theorem cell22_622268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 4, 1, 7].length) (baseStart_622268 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_622268 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_622268 prefixEnd_622268 := by exact prefixLift 622268
  have htrace : WordTrace (prefixWord ++ tailWord_622268) baseStart_622268 baseEnd_622268 := by
    simpa [prefixWord, tailWord_622268, baseEnd_622268] using wordTrace_append hprefix tailTrace_622268
  have hstable : (prefixWord ++ tailWord_622268).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_622268).length < 2 ^ (prefixWord ++ tailWord_622268).sum := by decide
  have hdescent : baseEnd_622268 < baseStart_622268 := by decide
  rcases family_descends (prefixWord ++ tailWord_622268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_622296 : List Nat := [2, 1, 2, 2, 3, 1, 2, 2, 7]
def baseStart_622296 : Nat := 118140960795 + 622296 * 2 ^ 59
def prefixEnd_622296 : Nat := 4983230072969 + 3 ^ 40 * 622296 * 2
def baseEnd_622296 : Nat := 71008212748978332830693

theorem tailTrace_622296 : CollatzResearch.WordTrace tailWord_622296 prefixEnd_622296 71008212748978332830693 := by
  unfold tailWord_622296
  simp only [CollatzResearch.WordTrace]
  refine ⟨11348499876767673270275371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15131333169023564360367161 11348499876767673270275371)
  ·
    refine ⟨17022749815151509905413057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11348499876767673270275371 17022749815151509905413057)
    ·
      refine ⟨12767062361363632429059793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17022749815151509905413057 12767062361363632429059793)
      ·
        refine ⟨9575296771022724321794845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12767062361363632429059793 9575296771022724321794845)
        ·
          refine ⟨3590736289133521620673067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9575296771022724321794845 3590736289133521620673067)
          ·
            refine ⟨5386104433700282431009601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3590736289133521620673067 5386104433700282431009601)
            ·
              refine ⟨4039578325275211823257201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5386104433700282431009601 4039578325275211823257201)
              ·
                refine ⟨3029683743956408867442901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4039578325275211823257201 3029683743956408867442901)
                ·
                  refine ⟨71008212748978332830693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3029683743956408867442901 71008212748978332830693)
                  ·
                    rfl

theorem cell22_622296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 2, 2, 7].length) (baseStart_622296 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_622296 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_622296 prefixEnd_622296 := by exact prefixLift 622296
  have htrace : WordTrace (prefixWord ++ tailWord_622296) baseStart_622296 baseEnd_622296 := by
    simpa [prefixWord, tailWord_622296, baseEnd_622296] using wordTrace_append hprefix tailTrace_622296
  have hstable : (prefixWord ++ tailWord_622296).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_622296).length < 2 ^ (prefixWord ++ tailWord_622296).sum := by decide
  have hdescent : baseEnd_622296 < baseStart_622296 := by decide
  rcases family_descends (prefixWord ++ tailWord_622296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_622317 : List Nat := [1, 5, 1, 2, 1, 2, 2, 4, 1, 3]
def baseStart_622317 : Nat := 118140960795 + 622317 * 2 ^ 59
def prefixEnd_622317 : Nat := 4983230072969 + 3 ^ 40 * 622317 * 2
def baseEnd_622317 : Nat := 213031826976097943717015

theorem tailTrace_622317 : CollatzResearch.WordTrace tailWord_622317 prefixEnd_622317 213031826976097943717015 := by
  unfold tailWord_622317
  simp only [CollatzResearch.WordTrace]
  refine ⟨22697765686459267127065205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15131843790972844751376803 22697765686459267127065205)
  ·
    refine ⟨2127915533105556293162363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 22697765686459267127065205 2127915533105556293162363)
    ·
      refine ⟨3191873299658334439743545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2127915533105556293162363 3191873299658334439743545)
      ·
        refine ⟨2393904974743750829807659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3191873299658334439743545 2393904974743750829807659)
        ·
          refine ⟨3590857462115626244711489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2393904974743750829807659 3590857462115626244711489)
          ·
            refine ⟨2693143096586719683533617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3590857462115626244711489 2693143096586719683533617)
            ·
              refine ⟨2019857322440039762650213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2693143096586719683533617 2019857322440039762650213)
              ·
                refine ⟨378723247957507455496915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2019857322440039762650213 378723247957507455496915)
                ·
                  refine ⟨568084871936261183245373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 378723247957507455496915 568084871936261183245373)
                  ·
                    refine ⟨213031826976097943717015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 568084871936261183245373 213031826976097943717015)
                    ·
                      rfl

theorem cell22_622317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 2, 4, 1, 3].length) (baseStart_622317 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_622317 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_622317 prefixEnd_622317 := by exact prefixLift 622317
  have htrace : WordTrace (prefixWord ++ tailWord_622317) baseStart_622317 baseEnd_622317 := by
    simpa [prefixWord, tailWord_622317, baseEnd_622317] using wordTrace_append hprefix tailTrace_622317
  have hstable : (prefixWord ++ tailWord_622317).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_622317).length < 2 ^ (prefixWord ++ tailWord_622317).sum := by decide
  have hdescent : baseEnd_622317 < baseStart_622317 := by decide
  rcases family_descends (prefixWord ++ tailWord_622317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_622482 : List Nat := [3, 2, 3, 2, 1, 1, 3, 2, 5]
def baseStart_622482 : Nat := 118140960795 + 622482 * 2 ^ 59
def prefixEnd_622482 : Nat := 4983230072969 + 3 ^ 40 * 622482 * 2
def baseEnd_622482 : Nat := 71029436616030837780503

theorem tailTrace_622482 : CollatzResearch.WordTrace tailWord_622482 prefixEnd_622482 71029436616030837780503 := by
  unfold tailWord_622482
  simp only [CollatzResearch.WordTrace]
  refine ⟨5675945932715375076705425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15135855820574333537881133 5675945932715375076705425)
  ·
    refine ⟨4256959449536531307529069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5675945932715375076705425 4256959449536531307529069)
    ·
      refine ⟨1596359793576199240323401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4256959449536531307529069 1596359793576199240323401)
      ·
        refine ⟨1197269845182149430242551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1596359793576199240323401 1197269845182149430242551)
        ·
          refine ⟨1795904767773224145363827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1197269845182149430242551 1795904767773224145363827)
          ·
            refine ⟨2693857151659836218045741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1795904767773224145363827 2693857151659836218045741)
            ·
              refine ⟨1010196431872438581767153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2693857151659836218045741 1010196431872438581767153)
              ·
                refine ⟨757647323904328936325365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1010196431872438581767153 757647323904328936325365)
                ·
                  refine ⟨71029436616030837780503, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 757647323904328936325365 71029436616030837780503)
                  ·
                    rfl

theorem cell22_622482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 3, 2, 5].length) (baseStart_622482 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_622482 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_622482 prefixEnd_622482 := by exact prefixLift 622482
  have htrace : WordTrace (prefixWord ++ tailWord_622482) baseStart_622482 baseEnd_622482 := by
    simpa [prefixWord, tailWord_622482, baseEnd_622482] using wordTrace_append hprefix tailTrace_622482
  have hstable : (prefixWord ++ tailWord_622482).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_622482).length < 2 ^ (prefixWord ++ tailWord_622482).sum := by decide
  have hdescent : baseEnd_622482 < baseStart_622482 := by decide
  rcases family_descends (prefixWord ++ tailWord_622482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_622538 : List Nat := [3, 1, 2, 1, 2, 1, 12]
def baseStart_622538 : Nat := 118140960795 + 622538 * 2 ^ 59
def prefixEnd_622538 : Nat := 4983230072969 + 3 ^ 40 * 622538 * 2
def baseEnd_622538 : Nat := 7892869621945445701531

theorem tailTrace_622538 : CollatzResearch.WordTrace tailWord_622538 prefixEnd_622538 7892869621945445701531 := by
  unfold tailWord_622538
  simp only [CollatzResearch.WordTrace]
  refine ⟨5676456554664655467715067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15137217479105747913906845 5676456554664655467715067)
  ·
    refine ⟨8514684831996983201572601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5676456554664655467715067 8514684831996983201572601)
    ·
      refine ⟨6386013623997737401179451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8514684831996983201572601 6386013623997737401179451)
      ·
        refine ⟨9579020435996606101769177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6386013623997737401179451 9579020435996606101769177)
        ·
          refine ⟨7184265326997454576326883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9579020435996606101769177 7184265326997454576326883)
          ·
            refine ⟨10776397990496181864490325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7184265326997454576326883 10776397990496181864490325)
            ·
              refine ⟨7892869621945445701531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 10776397990496181864490325 7892869621945445701531)
              ·
                rfl

theorem cell22_622538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 12].length) (baseStart_622538 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_622538 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_622538 prefixEnd_622538 := by exact prefixLift 622538
  have htrace : WordTrace (prefixWord ++ tailWord_622538) baseStart_622538 baseEnd_622538 := by
    simpa [prefixWord, tailWord_622538, baseEnd_622538] using wordTrace_append hprefix tailTrace_622538
  have hstable : (prefixWord ++ tailWord_622538).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_622538).length < 2 ^ (prefixWord ++ tailWord_622538).sum := by decide
  have hdescent : baseEnd_622538 < baseStart_622538 := by decide
  rcases family_descends (prefixWord ++ tailWord_622538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_622540 : List Nat := [2, 2, 1, 4, 1, 2, 1, 1, 4, 4]
def baseStart_622540 : Nat := 118140960795 + 622540 * 2 ^ 59
def prefixEnd_622540 : Nat := 4983230072969 + 3 ^ 40 * 622540 * 2
def baseEnd_622540 : Nat := 213108164433399695391331

theorem tailTrace_622540 : CollatzResearch.WordTrace tailWord_622540 prefixEnd_622540 213108164433399695391331 := by
  unfold tailWord_622540
  simp only [CollatzResearch.WordTrace]
  refine ⟨11352949582325688106216537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15137266109767584141622049 11352949582325688106216537)
  ·
    refine ⟨8514712186744266079662403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11352949582325688106216537 8514712186744266079662403)
    ·
      refine ⟨12772068280116399119493605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8514712186744266079662403 12772068280116399119493605)
      ·
        refine ⟨2394762802521824834905051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12772068280116399119493605 2394762802521824834905051)
        ·
          refine ⟨3592144203782737252357577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2394762802521824834905051 3592144203782737252357577)
          ·
            refine ⟨2694108152837052939268183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3592144203782737252357577 2694108152837052939268183)
            ·
              refine ⟨4041162229255579408902275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2694108152837052939268183 4041162229255579408902275)
              ·
                refine ⟨6061743343883369113353413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4041162229255579408902275 6061743343883369113353413)
                ·
                  refine ⟨1136576876978131708753765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6061743343883369113353413 1136576876978131708753765)
                  ·
                    refine ⟨213108164433399695391331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1136576876978131708753765 213108164433399695391331)
                    ·
                      rfl

theorem cell22_622540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 1, 1, 4, 4].length) (baseStart_622540 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_622540 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_622540 prefixEnd_622540 := by exact prefixLift 622540
  have htrace : WordTrace (prefixWord ++ tailWord_622540) baseStart_622540 baseEnd_622540 := by
    simpa [prefixWord, tailWord_622540, baseEnd_622540] using wordTrace_append hprefix tailTrace_622540
  have hstable : (prefixWord ++ tailWord_622540).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_622540).length < 2 ^ (prefixWord ++ tailWord_622540).sum := by decide
  have hdescent : baseEnd_622540 < baseStart_622540 := by decide
  rcases family_descends (prefixWord ++ tailWord_622540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_622542 : List Nat := [4, 1, 1, 1, 2, 2, 2, 4, 2, 3]
def baseStart_622542 : Nat := 118140960795 + 622542 * 2 ^ 59
def prefixEnd_622542 : Nat := 4983230072969 + 3 ^ 40 * 622542 * 2
def baseEnd_622542 : Nat := 213108849074272356841325

theorem tailTrace_622542 : CollatzResearch.WordTrace tailWord_622542 prefixEnd_622542 213108849074272356841325 := by
  unfold tailWord_622542
  simp only [CollatzResearch.WordTrace]
  refine ⟨2838246513830516319250735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15137314740429420369337253 2838246513830516319250735)
  ·
    refine ⟨4257369770745774478876103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2838246513830516319250735 4257369770745774478876103)
    ·
      refine ⟨6386054656118661718314155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4257369770745774478876103 6386054656118661718314155)
      ·
        refine ⟨9579081984177992577471233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6386054656118661718314155 9579081984177992577471233)
        ·
          refine ⟨7184311488133494433103425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9579081984177992577471233 7184311488133494433103425)
          ·
            refine ⟨5388233616100120824827569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7184311488133494433103425 5388233616100120824827569)
            ·
              refine ⟨4041175212075090618620677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5388233616100120824827569 4041175212075090618620677)
              ·
                refine ⟨757720352264079490991377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4041175212075090618620677 757720352264079490991377)
                ·
                  refine ⟨568290264198059618243533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 757720352264079490991377 568290264198059618243533)
                  ·
                    refine ⟨213108849074272356841325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 568290264198059618243533 213108849074272356841325)
                    ·
                      rfl

theorem cell22_622542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 2, 4, 2, 3].length) (baseStart_622542 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_622542 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_622542 prefixEnd_622542 := by exact prefixLift 622542
  have htrace : WordTrace (prefixWord ++ tailWord_622542) baseStart_622542 baseEnd_622542 := by
    simpa [prefixWord, tailWord_622542, baseEnd_622542] using wordTrace_append hprefix tailTrace_622542
  have hstable : (prefixWord ++ tailWord_622542).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_622542).length < 2 ^ (prefixWord ++ tailWord_622542).sum := by decide
  have hdescent : baseEnd_622542 < baseStart_622542 := by decide
  rcases family_descends (prefixWord ++ tailWord_622542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_622559 : List Nat := [1, 1, 2, 3, 4, 1, 4, 1, 2, 3]
def baseStart_622559 : Nat := 118140960795 + 622559 * 2 ^ 59
def prefixEnd_622559 : Nat := 4983230072969 + 3 ^ 40 * 622559 * 2
def baseEnd_622559 : Nat := 213114668521689979166273

theorem tailTrace_622559 : CollatzResearch.WordTrace tailWord_622559 prefixEnd_622559 213114668521689979166273 := by
  unfold tailWord_622559
  simp only [CollatzResearch.WordTrace]
  refine ⟨22706592151582542457374731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15137728101055028304916487 22706592151582542457374731)
  ·
    refine ⟨34059888227373813686062097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22706592151582542457374731 34059888227373813686062097)
    ·
      refine ⟨25544916170530360264546573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34059888227373813686062097 25544916170530360264546573)
      ·
        refine ⟨9579343563948885099204965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25544916170530360264546573 9579343563948885099204965)
        ·
          refine ⟨1796126918240415956100931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9579343563948885099204965 1796126918240415956100931)
          ·
            refine ⟨2694190377360623934151397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1796126918240415956100931 2694190377360623934151397)
            ·
              refine ⟨505160695755116987653387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2694190377360623934151397 505160695755116987653387)
              ·
                refine ⟨757741043632675481480081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 505160695755116987653387 757741043632675481480081)
                ·
                  refine ⟨568305782724506611110061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 757741043632675481480081 568305782724506611110061)
                  ·
                    refine ⟨213114668521689979166273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 568305782724506611110061 213114668521689979166273)
                    ·
                      rfl

theorem cell22_622559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 4, 1, 2, 3].length) (baseStart_622559 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_622559 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_622559 prefixEnd_622559 := by exact prefixLift 622559
  have htrace : WordTrace (prefixWord ++ tailWord_622559) baseStart_622559 baseEnd_622559 := by
    simpa [prefixWord, tailWord_622559, baseEnd_622559] using wordTrace_append hprefix tailTrace_622559
  have hstable : (prefixWord ++ tailWord_622559).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_622559).length < 2 ^ (prefixWord ++ tailWord_622559).sum := by decide
  have hdescent : baseEnd_622559 < baseStart_622559 := by decide
  rcases family_descends (prefixWord ++ tailWord_622559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_622604 : List Nat := [2, 2, 1, 2, 3, 1, 3, 4, 1, 3]
def baseStart_622604 : Nat := 118140960795 + 622604 * 2 ^ 59
def prefixEnd_622604 : Nat := 4983230072969 + 3 ^ 40 * 622604 * 2
def baseEnd_622604 : Nat := 213130072941324861791135

theorem tailTrace_622604 : CollatzResearch.WordTrace tailWord_622604 prefixEnd_622604 213130072941324861791135 := by
  unfold tailWord_622604
  simp only [CollatzResearch.WordTrace]
  refine ⟨11354116718209757571381433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15138822290946343428508577 11354116718209757571381433)
  ·
    refine ⟨8515587538657318178536075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11354116718209757571381433 8515587538657318178536075)
    ·
      refine ⟨12773381307985977267804113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8515587538657318178536075 12773381307985977267804113)
      ·
        refine ⟨9580035980989482950853085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12773381307985977267804113 9580035980989482950853085)
        ·
          refine ⟨3592513492871056106569907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9580035980989482950853085 3592513492871056106569907)
          ·
            refine ⟨5388770239306584159854861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3592513492871056106569907 5388770239306584159854861)
            ·
              refine ⟨2020788839739969059945573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5388770239306584159854861 2020788839739969059945573)
              ·
                refine ⟨378897907451244198739795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2020788839739969059945573 378897907451244198739795)
                ·
                  refine ⟨568346861176866298109693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 378897907451244198739795 568346861176866298109693)
                  ·
                    refine ⟨213130072941324861791135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 568346861176866298109693 213130072941324861791135)
                    ·
                      rfl

theorem cell22_622604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 3, 4, 1, 3].length) (baseStart_622604 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_622604 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_622604 prefixEnd_622604 := by exact prefixLift 622604
  have htrace : WordTrace (prefixWord ++ tailWord_622604) baseStart_622604 baseEnd_622604 := by
    simpa [prefixWord, tailWord_622604, baseEnd_622604] using wordTrace_append hprefix tailTrace_622604
  have hstable : (prefixWord ++ tailWord_622604).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_622604).length < 2 ^ (prefixWord ++ tailWord_622604).sum := by decide
  have hdescent : baseEnd_622604 < baseStart_622604 := by decide
  rcases family_descends (prefixWord ++ tailWord_622604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_622677 : List Nat := [1, 3, 2, 2, 1, 3, 3, 1, 1, 5]
def baseStart_622677 : Nat := 118140960795 + 622677 * 2 ^ 59
def prefixEnd_622677 : Nat := 4983230072969 + 3 ^ 40 * 622677 * 2
def baseEnd_622677 : Nat := 213155062333177004715911

theorem tailTrace_622677 : CollatzResearch.WordTrace tailWord_622677 prefixEnd_622677 213155062333177004715911 := by
  unfold tailWord_622677
  simp only [CollatzResearch.WordTrace]
  refine ⟨22710895965155048610170285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15140597310103365740113523 22710895965155048610170285)
  ·
    refine ⟨8516585986933143228813857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22710895965155048610170285 8516585986933143228813857)
    ·
      refine ⟨6387439490199857421610393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8516585986933143228813857 6387439490199857421610393)
      ·
        refine ⟨4790579617649893066207795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6387439490199857421610393 4790579617649893066207795)
        ·
          refine ⟨7185869426474839599311693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4790579617649893066207795 7185869426474839599311693)
          ·
            refine ⟨2694701034928064849741885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7185869426474839599311693 2694701034928064849741885)
            ·
              refine ⟨1010512888098024318653207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2694701034928064849741885 1010512888098024318653207)
              ·
                refine ⟨1515769332147036477979811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1010512888098024318653207 1515769332147036477979811)
                ·
                  refine ⟨2273653998220554716969717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1515769332147036477979811 2273653998220554716969717)
                  ·
                    refine ⟨213155062333177004715911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2273653998220554716969717 213155062333177004715911)
                    ·
                      rfl

theorem cell22_622677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 3, 1, 1, 5].length) (baseStart_622677 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_622677 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_622677 prefixEnd_622677 := by exact prefixLift 622677
  have htrace : WordTrace (prefixWord ++ tailWord_622677) baseStart_622677 baseEnd_622677 := by
    simpa [prefixWord, tailWord_622677, baseEnd_622677] using wordTrace_append hprefix tailTrace_622677
  have hstable : (prefixWord ++ tailWord_622677).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_622677).length < 2 ^ (prefixWord ++ tailWord_622677).sum := by decide
  have hdescent : baseEnd_622677 < baseStart_622677 := by decide
  rcases family_descends (prefixWord ++ tailWord_622677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_622720 : List Nat := [2, 1, 1, 2, 1, 3, 1, 3, 2, 6]
def baseStart_622720 : Nat := 118140960795 + 622720 * 2 ^ 59
def prefixEnd_622720 : Nat := 4983230072969 + 3 ^ 40 * 622720 * 2
def baseEnd_622720 : Nat := 213169782111939225890779

theorem tailTrace_622720 : CollatzResearch.WordTrace tailWord_622720 prefixEnd_622720 213169782111939225890779 := by
  unfold tailWord_622720
  simp only [CollatzResearch.WordTrace]
  refine ⟨11356232151999633476992807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15141642869332844635990409 11356232151999633476992807)
  ·
    refine ⟨17034348227999450215489211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11356232151999633476992807 17034348227999450215489211)
    ·
      refine ⟨25551522341999175323233817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17034348227999450215489211 25551522341999175323233817)
      ·
        refine ⟨19163641756499381492425363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25551522341999175323233817 19163641756499381492425363)
        ·
          refine ⟨28745462634749072238638045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19163641756499381492425363 28745462634749072238638045)
          ·
            refine ⟨10779548488030902089489267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28745462634749072238638045 10779548488030902089489267)
            ·
              refine ⟨16169322732046353134233901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10779548488030902089489267 16169322732046353134233901)
              ·
                refine ⟨6063496024517382425337713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16169322732046353134233901 6063496024517382425337713)
                ·
                  refine ⟨4547622018388036819003285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6063496024517382425337713 4547622018388036819003285)
                  ·
                    refine ⟨213169782111939225890779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4547622018388036819003285 213169782111939225890779)
                    ·
                      rfl

theorem cell22_622720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 3, 2, 6].length) (baseStart_622720 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_622720 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_622720 prefixEnd_622720 := by exact prefixLift 622720
  have htrace : WordTrace (prefixWord ++ tailWord_622720) baseStart_622720 baseEnd_622720 := by
    simpa [prefixWord, tailWord_622720, baseEnd_622720] using wordTrace_append hprefix tailTrace_622720
  have hstable : (prefixWord ++ tailWord_622720).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_622720).length < 2 ^ (prefixWord ++ tailWord_622720).sum := by decide
  have hdescent : baseEnd_622720 < baseStart_622720 := by decide
  rcases family_descends (prefixWord ++ tailWord_622720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_622728 : List Nat := [2, 1, 3, 4, 1, 3, 2, 1, 2, 3]
def baseStart_622728 : Nat := 118140960795 + 622728 * 2 ^ 59
def prefixEnd_622728 : Nat := 4983230072969 + 3 ^ 40 * 622728 * 2
def baseEnd_622728 : Nat := 213172520675429871690755

theorem tailTrace_622728 : CollatzResearch.WordTrace tailWord_622728 prefixEnd_622728 213172520675429871690755 := by
  unfold tailWord_622728
  simp only [CollatzResearch.WordTrace]
  refine ⟨11356378043985142160138419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15141837391980189546851225 11356378043985142160138419)
  ·
    refine ⟨17034567065977713240207629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11356378043985142160138419 17034567065977713240207629)
    ·
      refine ⟨6387962649741642465077861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17034567065977713240207629 6387962649741642465077861)
      ·
        refine ⟨1197742996826557962202099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6387962649741642465077861 1197742996826557962202099)
        ·
          refine ⟨1796614495239836943303149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1197742996826557962202099 1796614495239836943303149)
          ·
            refine ⟨673730435714938853738681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1796614495239836943303149 673730435714938853738681)
            ·
              refine ⟨505297826786204140304011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 673730435714938853738681 505297826786204140304011)
              ·
                refine ⟨757946740179306210456017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 505297826786204140304011 757946740179306210456017)
                ·
                  refine ⟨568460055134479657842013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 757946740179306210456017 568460055134479657842013)
                  ·
                    refine ⟨213172520675429871690755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 568460055134479657842013 213172520675429871690755)
                    ·
                      rfl

theorem cell22_622728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 3, 2, 1, 2, 3].length) (baseStart_622728 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_622728 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_622728 prefixEnd_622728 := by exact prefixLift 622728
  have htrace : WordTrace (prefixWord ++ tailWord_622728) baseStart_622728 baseEnd_622728 := by
    simpa [prefixWord, tailWord_622728, baseEnd_622728] using wordTrace_append hprefix tailTrace_622728
  have hstable : (prefixWord ++ tailWord_622728).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_622728).length < 2 ^ (prefixWord ++ tailWord_622728).sum := by decide
  have hdescent : baseEnd_622728 < baseStart_622728 := by decide
  rcases family_descends (prefixWord ++ tailWord_622728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_622827 : List Nat := [1, 1, 1, 1, 2, 5, 2, 1, 4, 4]
def baseStart_622827 : Nat := 118140960795 + 622827 * 2 ^ 59
def prefixEnd_622827 : Nat := 4983230072969 + 3 ^ 40 * 622827 * 2
def baseEnd_622827 : Nat := 213206410398626613465451

theorem tailTrace_622827 : CollatzResearch.WordTrace tailWord_622827 prefixEnd_622827 213206410398626613465451 := by
  unfold tailWord_622827
  simp only [CollatzResearch.WordTrace]
  refine ⟨22716366914611624228130735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15144244609741082818753823 22716366914611624228130735)
  ·
    refine ⟨34074550371917436342196103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22716366914611624228130735 34074550371917436342196103)
    ·
      refine ⟨51111825557876154513294155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34074550371917436342196103 51111825557876154513294155)
      ·
        refine ⟨76667738336814231769941233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51111825557876154513294155 76667738336814231769941233)
        ·
          refine ⟨57500803752610673827455925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76667738336814231769941233 57500803752610673827455925)
          ·
            refine ⟨5390700351807250671323993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 57500803752610673827455925 5390700351807250671323993)
            ·
              refine ⟨4043025263855438003492995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5390700351807250671323993 4043025263855438003492995)
              ·
                refine ⟨6064537895783157005239493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4043025263855438003492995 6064537895783157005239493)
                ·
                  refine ⟨1137100855459341938482405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6064537895783157005239493 1137100855459341938482405)
                  ·
                    refine ⟨213206410398626613465451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1137100855459341938482405 213206410398626613465451)
                    ·
                      rfl

theorem cell22_622827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 2, 1, 4, 4].length) (baseStart_622827 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_622827 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_622827 prefixEnd_622827 := by exact prefixLift 622827
  have htrace : WordTrace (prefixWord ++ tailWord_622827) baseStart_622827 baseEnd_622827 := by
    simpa [prefixWord, tailWord_622827, baseEnd_622827] using wordTrace_append hprefix tailTrace_622827
  have hstable : (prefixWord ++ tailWord_622827).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_622827).length < 2 ^ (prefixWord ++ tailWord_622827).sum := by decide
  have hdescent : baseEnd_622827 < baseStart_622827 := by decide
  rcases family_descends (prefixWord ++ tailWord_622827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_622878 : List Nat := [4, 3, 2, 1, 1, 2, 1, 2, 2, 4]
def baseStart_622878 : Nat := 118140960795 + 622878 * 2 ^ 59
def prefixEnd_622878 : Nat := 4983230072969 + 3 ^ 40 * 622878 * 2
def baseEnd_622878 : Nat := 213223868740879480440295

theorem tailTrace_622878 : CollatzResearch.WordTrace tailWord_622878 prefixEnd_622878 213223868740879480440295 := by
  unfold tailWord_622878
  simp only [CollatzResearch.WordTrace]
  refine ⟨2839778379678357492279661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15145484691617906625491525 2839778379678357492279661)
  ·
    refine ⟨1064916892379384059604873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2839778379678357492279661 1064916892379384059604873)
    ·
      refine ⟨798687669284538044703655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1064916892379384059604873 798687669284538044703655)
      ·
        refine ⟨1198031503926807067055483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 798687669284538044703655 1198031503926807067055483)
        ·
          refine ⟨1797047255890210600583225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1198031503926807067055483 1797047255890210600583225)
          ·
            refine ⟨1347785441917657950437419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1797047255890210600583225 1347785441917657950437419)
            ·
              refine ⟨2021678162876486925656129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1347785441917657950437419 2021678162876486925656129)
              ·
                refine ⟨1516258622157365194242097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2021678162876486925656129 1516258622157365194242097)
                ·
                  refine ⟨1137193966618023895681573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1516258622157365194242097 1137193966618023895681573)
                  ·
                    refine ⟨213223868740879480440295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1137193966618023895681573 213223868740879480440295)
                    ·
                      rfl

theorem cell22_622878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 1, 2, 2, 4].length) (baseStart_622878 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_622878 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_622878 prefixEnd_622878 := by exact prefixLift 622878
  have htrace : WordTrace (prefixWord ++ tailWord_622878) baseStart_622878 baseEnd_622878 := by
    simpa [prefixWord, tailWord_622878, baseEnd_622878] using wordTrace_append hprefix tailTrace_622878
  have hstable : (prefixWord ++ tailWord_622878).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_622878).length < 2 ^ (prefixWord ++ tailWord_622878).sum := by decide
  have hdescent : baseEnd_622878 < baseStart_622878 := by decide
  rcases family_descends (prefixWord ++ tailWord_622878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_623015 : List Nat := [1, 1, 6, 1, 1, 3, 3, 1, 2, 3]
def baseStart_623015 : Nat := 118140960795 + 623015 * 2 ^ 59
def prefixEnd_623015 : Nat := 4983230072969 + 3 ^ 40 * 623015 * 2
def baseEnd_623015 : Nat := 213270766640656789764875

theorem tailTrace_623015 : CollatzResearch.WordTrace tailWord_623015 prefixEnd_623015 213270766640656789764875 := by
  unfold tailWord_623015
  simp only [CollatzResearch.WordTrace]
  refine ⟨22723223837930532335974499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15148815891953688223982999 22723223837930532335974499)
  ·
    refine ⟨34084835756895798503961749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22723223837930532335974499 34084835756895798503961749)
    ·
      refine ⟨1597726676104490554873207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 34084835756895798503961749 1597726676104490554873207)
      ·
        refine ⟨2396590014156735832309811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1597726676104490554873207 2396590014156735832309811)
        ·
          refine ⟨3594885021235103748464717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2396590014156735832309811 3594885021235103748464717)
          ·
            refine ⟨1348081882963163905674269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3594885021235103748464717 1348081882963163905674269)
            ·
              refine ⟨505530706111186464627851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1348081882963163905674269 505530706111186464627851)
              ·
                refine ⟨758296059166779696941777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 505530706111186464627851 758296059166779696941777)
                ·
                  refine ⟨568722044375084772706333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 758296059166779696941777 568722044375084772706333)
                  ·
                    refine ⟨213270766640656789764875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 568722044375084772706333 213270766640656789764875)
                    ·
                      rfl

theorem cell22_623015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 3, 1, 2, 3].length) (baseStart_623015 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_623015 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_623015 prefixEnd_623015 := by exact prefixLift 623015
  have htrace : WordTrace (prefixWord ++ tailWord_623015) baseStart_623015 baseEnd_623015 := by
    simpa [prefixWord, tailWord_623015, baseEnd_623015] using wordTrace_append hprefix tailTrace_623015
  have hstable : (prefixWord ++ tailWord_623015).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_623015).length < 2 ^ (prefixWord ++ tailWord_623015).sum := by decide
  have hdescent : baseEnd_623015 < baseStart_623015 := by decide
  rcases family_descends (prefixWord ++ tailWord_623015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_623026 : List Nat := [3, 2, 1, 1, 1, 1, 3, 4, 3, 3]
def baseStart_623026 : Nat := 118140960795 + 623026 * 2 ^ 59
def prefixEnd_623026 : Nat := 4983230072969 + 3 ^ 40 * 623026 * 2
def baseEnd_623026 : Nat := 213274532165456427739841

theorem tailTrace_623026 : CollatzResearch.WordTrace tailWord_623026 prefixEnd_623026 213274532165456427739841 := by
  unfold tailWord_623026
  simp only [CollatzResearch.WordTrace]
  refine ⟨5680906260222670303656233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15149083360593787476416621 5680906260222670303656233)
  ·
    refine ⟨4260679695167002727742175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5680906260222670303656233 4260679695167002727742175)
    ·
      refine ⟨6391019542750504091613263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4260679695167002727742175 6391019542750504091613263)
      ·
        refine ⟨9586529314125756137419895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6391019542750504091613263 9586529314125756137419895)
        ·
          refine ⟨14379793971188634206129843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9586529314125756137419895 14379793971188634206129843)
          ·
            refine ⟨21569690956782951309194765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14379793971188634206129843 21569690956782951309194765)
            ·
              refine ⟨8088634108793606740948037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21569690956782951309194765 8088634108793606740948037)
              ·
                refine ⟨1516618895398801263927757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8088634108793606740948037 1516618895398801263927757)
                ·
                  refine ⟨568732085774550473972909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1516618895398801263927757 568732085774550473972909)
                  ·
                    refine ⟨213274532165456427739841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 568732085774550473972909 213274532165456427739841)
                    ·
                      rfl

theorem cell22_623026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 4, 3, 3].length) (baseStart_623026 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_623026 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_623026 prefixEnd_623026 := by exact prefixLift 623026
  have htrace : WordTrace (prefixWord ++ tailWord_623026) baseStart_623026 baseEnd_623026 := by
    simpa [prefixWord, tailWord_623026, baseEnd_623026] using wordTrace_append hprefix tailTrace_623026
  have hstable : (prefixWord ++ tailWord_623026).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_623026).length < 2 ^ (prefixWord ++ tailWord_623026).sum := by decide
  have hdescent : baseEnd_623026 < baseStart_623026 := by decide
  rcases family_descends (prefixWord ++ tailWord_623026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_623060 : List Nat := [2, 4, 1, 2, 2, 3, 1, 1, 3, 3]
def baseStart_623060 : Nat := 118140960795 + 623060 * 2 ^ 59
def prefixEnd_623060 : Nat := 4983230072969 + 3 ^ 40 * 623060 * 2
def baseEnd_623060 : Nat := 213286171060291672389737

theorem tailTrace_623060 : CollatzResearch.WordTrace tailWord_623060 prefixEnd_623060 213286171060291672389737 := by
  unfold tailWord_623060
  simp only [CollatzResearch.WordTrace]
  refine ⟨11362432561383752510681317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15149910081845003347575089 11362432561383752510681317)
  ·
    refine ⟨2130456105259453595752747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11362432561383752510681317 2130456105259453595752747)
    ·
      refine ⟨3195684157889180393629121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2130456105259453595752747 3195684157889180393629121)
      ·
        refine ⟨2396763118416885295221841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3195684157889180393629121 2396763118416885295221841)
        ·
          refine ⟨1797572338812663971416381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2396763118416885295221841 1797572338812663971416381)
          ·
            refine ⟨674089627054748989281143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1797572338812663971416381 674089627054748989281143)
            ·
              refine ⟨1011134440582123483921715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 674089627054748989281143 1011134440582123483921715)
              ·
                refine ⟨1516701660873185225882573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1011134440582123483921715 1516701660873185225882573)
                ·
                  refine ⟨568763122827444459705965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1516701660873185225882573 568763122827444459705965)
                  ·
                    refine ⟨213286171060291672389737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 568763122827444459705965 213286171060291672389737)
                    ·
                      rfl

theorem cell22_623060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 3, 1, 1, 3, 3].length) (baseStart_623060 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_623060 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_623060 prefixEnd_623060 := by exact prefixLift 623060
  have htrace : WordTrace (prefixWord ++ tailWord_623060) baseStart_623060 baseEnd_623060 := by
    simpa [prefixWord, tailWord_623060, baseEnd_623060] using wordTrace_append hprefix tailTrace_623060
  have hstable : (prefixWord ++ tailWord_623060).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_623060).length < 2 ^ (prefixWord ++ tailWord_623060).sum := by decide
  have hdescent : baseEnd_623060 < baseStart_623060 := by decide
  rcases family_descends (prefixWord ++ tailWord_623060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_623084 : List Nat := [2, 2, 1, 1, 2, 1, 4, 1, 8]
def baseStart_623084 : Nat := 118140960795 + 623084 * 2 ^ 59
def prefixEnd_623084 : Nat := 4983230072969 + 3 ^ 40 * 623084 * 2
def baseEnd_623084 : Nat := 71098128916921203263221

theorem tailTrace_623084 : CollatzResearch.WordTrace tailWord_623084 prefixEnd_623084 71098128916921203263221 := by
  unfold tailWord_623084
  simp only [CollatzResearch.WordTrace]
  refine ⟨11362870237340278560118153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15150493649787038080157537 11362870237340278560118153)
  ·
    refine ⟨8522152678005208920088615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11362870237340278560118153 8522152678005208920088615)
    ·
      refine ⟨12783229017007813380132923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8522152678005208920088615 12783229017007813380132923)
      ·
        refine ⟨19174843525511720070199385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12783229017007813380132923 19174843525511720070199385)
        ·
          refine ⟨14381132644133790052649539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19174843525511720070199385 14381132644133790052649539)
          ·
            refine ⟨21571698966200685078974309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14381132644133790052649539 21571698966200685078974309)
            ·
              refine ⟨4044693556162628452307683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21571698966200685078974309 4044693556162628452307683)
              ·
                refine ⟨6067040334243942678461525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4044693556162628452307683 6067040334243942678461525)
                ·
                  refine ⟨71098128916921203263221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 6067040334243942678461525 71098128916921203263221)
                  ·
                    rfl

theorem cell22_623084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 8].length) (baseStart_623084 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_623084 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_623084 prefixEnd_623084 := by exact prefixLift 623084
  have htrace : WordTrace (prefixWord ++ tailWord_623084) baseStart_623084 baseEnd_623084 := by
    simpa [prefixWord, tailWord_623084, baseEnd_623084] using wordTrace_append hprefix tailTrace_623084
  have hstable : (prefixWord ++ tailWord_623084).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_623084).length < 2 ^ (prefixWord ++ tailWord_623084).sum := by decide
  have hdescent : baseEnd_623084 < baseStart_623084 := by decide
  rcases family_descends (prefixWord ++ tailWord_623084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_623103 : List Nat := [1, 1, 2, 2, 1, 2, 7, 1, 1, 4]
def baseStart_623103 : Nat := 118140960795 + 623103 * 2 ^ 59
def prefixEnd_623103 : Nat := 4983230072969 + 3 ^ 40 * 623103 * 2
def baseEnd_623103 : Nat := 213300890839053893564605

theorem tailTrace_623103 : CollatzResearch.WordTrace tailWord_623103 prefixEnd_623103 213300890839053893564605 := by
  unfold tailWord_623103
  simp only [CollatzResearch.WordTrace]
  refine ⟨22726433461611723365177963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15150955641074482243451975 22726433461611723365177963)
  ·
    refine ⟨34089650192417585047766945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22726433461611723365177963 34089650192417585047766945)
    ·
      refine ⟨25567237644313188785825209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34089650192417585047766945 25567237644313188785825209)
      ·
        refine ⟨19175428233234891589368907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25567237644313188785825209 19175428233234891589368907)
        ·
          refine ⟨28763142349852337384053361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19175428233234891589368907 28763142349852337384053361)
          ·
            refine ⟨21572356762389253038040021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28763142349852337384053361 21572356762389253038040021)
            ·
              refine ⟨505602111618498118079063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 21572356762389253038040021 505602111618498118079063)
              ·
                refine ⟨758403167427747177118595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 505602111618498118079063 758403167427747177118595)
                ·
                  refine ⟨1137604751141620765677893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 758403167427747177118595 1137604751141620765677893)
                  ·
                    refine ⟨213300890839053893564605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1137604751141620765677893 213300890839053893564605)
                    ·
                      rfl

theorem cell22_623103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 7, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 7, 1, 1, 4].length) (baseStart_623103 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_623103 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_623103 prefixEnd_623103 := by exact prefixLift 623103
  have htrace : WordTrace (prefixWord ++ tailWord_623103) baseStart_623103 baseEnd_623103 := by
    simpa [prefixWord, tailWord_623103, baseEnd_623103] using wordTrace_append hprefix tailTrace_623103
  have hstable : (prefixWord ++ tailWord_623103).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_623103).length < 2 ^ (prefixWord ++ tailWord_623103).sum := by decide
  have hdescent : baseEnd_623103 < baseStart_623103 := by decide
  rcases family_descends (prefixWord ++ tailWord_623103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_623133 : List Nat := [1, 4, 2, 2, 1, 3, 2, 1, 1, 5]
def baseStart_623133 : Nat := 118140960795 + 623133 * 2 ^ 59
def prefixEnd_623133 : Nat := 4983230072969 + 3 ^ 40 * 623133 * 2
def baseEnd_623133 : Nat := 213311160452143815314513

theorem tailTrace_623133 : CollatzResearch.WordTrace tailWord_623133 prefixEnd_623133 213311160452143815314513 := by
  unfold tailWord_623133
  simp only [CollatzResearch.WordTrace]
  refine ⟨22727527651503038488770053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15151685101002025659180035 22727527651503038488770053)
  ·
    refine ⟨4261411434656819716644385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22727527651503038488770053 4261411434656819716644385)
    ·
      refine ⟨3196058575992614787483289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4261411434656819716644385 3196058575992614787483289)
      ·
        refine ⟨2397043931994461090612467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3196058575992614787483289 2397043931994461090612467)
        ·
          refine ⟨3595565897991691635918701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2397043931994461090612467 3595565897991691635918701)
          ·
            refine ⟨1348337211746884363469513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3595565897991691635918701 1348337211746884363469513)
            ·
              refine ⟨1011252908810163272602135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1348337211746884363469513 1011252908810163272602135)
              ·
                refine ⟨1516879363215244908903203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1011252908810163272602135 1516879363215244908903203)
                ·
                  refine ⟨2275319044822867363354805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1516879363215244908903203 2275319044822867363354805)
                  ·
                    refine ⟨213311160452143815314513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2275319044822867363354805 213311160452143815314513)
                    ·
                      rfl

theorem cell22_623133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 2, 1, 1, 5].length) (baseStart_623133 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_623133 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_623133 prefixEnd_623133 := by exact prefixLift 623133
  have htrace : WordTrace (prefixWord ++ tailWord_623133) baseStart_623133 baseEnd_623133 := by
    simpa [prefixWord, tailWord_623133, baseEnd_623133] using wordTrace_append hprefix tailTrace_623133
  have hstable : (prefixWord ++ tailWord_623133).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_623133).length < 2 ^ (prefixWord ++ tailWord_623133).sum := by decide
  have hdescent : baseEnd_623133 < baseStart_623133 := by decide
  rcases family_descends (prefixWord ++ tailWord_623133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_623178 : List Nat := [3, 1, 2, 1, 1, 4, 1, 3, 3, 3]
def baseStart_623178 : Nat := 118140960795 + 623178 * 2 ^ 59
def prefixEnd_623178 : Nat := 4983230072969 + 3 ^ 40 * 623178 * 2
def baseEnd_623178 : Nat := 213326564871778697939375

theorem tailTrace_623178 : CollatzResearch.WordTrace tailWord_623178 prefixEnd_623178 213326564871778697939375 := by
  unfold tailWord_623178
  simp only [CollatzResearch.WordTrace]
  refine ⟨5682292234085002793539547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15152779290893340782772125 5682292234085002793539547)
  ·
    refine ⟨8523438351127504190309321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5682292234085002793539547 8523438351127504190309321)
    ·
      refine ⟨6392578763345628142731991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8523438351127504190309321 6392578763345628142731991)
      ·
        refine ⟨9588868145018442214097987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6392578763345628142731991 9588868145018442214097987)
        ·
          refine ⟨14383302217527663321146981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9588868145018442214097987 14383302217527663321146981)
          ·
            refine ⟨2696869165786436872715059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14383302217527663321146981 2696869165786436872715059)
            ·
              refine ⟨4045303748679655309072589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2696869165786436872715059 4045303748679655309072589)
              ·
                refine ⟨1516988905754870740902221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4045303748679655309072589 1516988905754870740902221)
                ·
                  refine ⟨568870839658076527838333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1516988905754870740902221 568870839658076527838333)
                  ·
                    refine ⟨213326564871778697939375, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 568870839658076527838333 213326564871778697939375)
                    ·
                      rfl

theorem cell22_623178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 1, 3, 3, 3].length) (baseStart_623178 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_623178 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_623178 prefixEnd_623178 := by exact prefixLift 623178
  have htrace : WordTrace (prefixWord ++ tailWord_623178) baseStart_623178 baseEnd_623178 := by
    simpa [prefixWord, tailWord_623178, baseEnd_623178] using wordTrace_append hprefix tailTrace_623178
  have hstable : (prefixWord ++ tailWord_623178).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_623178).length < 2 ^ (prefixWord ++ tailWord_623178).sum := by decide
  have hdescent : baseEnd_623178 < baseStart_623178 := by decide
  rcases family_descends (prefixWord ++ tailWord_623178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_623229 : List Nat := [1, 4, 1, 1, 5, 1, 3, 2, 1, 3]
def baseStart_623229 : Nat := 118140960795 + 623229 * 2 ^ 59
def prefixEnd_623229 : Nat := 4983230072969 + 3 ^ 40 * 623229 * 2
def baseEnd_623229 : Nat := 213344023214031564914219

theorem tailTrace_623229 : CollatzResearch.WordTrace tailWord_623229 prefixEnd_623229 213344023214031564914219 := by
  unfold tailWord_623229
  simp only [CollatzResearch.WordTrace]
  refine ⟨22731029059155246884264741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15154019372770164589509827 22731029059155246884264741)
  ·
    refine ⟨4262067948591608790799639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22731029059155246884264741 4262067948591608790799639)
    ·
      refine ⟨6393101922887413186199459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4262067948591608790799639 6393101922887413186199459)
      ·
        refine ⟨9589652884331119779299189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6393101922887413186199459 9589652884331119779299189)
        ·
          refine ⟨899029957906042479309299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 9589652884331119779299189 899029957906042479309299)
          ·
            refine ⟨1348544936859063718963949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 899029957906042479309299 1348544936859063718963949)
            ·
              refine ⟨505704351322148894611481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1348544936859063718963949 505704351322148894611481)
              ·
                refine ⟨379278263491611670958611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 505704351322148894611481 379278263491611670958611)
                ·
                  refine ⟨568917395237417506437917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 379278263491611670958611 568917395237417506437917)
                  ·
                    refine ⟨213344023214031564914219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 568917395237417506437917 213344023214031564914219)
                    ·
                      rfl

theorem cell22_623229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 3, 2, 1, 3].length) (baseStart_623229 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_623229 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_623229 prefixEnd_623229 := by exact prefixLift 623229
  have htrace : WordTrace (prefixWord ++ tailWord_623229) baseStart_623229 baseEnd_623229 := by
    simpa [prefixWord, tailWord_623229, baseEnd_623229] using wordTrace_append hprefix tailTrace_623229
  have hstable : (prefixWord ++ tailWord_623229).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_623229).length < 2 ^ (prefixWord ++ tailWord_623229).sum := by decide
  have hdescent : baseEnd_623229 < baseStart_623229 := by decide
  rcases family_descends (prefixWord ++ tailWord_623229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_623242 : List Nat := [3, 1, 2, 3, 3, 2, 2, 1, 5]
def baseStart_623242 : Nat := 118140960795 + 623242 * 2 ^ 59
def prefixEnd_623242 : Nat := 4983230072969 + 3 ^ 40 * 623242 * 2
def baseEnd_623242 : Nat := 71116157793234621446393

theorem tailTrace_623242 : CollatzResearch.WordTrace tailWord_623242 prefixEnd_623242 71116157793234621446393 := by
  unfold tailWord_623242
  simp only [CollatzResearch.WordTrace]
  refine ⟨5682875802027037526121995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15154335472072100069658653 5682875802027037526121995)
  ·
    refine ⟨8524313703040556289182993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5682875802027037526121995 8524313703040556289182993)
    ·
      refine ⟨6393235277280417216887245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8524313703040556289182993 6393235277280417216887245)
      ·
        refine ⟨2397463228980156456332717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6393235277280417216887245 2397463228980156456332717)
        ·
          refine ⟨899048710867558671124769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2397463228980156456332717 899048710867558671124769)
          ·
            refine ⟨674286533150669003343577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 899048710867558671124769 674286533150669003343577)
            ·
              refine ⟨505714899863001752507683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 674286533150669003343577 505714899863001752507683)
              ·
                refine ⟨758572349794502628761525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 505714899863001752507683 758572349794502628761525)
                ·
                  refine ⟨71116157793234621446393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 758572349794502628761525 71116157793234621446393)
                  ·
                    rfl

theorem cell22_623242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 2, 2, 1, 5].length) (baseStart_623242 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_623242 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_623242 prefixEnd_623242 := by exact prefixLift 623242
  have htrace : WordTrace (prefixWord ++ tailWord_623242) baseStart_623242 baseEnd_623242 := by
    simpa [prefixWord, tailWord_623242, baseEnd_623242] using wordTrace_append hprefix tailTrace_623242
  have hstable : (prefixWord ++ tailWord_623242).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_623242).length < 2 ^ (prefixWord ++ tailWord_623242).sum := by decide
  have hdescent : baseEnd_623242 < baseStart_623242 := by decide
  rcases family_descends (prefixWord ++ tailWord_623242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_623268 : List Nat := [2, 3, 1, 2, 2, 1, 3, 2, 1, 5]
def baseStart_623268 : Nat := 118140960795 + 623268 * 2 ^ 59
def prefixEnd_623268 : Nat := 4983230072969 + 3 ^ 40 * 623268 * 2
def baseEnd_623268 : Nat := 213357373711048463189099

theorem tailTrace_623268 : CollatzResearch.WordTrace tailWord_623268 prefixEnd_623268 213357373711048463189099 := by
  unfold tailWord_623268
  simp only [CollatzResearch.WordTrace]
  refine ⟨11366225753006978272467229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15154967670675971029956305 11366225753006978272467229)
  ·
    refine ⟨4262334657377616852175211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11366225753006978272467229 4262334657377616852175211)
    ·
      refine ⟨6393501986066425278262817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4262334657377616852175211 6393501986066425278262817)
      ·
        refine ⟨4795126489549818958697113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6393501986066425278262817 4795126489549818958697113)
        ·
          refine ⟨3596344867162364219022835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4795126489549818958697113 3596344867162364219022835)
          ·
            refine ⟨5394517300743546328534253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3596344867162364219022835 5394517300743546328534253)
            ·
              refine ⟨2022943987778829873200345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5394517300743546328534253 2022943987778829873200345)
              ·
                refine ⟨1517207990834122404900259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2022943987778829873200345 1517207990834122404900259)
                ·
                  refine ⟨2275811986251183607350389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1517207990834122404900259 2275811986251183607350389)
                  ·
                    refine ⟨213357373711048463189099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2275811986251183607350389 213357373711048463189099)
                    ·
                      rfl

theorem cell22_623268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 3, 2, 1, 5].length) (baseStart_623268 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_623268 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_623268 prefixEnd_623268 := by exact prefixLift 623268
  have htrace : WordTrace (prefixWord ++ tailWord_623268) baseStart_623268 baseEnd_623268 := by
    simpa [prefixWord, tailWord_623268, baseEnd_623268] using wordTrace_append hprefix tailTrace_623268
  have hstable : (prefixWord ++ tailWord_623268).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_623268).length < 2 ^ (prefixWord ++ tailWord_623268).sum := by decide
  have hdescent : baseEnd_623268 < baseStart_623268 := by decide
  rcases family_descends (prefixWord ++ tailWord_623268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_623283 : List Nat := [1, 1, 1, 2, 3, 4, 2, 2, 2, 4]
def baseStart_623283 : Nat := 118140960795 + 623283 * 2 ^ 59
def prefixEnd_623283 : Nat := 4983230072969 + 3 ^ 40 * 623283 * 2
def baseEnd_623283 : Nat := 213362508517593424064053

theorem tailTrace_623283 : CollatzResearch.WordTrace tailWord_623283 prefixEnd_623283 213362508517593424064053 := by
  unfold tailWord_623283
  simp only [CollatzResearch.WordTrace]
  refine ⟨22732998600959614106730503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15155332400639742737820335 22732998600959614106730503)
  ·
    refine ⟨34099497901439421160095755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22732998600959614106730503 34099497901439421160095755)
    ·
      refine ⟨51149246852159131740143633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34099497901439421160095755 51149246852159131740143633)
      ·
        refine ⟨38361935139119348805107725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51149246852159131740143633 38361935139119348805107725)
        ·
          refine ⟨14385725677169755801915397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38361935139119348805107725 14385725677169755801915397)
          ·
            refine ⟨2697323564469329212859137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14385725677169755801915397 2697323564469329212859137)
            ·
              refine ⟨2022992673351996909644353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2697323564469329212859137 2022992673351996909644353)
              ·
                refine ⟨1517244505013997682233265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2022992673351996909644353 1517244505013997682233265)
                ·
                  refine ⟨1137933378760498261674949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1517244505013997682233265 1137933378760498261674949)
                  ·
                    refine ⟨213362508517593424064053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1137933378760498261674949 213362508517593424064053)
                    ·
                      rfl

theorem cell22_623283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 2, 2, 2, 4].length) (baseStart_623283 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_623283 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_623283 prefixEnd_623283 := by exact prefixLift 623283
  have htrace : WordTrace (prefixWord ++ tailWord_623283) baseStart_623283 baseEnd_623283 := by
    simpa [prefixWord, tailWord_623283, baseEnd_623283] using wordTrace_append hprefix tailTrace_623283
  have hstable : (prefixWord ++ tailWord_623283).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_623283).length < 2 ^ (prefixWord ++ tailWord_623283).sum := by decide
  have hdescent : baseEnd_623283 < baseStart_623283 := by decide
  rcases family_descends (prefixWord ++ tailWord_623283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_623343 : List Nat := [1, 1, 2, 1, 5, 3, 1, 1, 7]
def baseStart_623343 : Nat := 118140960795 + 623343 * 2 ^ 59
def prefixEnd_623343 : Nat := 4983230072969 + 3 ^ 40 * 623343 * 2
def baseEnd_623343 : Nat := 71127682581257755854623

theorem tailTrace_623343 : CollatzResearch.WordTrace tailWord_623343 prefixEnd_623343 71127682581257755854623 := by
  unfold tailWord_623343
  simp only [CollatzResearch.WordTrace]
  refine ⟨22735186980742244353914683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15156791320494829569276455 22735186980742244353914683)
  ·
    refine ⟨34102780471113366530872025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22735186980742244353914683 34102780471113366530872025)
    ·
      refine ⟨25577085353335024898154019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34102780471113366530872025 25577085353335024898154019)
      ·
        refine ⟨38365628030002537347231029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25577085353335024898154019 38365628030002537347231029)
        ·
          refine ⟨3596777627812737876302909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 38365628030002537347231029 3596777627812737876302909)
          ·
            refine ⟨1348791610429776703613591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3596777627812737876302909 1348791610429776703613591)
            ·
              refine ⟨2023187415644665055420387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1348791610429776703613591 2023187415644665055420387)
              ·
                refine ⟨3034781123466997583130581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2023187415644665055420387 3034781123466997583130581)
                ·
                  refine ⟨71127682581257755854623, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3034781123466997583130581 71127682581257755854623)
                  ·
                    rfl

theorem cell22_623343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 1, 1, 7].length) (baseStart_623343 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_623343 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_623343 prefixEnd_623343 := by exact prefixLift 623343
  have htrace : WordTrace (prefixWord ++ tailWord_623343) baseStart_623343 baseEnd_623343 := by
    simpa [prefixWord, tailWord_623343, baseEnd_623343] using wordTrace_append hprefix tailTrace_623343
  have hstable : (prefixWord ++ tailWord_623343).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_623343).length < 2 ^ (prefixWord ++ tailWord_623343).sum := by decide
  have hdescent : baseEnd_623343 < baseStart_623343 := by decide
  rcases family_descends (prefixWord ++ tailWord_623343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_623433 : List Nat := [1, 2, 1, 1, 2, 5, 2, 8]
def baseStart_623433 : Nat := 118140960795 + 623433 * 2 ^ 59
def prefixEnd_623433 : Nat := 4983230072969 + 3 ^ 40 * 623433 * 2
def baseEnd_623433 : Nat := 23712650731449225868177

theorem tailTrace_623433 : CollatzResearch.WordTrace tailWord_623433 prefixEnd_623433 23712650731449225868177 := by
  unfold tailWord_623433
  simp only [CollatzResearch.WordTrace]
  refine ⟨22738469550416189724690953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15158979700277459816460635 22738469550416189724690953)
  ·
    refine ⟨17053852162812142293518215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22738469550416189724690953 17053852162812142293518215)
    ·
      refine ⟨25580778244218213440277323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17053852162812142293518215 25580778244218213440277323)
      ·
        refine ⟨38371167366327320160415985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25580778244218213440277323 38371167366327320160415985)
        ·
          refine ⟨28778375524745490120311989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38371167366327320160415985 28778375524745490120311989)
          ·
            refine ⟨2697972705444889698779249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 28778375524745490120311989 2697972705444889698779249)
            ·
              refine ⟨2023479529083667274084437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2697972705444889698779249 2023479529083667274084437)
              ·
                refine ⟨23712650731449225868177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2023479529083667274084437 23712650731449225868177)
                ·
                  rfl

theorem cell22_623433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 2, 8].length) (baseStart_623433 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_623433 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_623433 prefixEnd_623433 := by exact prefixLift 623433
  have htrace : WordTrace (prefixWord ++ tailWord_623433) baseStart_623433 baseEnd_623433 := by
    simpa [prefixWord, tailWord_623433, baseEnd_623433] using wordTrace_append hprefix tailTrace_623433
  have hstable : (prefixWord ++ tailWord_623433).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_623433).length < 2 ^ (prefixWord ++ tailWord_623433).sum := by decide
  have hdescent : baseEnd_623433 < baseStart_623433 := by decide
  rcases family_descends (prefixWord ++ tailWord_623433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_623452 : List Nat := [2, 2, 4, 2, 1, 1, 2, 2, 2, 4]
def baseStart_623452 : Nat := 118140960795 + 623452 * 2 ^ 59
def prefixEnd_623452 : Nat := 4983230072969 + 3 ^ 40 * 623452 * 2
def baseEnd_623452 : Nat := 213420360671333316588535

theorem tailTrace_623452 : CollatzResearch.WordTrace tailWord_623452 prefixEnd_623452 213420360671333316588535 := by
  unfold tailWord_623452
  simp only [CollatzResearch.WordTrace]
  refine ⟨11369581268673677984816305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15159441691564903979755073 11369581268673677984816305)
  ·
    refine ⟨8527185951505258488612229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11369581268673677984816305 8527185951505258488612229)
    ·
      refine ⟨1598847365907235966614793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8527185951505258488612229 1598847365907235966614793)
      ·
        refine ⟨1199135524430426974961095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1598847365907235966614793 1199135524430426974961095)
        ·
          refine ⟨1798703286645640462441643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1199135524430426974961095 1798703286645640462441643)
          ·
            refine ⟨2698054929968460693662465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1798703286645640462441643 2698054929968460693662465)
            ·
              refine ⟨2023541197476345520246849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2698054929968460693662465 2023541197476345520246849)
              ·
                refine ⟨1517655898107259140185137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2023541197476345520246849 1517655898107259140185137)
                ·
                  refine ⟨1138241923580444355138853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1517655898107259140185137 1138241923580444355138853)
                  ·
                    refine ⟨213420360671333316588535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1138241923580444355138853 213420360671333316588535)
                    ·
                      rfl

theorem cell22_623452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 2, 2, 2, 4].length) (baseStart_623452 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_623452 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_623452 prefixEnd_623452 := by exact prefixLift 623452
  have htrace : WordTrace (prefixWord ++ tailWord_623452) baseStart_623452 baseEnd_623452 := by
    simpa [prefixWord, tailWord_623452, baseEnd_623452] using wordTrace_append hprefix tailTrace_623452
  have hstable : (prefixWord ++ tailWord_623452).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_623452).length < 2 ^ (prefixWord ++ tailWord_623452).sum := by decide
  have hdescent : baseEnd_623452 < baseStart_623452 := by decide
  rcases family_descends (prefixWord ++ tailWord_623452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_623486 : List Nat := [4, 2, 3, 1, 2, 2, 1, 1, 2, 4]
def baseStart_623486 : Nat := 118140960795 + 623486 * 2 ^ 59
def prefixEnd_623486 : Nat := 4983230072969 + 3 ^ 40 * 623486 * 2
def baseEnd_623486 : Nat := 213431999566168561238431

theorem tailTrace_623486 : CollatzResearch.WordTrace tailWord_623486 prefixEnd_623486 213431999566168561238431 := by
  unfold tailWord_623486
  simp only [CollatzResearch.WordTrace]
  refine ⟨2842550327403022472046289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15160268412816119850913541 2842550327403022472046289)
  ·
    refine ⟨2131912745552266854034717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2842550327403022472046289 2131912745552266854034717)
    ·
      refine ⟨799467279582100070263019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2131912745552266854034717 799467279582100070263019)
      ·
        refine ⟨1199200919373150105394529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 799467279582100070263019 1199200919373150105394529)
        ·
          refine ⟨899400689529862579045897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1199200919373150105394529 899400689529862579045897)
          ·
            refine ⟨674550517147396934284423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 899400689529862579045897 674550517147396934284423)
            ·
              refine ⟨1011825775721095401426635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 674550517147396934284423 1011825775721095401426635)
              ·
                refine ⟨1517738663581643102139953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1011825775721095401426635 1517738663581643102139953)
                ·
                  refine ⟨1138303997686232326604965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1517738663581643102139953 1138303997686232326604965)
                  ·
                    refine ⟨213431999566168561238431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1138303997686232326604965 213431999566168561238431)
                    ·
                      rfl

theorem cell22_623486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 2, 1, 1, 2, 4].length) (baseStart_623486 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_623486 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_623486 prefixEnd_623486 := by exact prefixLift 623486
  have htrace : WordTrace (prefixWord ++ tailWord_623486) baseStart_623486 baseEnd_623486 := by
    simpa [prefixWord, tailWord_623486, baseEnd_623486] using wordTrace_append hprefix tailTrace_623486
  have hstable : (prefixWord ++ tailWord_623486).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_623486).length < 2 ^ (prefixWord ++ tailWord_623486).sum := by decide
  have hdescent : baseEnd_623486 < baseStart_623486 := by decide
  rcases family_descends (prefixWord ++ tailWord_623486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_623574 : List Nat := [5, 2, 1, 1, 2, 1, 3, 1, 6]
def baseStart_623574 : Nat := 118140960795 + 623574 * 2 ^ 59
def prefixEnd_623574 : Nat := 4983230072969 + 3 ^ 40 * 623574 * 2
def baseEnd_623574 : Nat := 71154041254855221679387

theorem tailTrace_623574 : CollatzResearch.WordTrace tailWord_623574 prefixEnd_623574 71154041254855221679387 := by
  unfold tailWord_623574
  simp only [CollatzResearch.WordTrace]
  refine ⟨1421475765181585675348361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 15162408161936913870382517 1421475765181585675348361)
  ·
    refine ⟨1066106823886189256511271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1421475765181585675348361 1066106823886189256511271)
    ·
      refine ⟨1599160235829283884766907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1066106823886189256511271 1599160235829283884766907)
      ·
        refine ⟨2398740353743925827150361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1599160235829283884766907 2398740353743925827150361)
        ·
          refine ⟨1799055265307944370362771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2398740353743925827150361 1799055265307944370362771)
          ·
            refine ⟨2698582897961916555544157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1799055265307944370362771 2698582897961916555544157)
            ·
              refine ⟨1011968586735718708329059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2698582897961916555544157 1011968586735718708329059)
              ·
                refine ⟨1517952880103578062493589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1011968586735718708329059 1517952880103578062493589)
                ·
                  refine ⟨71154041254855221679387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1517952880103578062493589 71154041254855221679387)
                  ·
                    rfl

theorem cell22_623574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 3, 1, 6].length) (baseStart_623574 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_623574 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_623574 prefixEnd_623574 := by exact prefixLift 623574
  have htrace : WordTrace (prefixWord ++ tailWord_623574) baseStart_623574 baseEnd_623574 := by
    simpa [prefixWord, tailWord_623574, baseEnd_623574] using wordTrace_append hprefix tailTrace_623574
  have hstable : (prefixWord ++ tailWord_623574).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_623574).length < 2 ^ (prefixWord ++ tailWord_623574).sum := by decide
  have hdescent : baseEnd_623574 < baseStart_623574 := by decide
  rcases family_descends (prefixWord ++ tailWord_623574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_623647 : List Nat := [1, 1, 2, 4, 1, 3, 2, 3, 5]
def baseStart_623647 : Nat := 118140960795 + 623647 * 2 ^ 59
def prefixEnd_623647 : Nat := 4983230072969 + 3 ^ 40 * 623647 * 2
def baseEnd_623647 : Nat := 71162371052139269320979

theorem tailTrace_623647 : CollatzResearch.WordTrace tailWord_623647 prefixEnd_623647 71162371052139269320979 := by
  unfold tailWord_623647
  simp only [CollatzResearch.WordTrace]
  refine ⟨22746274771640904272981195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15164183181093936181987463 22746274771640904272981195)
  ·
    refine ⟨34119412157461356409471793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22746274771640904272981195 34119412157461356409471793)
    ·
      refine ⟨25589559118096017307103845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34119412157461356409471793 25589559118096017307103845)
      ·
        refine ⟨4798042334643003245081971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25589559118096017307103845 4798042334643003245081971)
        ·
          refine ⟨7197063501964504867622957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4798042334643003245081971 7197063501964504867622957)
          ·
            refine ⟨2698898813236689325358609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7197063501964504867622957 2698898813236689325358609)
            ·
              refine ⟨2024174109927516994018957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2698898813236689325358609 2024174109927516994018957)
              ·
                refine ⟨759065291222818872757109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2024174109927516994018957 759065291222818872757109)
                ·
                  refine ⟨71162371052139269320979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 759065291222818872757109 71162371052139269320979)
                  ·
                    rfl

theorem cell22_623647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 2, 3, 5].length) (baseStart_623647 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_623647 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_623647 prefixEnd_623647 := by exact prefixLift 623647
  have htrace : WordTrace (prefixWord ++ tailWord_623647) baseStart_623647 baseEnd_623647 := by
    simpa [prefixWord, tailWord_623647, baseEnd_623647] using wordTrace_append hprefix tailTrace_623647
  have hstable : (prefixWord ++ tailWord_623647).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_623647).length < 2 ^ (prefixWord ++ tailWord_623647).sum := by decide
  have hdescent : baseEnd_623647 < baseStart_623647 := by decide
  rcases family_descends (prefixWord ++ tailWord_623647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_623662 : List Nat := [4, 1, 3, 1, 1, 1, 1, 2, 1, 7]
def baseStart_623662 : Nat := 118140960795 + 623662 * 2 ^ 59
def prefixEnd_623662 : Nat := 4983230072969 + 3 ^ 40 * 623662 * 2
def baseEnd_623662 : Nat := 213492247962962768837891

theorem tailTrace_623662 : CollatzResearch.WordTrace tailWord_623662 prefixEnd_623662 213492247962962768837891 := by
  unfold tailWord_623662
  simp only [CollatzResearch.WordTrace]
  refine ⟨2843352733323320229347155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15164547911057707889851493 2843352733323320229347155)
  ·
    refine ⟨4265029099984980344020733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2843352733323320229347155 4265029099984980344020733)
    ·
      refine ⟨1599385912494367629007775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4265029099984980344020733 1599385912494367629007775)
      ·
        refine ⟨2399078868741551443511663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1599385912494367629007775 2399078868741551443511663)
        ·
          refine ⟨3598618303112327165267495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2399078868741551443511663 3598618303112327165267495)
          ·
            refine ⟨5397927454668490747901243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3598618303112327165267495 5397927454668490747901243)
            ·
              refine ⟨8096891182002736121851865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5397927454668490747901243 8096891182002736121851865)
              ·
                refine ⟨6072668386502052091388899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8096891182002736121851865 6072668386502052091388899)
                ·
                  refine ⟨9109002579753078137083349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6072668386502052091388899 9109002579753078137083349)
                  ·
                    refine ⟨213492247962962768837891, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 9109002579753078137083349 213492247962962768837891)
                    ·
                      rfl

theorem cell22_623662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 2, 1, 7].length) (baseStart_623662 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_623662 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_623662 prefixEnd_623662 := by exact prefixLift 623662
  have htrace : WordTrace (prefixWord ++ tailWord_623662) baseStart_623662 baseEnd_623662 := by
    simpa [prefixWord, tailWord_623662, baseEnd_623662] using wordTrace_append hprefix tailTrace_623662
  have hstable : (prefixWord ++ tailWord_623662).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_623662).length < 2 ^ (prefixWord ++ tailWord_623662).sum := by decide
  have hdescent : baseEnd_623662 < baseStart_623662 := by decide
  rcases family_descends (prefixWord ++ tailWord_623662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_623668 : List Nat := [2, 5, 1, 2, 1, 1, 1, 5, 1, 3]
def baseStart_623668 : Nat := 118140960795 + 623668 * 2 ^ 59
def prefixEnd_623668 : Nat := 4983230072969 + 3 ^ 40 * 623668 * 2
def baseEnd_623668 : Nat := 213494301885580753187873

theorem tailTrace_623668 : CollatzResearch.WordTrace tailWord_623668 prefixEnd_623668 213494301885580753187873 := by
  unfold tailWord_623668
  simp only [CollatzResearch.WordTrace]
  refine ⟨11373520352282412429747829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15164693803043216572997105 11373520352282412429747829)
  ·
    refine ⟨1066267533026476165288859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 11373520352282412429747829 1066267533026476165288859)
    ·
      refine ⟨1599401299539714247933289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1066267533026476165288859 1599401299539714247933289)
      ·
        refine ⟨1199550974654785685949967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1599401299539714247933289 1199550974654785685949967)
        ·
          refine ⟨1799326461982178528924951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1199550974654785685949967 1799326461982178528924951)
          ·
            refine ⟨2698989692973267793387427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1799326461982178528924951 2698989692973267793387427)
            ·
              refine ⟨4048484539459901690081141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2698989692973267793387427 4048484539459901690081141)
              ·
                refine ⟨379545425574365783445107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4048484539459901690081141 379545425574365783445107)
                ·
                  refine ⟨569318138361548675167661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 379545425574365783445107 569318138361548675167661)
                  ·
                    refine ⟨213494301885580753187873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 569318138361548675167661 213494301885580753187873)
                    ·
                      rfl

theorem cell22_623668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 1, 5, 1, 3].length) (baseStart_623668 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_623668 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_623668 prefixEnd_623668 := by exact prefixLift 623668
  have htrace : WordTrace (prefixWord ++ tailWord_623668) baseStart_623668 baseEnd_623668 := by
    simpa [prefixWord, tailWord_623668, baseEnd_623668] using wordTrace_append hprefix tailTrace_623668
  have hstable : (prefixWord ++ tailWord_623668).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_623668).length < 2 ^ (prefixWord ++ tailWord_623668).sum := by decide
  have hdescent : baseEnd_623668 < baseStart_623668 := by decide
  rcases family_descends (prefixWord ++ tailWord_623668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_623681 : List Nat := [1, 2, 5, 1, 3, 2, 1, 2, 5]
def baseStart_623681 : Nat := 118140960795 + 623681 * 2 ^ 59
def prefixEnd_623681 : Nat := 4983230072969 + 3 ^ 40 * 623681 * 2
def baseEnd_623681 : Nat := 71166250683751017537611

theorem tailTrace_623681 : CollatzResearch.WordTrace tailWord_623681 prefixEnd_623681 71166250683751017537611 := by
  unfold tailWord_623681
  simp only [CollatzResearch.WordTrace]
  refine ⟨22747514853517728079718897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15165009902345152053145931 22747514853517728079718897)
  ·
    refine ⟨17060636140138296059789173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22747514853517728079718897 17060636140138296059789173)
    ·
      refine ⟨1599434638137965255605235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 17060636140138296059789173 1599434638137965255605235)
      ·
        refine ⟨2399151957206947883407853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1599434638137965255605235 2399151957206947883407853)
        ·
          refine ⟨899681983952605456277945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2399151957206947883407853 899681983952605456277945)
          ·
            refine ⟨674761487964454092208459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 899681983952605456277945 674761487964454092208459)
            ·
              refine ⟨1012142231946681138312689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 674761487964454092208459 1012142231946681138312689)
              ·
                refine ⟨759106673960010853734517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1012142231946681138312689 759106673960010853734517)
                ·
                  refine ⟨71166250683751017537611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 759106673960010853734517 71166250683751017537611)
                  ·
                    rfl

theorem cell22_623681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 2, 1, 2, 5].length) (baseStart_623681 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_623681 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_623681 prefixEnd_623681 := by exact prefixLift 623681
  have htrace : WordTrace (prefixWord ++ tailWord_623681) baseStart_623681 baseEnd_623681 := by
    simpa [prefixWord, tailWord_623681, baseEnd_623681] using wordTrace_append hprefix tailTrace_623681
  have hstable : (prefixWord ++ tailWord_623681).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_623681).length < 2 ^ (prefixWord ++ tailWord_623681).sum := by decide
  have hdescent : baseEnd_623681 < baseStart_623681 := by decide
  rcases family_descends (prefixWord ++ tailWord_623681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_623726 : List Nat := [4, 1, 2, 2, 1, 2, 3, 3, 4]
def baseStart_623726 : Nat := 118140960795 + 623726 * 2 ^ 59
def prefixEnd_623726 : Nat := 4983230072969 + 3 ^ 40 * 623726 * 2
def baseEnd_623726 : Nat := 71171385490295978412565

theorem tailTrace_623726 : CollatzResearch.WordTrace tailWord_623726 prefixEnd_623726 71171385490295978412565 := by
  unfold tailWord_623726
  simp only [CollatzResearch.WordTrace]
  refine ⟨2843644517294337595638379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15166104092236467176738021 2843644517294337595638379)
  ·
    refine ⟨4265466775941506393457569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2843644517294337595638379 4265466775941506393457569)
    ·
      refine ⟨3199100081956129795093177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4265466775941506393457569 3199100081956129795093177)
      ·
        refine ⟨2399325061467097346319883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3199100081956129795093177 2399325061467097346319883)
        ·
          refine ⟨3598987592200646019479825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2399325061467097346319883 3598987592200646019479825)
          ·
            refine ⟨2699240694150484514609869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3598987592200646019479825 2699240694150484514609869)
            ·
              refine ⟨1012215260306431692978701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2699240694150484514609869 1012215260306431692978701)
              ·
                refine ⟨379580722614911884867013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1012215260306431692978701 379580722614911884867013)
                ·
                  refine ⟨71171385490295978412565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 379580722614911884867013 71171385490295978412565)
                  ·
                    rfl

theorem cell22_623726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 3, 3, 4].length) (baseStart_623726 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_623726 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_623726 prefixEnd_623726 := by exact prefixLift 623726
  have htrace : WordTrace (prefixWord ++ tailWord_623726) baseStart_623726 baseEnd_623726 := by
    simpa [prefixWord, tailWord_623726, baseEnd_623726] using wordTrace_append hprefix tailTrace_623726
  have hstable : (prefixWord ++ tailWord_623726).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_623726).length < 2 ^ (prefixWord ++ tailWord_623726).sum := by decide
  have hdescent : baseEnd_623726 < baseStart_623726 := by decide
  rcases family_descends (prefixWord ++ tailWord_623726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_623758 : List Nat := [4, 1, 1, 3, 2, 1, 4, 1, 2, 3]
def baseStart_623758 : Nat := 118140960795 + 623758 * 2 ^ 59
def prefixEnd_623758 : Nat := 4983230072969 + 3 ^ 40 * 623758 * 2
def baseEnd_623758 : Nat := 213525110724850518437597

theorem tailTrace_623758 : CollatzResearch.WordTrace tailWord_623758 prefixEnd_623758 213525110724850518437597 := by
  unfold tailWord_623758
  simp only [CollatzResearch.WordTrace]
  refine ⟨2843790409279846278783991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15166882182825846820181285 2843790409279846278783991)
  ·
    refine ⟨4265685613919769418175987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2843790409279846278783991 4265685613919769418175987)
    ·
      refine ⟨6398528420879654127263981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4265685613919769418175987 6398528420879654127263981)
      ·
        refine ⟨2399448157829870297723993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6398528420879654127263981 2399448157829870297723993)
        ·
          refine ⟨1799586118372402723292995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2399448157829870297723993 1799586118372402723292995)
          ·
            refine ⟨2699379177558604084939493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1799586118372402723292995 2699379177558604084939493)
            ·
              refine ⟨506133595792238265926155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2699379177558604084939493 506133595792238265926155)
              ·
                refine ⟨759200393688357398889233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 506133595792238265926155 759200393688357398889233)
                ·
                  refine ⟨569400295266268049166925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 759200393688357398889233 569400295266268049166925)
                  ·
                    refine ⟨213525110724850518437597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 569400295266268049166925 213525110724850518437597)
                    ·
                      rfl

theorem cell22_623758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 4, 1, 2, 3].length) (baseStart_623758 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_623758 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_623758 prefixEnd_623758 := by exact prefixLift 623758
  have htrace : WordTrace (prefixWord ++ tailWord_623758) baseStart_623758 baseEnd_623758 := by
    simpa [prefixWord, tailWord_623758, baseEnd_623758] using wordTrace_append hprefix tailTrace_623758
  have hstable : (prefixWord ++ tailWord_623758).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_623758).length < 2 ^ (prefixWord ++ tailWord_623758).sum := by decide
  have hdescent : baseEnd_623758 < baseStart_623758 := by decide
  rcases family_descends (prefixWord ++ tailWord_623758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_623799 : List Nat := [1, 1, 3, 1, 4, 1, 4, 2, 5]
def baseStart_623799 : Nat := 118140960795 + 623799 * 2 ^ 59
def prefixEnd_623799 : Nat := 4983230072969 + 3 ^ 40 * 623799 * 2
def baseEnd_623799 : Nat := 71179715287580026054157

theorem tailTrace_623799 : CollatzResearch.WordTrace tailWord_623799 prefixEnd_623799 71179715287580026054157 := by
  unfold tailWord_623799
  simp only [CollatzResearch.WordTrace]
  refine ⟨22751818667090234232514451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15167879111393489488342967 22751818667090234232514451)
  ·
    refine ⟨34127728000635351348771677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22751818667090234232514451 34127728000635351348771677)
    ·
      refine ⟨12797898000238256755789379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34127728000635351348771677 12797898000238256755789379)
      ·
        refine ⟨19196847000357385133684069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12797898000238256755789379 19196847000357385133684069)
        ·
          refine ⟨3599408812567009712565763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19196847000357385133684069 3599408812567009712565763)
          ·
            refine ⟨5399113218850514568848645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3599408812567009712565763 5399113218850514568848645)
            ·
              refine ⟨1012333728534471481659121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5399113218850514568848645 1012333728534471481659121)
              ·
                refine ⟨759250296400853611244341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1012333728534471481659121 759250296400853611244341)
                ·
                  refine ⟨71179715287580026054157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 759250296400853611244341 71179715287580026054157)
                  ·
                    rfl

theorem cell22_623799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 4, 2, 5].length) (baseStart_623799 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_623799 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_623799 prefixEnd_623799 := by exact prefixLift 623799
  have htrace : WordTrace (prefixWord ++ tailWord_623799) baseStart_623799 baseEnd_623799 := by
    simpa [prefixWord, tailWord_623799, baseEnd_623799] using wordTrace_append hprefix tailTrace_623799
  have hstable : (prefixWord ++ tailWord_623799).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_623799).length < 2 ^ (prefixWord ++ tailWord_623799).sum := by decide
  have hdescent : baseEnd_623799 < baseStart_623799 := by decide
  rcases family_descends (prefixWord ++ tailWord_623799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_623827 : List Nat := [1, 1, 1, 2, 1, 1, 1, 8, 6]
def baseStart_623827 : Nat := 118140960795 + 623827 * 2 ^ 59
def prefixEnd_623827 : Nat := 4983230072969 + 3 ^ 40 * 623827 * 2
def baseEnd_623827 : Nat := 71182910278319112820795

theorem tailTrace_623827 : CollatzResearch.WordTrace tailWord_623827 prefixEnd_623827 71182910278319112820795 := by
  unfold tailWord_623827
  simp only [CollatzResearch.WordTrace]
  refine ⟨22752839910988795014533735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15168559940659196676355823 22752839910988795014533735)
  ·
    refine ⟨34129259866483192521800603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22752839910988795014533735 34129259866483192521800603)
    ·
      refine ⟨51193889799724788782700905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34129259866483192521800603 51193889799724788782700905)
      ·
        refine ⟨38395417349793591587025679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51193889799724788782700905 38395417349793591587025679)
        ·
          refine ⟨57593126024690387380538519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38395417349793591587025679 57593126024690387380538519)
          ·
            refine ⟨86389689037035581070807779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57593126024690387380538519 86389689037035581070807779)
            ·
              refine ⟨129584533555553371606211669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 86389689037035581070807779 129584533555553371606211669)
              ·
                refine ⟨1518568752604141073510293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 129584533555553371606211669 1518568752604141073510293)
                ·
                  refine ⟨71182910278319112820795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1518568752604141073510293 71182910278319112820795)
                  ·
                    rfl

theorem cell22_623827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 8, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 8, 6].length) (baseStart_623827 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_623827 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_623827 prefixEnd_623827 := by exact prefixLift 623827
  have htrace : WordTrace (prefixWord ++ tailWord_623827) baseStart_623827 baseEnd_623827 := by
    simpa [prefixWord, tailWord_623827, baseEnd_623827] using wordTrace_append hprefix tailTrace_623827
  have hstable : (prefixWord ++ tailWord_623827).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_623827).length < 2 ^ (prefixWord ++ tailWord_623827).sum := by decide
  have hdescent : baseEnd_623827 < baseStart_623827 := by decide
  rcases family_descends (prefixWord ++ tailWord_623827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_623872 : List Nat := [2, 1, 1, 2, 1, 1, 3, 11]
def baseStart_623872 : Nat := 118140960795 + 623872 * 2 ^ 59
def prefixEnd_623872 : Nat := 4983230072969 + 3 ^ 40 * 623872 * 2
def baseEnd_623872 : Nat := 23729348361621357898583

theorem tailTrace_623872 : CollatzResearch.WordTrace tailWord_623872 prefixEnd_623872 23729348361621357898583 := by
  unfold tailWord_623872
  simp only [CollatzResearch.WordTrace]
  refine ⟨11377240597912883849960935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15169654130550511799947913 11377240597912883849960935)
  ·
    refine ⟨17065860896869325774941403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11377240597912883849960935 17065860896869325774941403)
    ·
      refine ⟨25598791345303988662412105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17065860896869325774941403 25598791345303988662412105)
      ·
        refine ⟨19199093508977991496809079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25598791345303988662412105 19199093508977991496809079)
        ·
          refine ⟨28798640263466987245213619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19199093508977991496809079 28798640263466987245213619)
          ·
            refine ⟨43197960395200480867820429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28798640263466987245213619 43197960395200480867820429)
            ·
              refine ⟨16199235148200180325432661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43197960395200480867820429 16199235148200180325432661)
              ·
                refine ⟨23729348361621357898583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 16199235148200180325432661 23729348361621357898583)
                ·
                  rfl

theorem cell22_623872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 11].length) (baseStart_623872 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_623872 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_623872 prefixEnd_623872 := by exact prefixLift 623872
  have htrace : WordTrace (prefixWord ++ tailWord_623872) baseStart_623872 baseEnd_623872 := by
    simpa [prefixWord, tailWord_623872, baseEnd_623872] using wordTrace_append hprefix tailTrace_623872
  have hstable : (prefixWord ++ tailWord_623872).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_623872).length < 2 ^ (prefixWord ++ tailWord_623872).sum := by decide
  have hdescent : baseEnd_623872 < baseStart_623872 := by decide
  rcases family_descends (prefixWord ++ tailWord_623872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_623876 : List Nat := [2, 3, 2, 2, 2, 1, 3, 1, 1, 5]
def baseStart_623876 : Nat := 118140960795 + 623876 * 2 ^ 59
def prefixEnd_623876 : Nat := 4983230072969 + 3 ^ 40 * 623876 * 2
def baseEnd_623876 : Nat := 213565504536337543987235

theorem tailTrace_623876 : CollatzResearch.WordTrace tailWord_623876 prefixEnd_623876 213565504536337543987235 := by
  unfold tailWord_623876
  simp only [CollatzResearch.WordTrace]
  refine ⟨11377313543905638191533741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15169751391874184255378321 11377313543905638191533741)
  ·
    refine ⟨4266492578964614321825153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11377313543905638191533741 4266492578964614321825153)
    ·
      refine ⟨3199869434223460741368865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4266492578964614321825153 3199869434223460741368865)
      ·
        refine ⟨2399902075667595556026649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3199869434223460741368865 2399902075667595556026649)
        ·
          refine ⟨1799926556750696667019987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2399902075667595556026649 1799926556750696667019987)
          ·
            refine ⟨2699889835126045000529981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1799926556750696667019987 2699889835126045000529981)
            ·
              refine ⟨1012458688172266875198743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2699889835126045000529981 1012458688172266875198743)
              ·
                refine ⟨1518688032258400312798115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1012458688172266875198743 1518688032258400312798115)
                ·
                  refine ⟨2278032048387600469197173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1518688032258400312798115 2278032048387600469197173)
                  ·
                    refine ⟨213565504536337543987235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2278032048387600469197173 213565504536337543987235)
                    ·
                      rfl

theorem cell22_623876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 3, 1, 1, 5].length) (baseStart_623876 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_623876 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_623876 prefixEnd_623876 := by exact prefixLift 623876
  have htrace : WordTrace (prefixWord ++ tailWord_623876) baseStart_623876 baseEnd_623876 := by
    simpa [prefixWord, tailWord_623876, baseEnd_623876] using wordTrace_append hprefix tailTrace_623876
  have hstable : (prefixWord ++ tailWord_623876).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_623876).length < 2 ^ (prefixWord ++ tailWord_623876).sum := by decide
  have hdescent : baseEnd_623876 < baseStart_623876 := by decide
  rcases family_descends (prefixWord ++ tailWord_623876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_623906 : List Nat := [3, 3, 1, 1, 4, 2, 8]
def baseStart_623906 : Nat := 118140960795 + 623906 * 2 ^ 59
def prefixEnd_623906 : Nat := 4983230072969 + 3 ^ 40 * 623906 * 2
def baseEnd_623906 : Nat := 7910213857386202434709

theorem tailTrace_623906 : CollatzResearch.WordTrace tailWord_623906 prefixEnd_623906 7910213857386202434709 := by
  unfold tailWord_623906
  simp only [CollatzResearch.WordTrace]
  refine ⟨5688930319425647876664893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15170480851801727671106381 5688930319425647876664893)
  ·
    refine ⟨2133348869784617953749335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5688930319425647876664893 2133348869784617953749335)
    ·
      refine ⟨3200023304676926930624003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2133348869784617953749335 3200023304676926930624003)
      ·
        refine ⟨4800034957015390395936005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3200023304676926930624003 4800034957015390395936005)
        ·
          refine ⟨900006554440385699238001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4800034957015390395936005 900006554440385699238001)
          ·
            refine ⟨675004915830289274428501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 900006554440385699238001 675004915830289274428501)
            ·
              refine ⟨7910213857386202434709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 675004915830289274428501 7910213857386202434709)
              ·
                rfl

theorem cell22_623906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 2, 8].length) (baseStart_623906 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_623906 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_623906 prefixEnd_623906 := by exact prefixLift 623906
  have htrace : WordTrace (prefixWord ++ tailWord_623906) baseStart_623906 baseEnd_623906 := by
    simpa [prefixWord, tailWord_623906, baseEnd_623906] using wordTrace_append hprefix tailTrace_623906
  have hstable : (prefixWord ++ tailWord_623906).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_623906).length < 2 ^ (prefixWord ++ tailWord_623906).sum := by decide
  have hdescent : baseEnd_623906 < baseStart_623906 := by decide
  rcases family_descends (prefixWord ++ tailWord_623906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_623942 : List Nat := [6, 1, 1, 3, 1, 1, 2, 1, 2, 4]
def baseStart_623942 : Nat := 118140960795 + 623942 * 2 ^ 59
def prefixEnd_623942 : Nat := 4983230072969 + 3 ^ 40 * 623942 * 2
def baseEnd_623942 : Nat := 213588097685135371837033

theorem tailTrace_623942 : CollatzResearch.WordTrace tailWord_623942 prefixEnd_623942 213588097685135371837033 := by
  unfold tailWord_623942
  simp only [CollatzResearch.WordTrace]
  refine ⟨711157322049130301717815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 15171356203714779769980053 711157322049130301717815)
  ·
    refine ⟨1066735983073695452576723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 711157322049130301717815 1066735983073695452576723)
    ·
      refine ⟨1600103974610543178865085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1066735983073695452576723 1600103974610543178865085)
      ·
        refine ⟨600038990478953692074407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1600103974610543178865085 600038990478953692074407)
        ·
          refine ⟨900058485718430538111611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 600038990478953692074407 900058485718430538111611)
          ·
            refine ⟨1350087728577645807167417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 900058485718430538111611 1350087728577645807167417)
            ·
              refine ⟨1012565796433234355375563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1350087728577645807167417 1012565796433234355375563)
              ·
                refine ⟨1518848694649851533063345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1012565796433234355375563 1518848694649851533063345)
                ·
                  refine ⟨1139136520987388649797509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1518848694649851533063345 1139136520987388649797509)
                  ·
                    refine ⟨213588097685135371837033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1139136520987388649797509 213588097685135371837033)
                    ·
                      rfl

theorem cell22_623942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 2, 1, 2, 4].length) (baseStart_623942 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_623942 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_623942 prefixEnd_623942 := by exact prefixLift 623942
  have htrace : WordTrace (prefixWord ++ tailWord_623942) baseStart_623942 baseEnd_623942 := by
    simpa [prefixWord, tailWord_623942, baseEnd_623942] using wordTrace_append hprefix tailTrace_623942
  have hstable : (prefixWord ++ tailWord_623942).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_623942).length < 2 ^ (prefixWord ++ tailWord_623942).sum := by decide
  have hdescent : baseEnd_623942 < baseStart_623942 := by decide
  rcases family_descends (prefixWord ++ tailWord_623942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_623972 : List Nat := [2, 3, 1, 1, 3, 4, 2, 2, 1, 3]
def baseStart_623972 : Nat := 118140960795 + 623972 * 2 ^ 59
def prefixEnd_623972 : Nat := 4983230072969 + 3 ^ 40 * 623972 * 2
def baseEnd_623972 : Nat := 213598367298225293586941

theorem tailTrace_623972 : CollatzResearch.WordTrace tailWord_623972 prefixEnd_623972 213598367298225293586941 := by
  unfold tailWord_623972
  simp only [CollatzResearch.WordTrace]
  refine ⟨11379064247731742389281085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15172085663642323185708113 11379064247731742389281085)
  ·
    refine ⟨4267149092899403395980407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11379064247731742389281085 4267149092899403395980407)
    ·
      refine ⟨6400723639349105093970611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4267149092899403395980407 6400723639349105093970611)
      ·
        refine ⟨9601085459023657640955917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6400723639349105093970611 9601085459023657640955917)
        ·
          refine ⟨3600407047133871615358469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9601085459023657640955917 3600407047133871615358469)
          ·
            refine ⟨675076321337600927879713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3600407047133871615358469 675076321337600927879713)
            ·
              refine ⟨506307241003200695909785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 675076321337600927879713 506307241003200695909785)
              ·
                refine ⟨379730430752400521932339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 506307241003200695909785 379730430752400521932339)
                ·
                  refine ⟨569595646128600782898509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 379730430752400521932339 569595646128600782898509)
                  ·
                    refine ⟨213598367298225293586941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 569595646128600782898509 213598367298225293586941)
                    ·
                      rfl

theorem cell22_623972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 4, 2, 2, 1, 3].length) (baseStart_623972 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_623972 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_623972 prefixEnd_623972 := by exact prefixLift 623972
  have htrace : WordTrace (prefixWord ++ tailWord_623972) baseStart_623972 baseEnd_623972 := by
    simpa [prefixWord, tailWord_623972, baseEnd_623972] using wordTrace_append hprefix tailTrace_623972
  have hstable : (prefixWord ++ tailWord_623972).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_623972).length < 2 ^ (prefixWord ++ tailWord_623972).sum := by decide
  have hdescent : baseEnd_623972 < baseStart_623972 := by decide
  rcases family_descends (prefixWord ++ tailWord_623972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_623981 : List Nat := [1, 5, 1, 1, 1, 3, 1, 2, 3, 4]
def baseStart_623981 : Nat := 118140960795 + 623981 * 2 ^ 59
def prefixEnd_623981 : Nat := 4983230072969 + 3 ^ 40 * 623981 * 2
def baseEnd_623981 : Nat := 213601448182152270111913

theorem tailTrace_623981 : CollatzResearch.WordTrace tailWord_623981 prefixEnd_623981 213601448182152270111913 := by
  unfold tailWord_623981
  simp only [CollatzResearch.WordTrace]
  refine ⟨22758456752430879315639797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15172304501620586210426531 22758456752430879315639797)
  ·
    refine ⟨2133605320540394935841231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 22758456752430879315639797 2133605320540394935841231)
    ·
      refine ⟨3200407980810592403761847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2133605320540394935841231 3200407980810592403761847)
      ·
        refine ⟨4800611971215888605642771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3200407980810592403761847 4800611971215888605642771)
        ·
          refine ⟨7200917956823832908464157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4800611971215888605642771 7200917956823832908464157)
          ·
            refine ⟨2700344233808937340674059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7200917956823832908464157 2700344233808937340674059)
            ·
              refine ⟨4050516350713406011011089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2700344233808937340674059 4050516350713406011011089)
              ·
                refine ⟨3037887263035054508258317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4050516350713406011011089 3037887263035054508258317)
                ·
                  refine ⟨1139207723638145440596869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3037887263035054508258317 1139207723638145440596869)
                  ·
                    refine ⟨213601448182152270111913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1139207723638145440596869 213601448182152270111913)
                    ·
                      rfl

theorem cell22_623981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 1, 2, 3, 4].length) (baseStart_623981 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_623981 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_623981 prefixEnd_623981 := by exact prefixLift 623981
  have htrace : WordTrace (prefixWord ++ tailWord_623981) baseStart_623981 baseEnd_623981 := by
    simpa [prefixWord, tailWord_623981, baseEnd_623981] using wordTrace_append hprefix tailTrace_623981
  have hstable : (prefixWord ++ tailWord_623981).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_623981).length < 2 ^ (prefixWord ++ tailWord_623981).sum := by decide
  have hdescent : baseEnd_623981 < baseStart_623981 := by decide
  rcases family_descends (prefixWord ++ tailWord_623981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_623994 : List Nat := [3, 1, 1, 1, 1, 1, 2, 2, 5, 5]
def baseStart_623994 : Nat := 118140960795 + 623994 * 2 ^ 59
def prefixEnd_623994 : Nat := 4983230072969 + 3 ^ 40 * 623994 * 2
def baseEnd_623994 : Nat := 213605898347824569536873

theorem tailTrace_623994 : CollatzResearch.WordTrace tailWord_623994 prefixEnd_623994 213605898347824569536873 := by
  unfold tailWord_623994
  simp only [CollatzResearch.WordTrace]
  refine ⟨5689732725345945633965759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15172620600922521690575357 5689732725345945633965759)
  ·
    refine ⟨8534599088018918450948639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5689732725345945633965759 8534599088018918450948639)
    ·
      refine ⟨12801898632028377676422959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8534599088018918450948639 12801898632028377676422959)
      ·
        refine ⟨19202847948042566514634439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12801898632028377676422959 19202847948042566514634439)
        ·
          refine ⟨28804271922063849771951659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19202847948042566514634439 28804271922063849771951659)
          ·
            refine ⟨43206407883095774657927489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28804271922063849771951659 43206407883095774657927489)
            ·
              refine ⟨32404805912321830993445617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43206407883095774657927489 32404805912321830993445617)
              ·
                refine ⟨24303604434241373245084213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32404805912321830993445617 24303604434241373245084213)
                ·
                  refine ⟨2278462915710128741726645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 24303604434241373245084213 2278462915710128741726645)
                  ·
                    refine ⟨213605898347824569536873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2278462915710128741726645 213605898347824569536873)
                    ·
                      rfl

theorem cell22_623994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 2, 5, 5].length) (baseStart_623994 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_623994 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_623994 prefixEnd_623994 := by exact prefixLift 623994
  have htrace : WordTrace (prefixWord ++ tailWord_623994) baseStart_623994 baseEnd_623994 := by
    simpa [prefixWord, tailWord_623994, baseEnd_623994] using wordTrace_append hprefix tailTrace_623994
  have hstable : (prefixWord ++ tailWord_623994).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_623994).length < 2 ^ (prefixWord ++ tailWord_623994).sum := by decide
  have hdescent : baseEnd_623994 < baseStart_623994 := by decide
  rcases family_descends (prefixWord ++ tailWord_623994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_624011 : List Nat := [1, 1, 1, 1, 4, 3, 2, 2, 4, 3]
def baseStart_624011 : Nat := 118140960795 + 624011 * 2 ^ 59
def prefixEnd_624011 : Nat := 4983230072969 + 3 ^ 40 * 624011 * 2
def baseEnd_624011 : Nat := 213611717795242191861821

theorem tailTrace_624011 : CollatzResearch.WordTrace tailWord_624011 prefixEnd_624011 213611717795242191861821 := by
  unfold tailWord_624011
  simp only [CollatzResearch.WordTrace]
  refine ⟨22759550942322194439231887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15173033961548129626154591 22759550942322194439231887)
  ·
    refine ⟨34139326413483291658847831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22759550942322194439231887 34139326413483291658847831)
    ·
      refine ⟨51208989620224937488271747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34139326413483291658847831 51208989620224937488271747)
      ·
        refine ⟨76813484430337406232407621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51208989620224937488271747 76813484430337406232407621)
        ·
          refine ⟨14402528330688263668576429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 76813484430337406232407621 14402528330688263668576429)
          ·
            refine ⟨5400948124008098875716161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14402528330688263668576429 5400948124008098875716161)
            ·
              refine ⟨4050711093006074156787121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5400948124008098875716161 4050711093006074156787121)
              ·
                refine ⟨3038033319754555617590341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4050711093006074156787121 3038033319754555617590341)
                ·
                  refine ⟨569631247453979178298189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3038033319754555617590341 569631247453979178298189)
                  ·
                    refine ⟨213611717795242191861821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 569631247453979178298189 213611717795242191861821)
                    ·
                      rfl

theorem cell22_624011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 2, 2, 4, 3].length) (baseStart_624011 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_624011 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_624011 prefixEnd_624011 := by exact prefixLift 624011
  have htrace : WordTrace (prefixWord ++ tailWord_624011) baseStart_624011 baseEnd_624011 := by
    simpa [prefixWord, tailWord_624011, baseEnd_624011] using wordTrace_append hprefix tailTrace_624011
  have hstable : (prefixWord ++ tailWord_624011).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_624011).length < 2 ^ (prefixWord ++ tailWord_624011).sum := by decide
  have hdescent : baseEnd_624011 < baseStart_624011 := by decide
  rcases family_descends (prefixWord ++ tailWord_624011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_624026 : List Nat := [3, 1, 1, 4, 1, 1, 2, 1, 4, 4]
def baseStart_624026 : Nat := 118140960795 + 624026 * 2 ^ 59
def prefixEnd_624026 : Nat := 4983230072969 + 3 ^ 40 * 624026 * 2
def baseEnd_624026 : Nat := 213616852601787152736775

theorem tailTrace_624026 : CollatzResearch.WordTrace tailWord_624026 prefixEnd_624026 213616852601787152736775 := by
  unfold tailWord_624026
  simp only [CollatzResearch.WordTrace]
  refine ⟨5690024509316963000256983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15173398691511901334018621 5690024509316963000256983)
  ·
    refine ⟨8535036763975444500385475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5690024509316963000256983 8535036763975444500385475)
    ·
      refine ⟨12802555145963166750578213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8535036763975444500385475 12802555145963166750578213)
      ·
        refine ⟨2400479089868093765733415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12802555145963166750578213 2400479089868093765733415)
        ·
          refine ⟨3600718634802140648600123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2400479089868093765733415 3600718634802140648600123)
          ·
            refine ⟨5401077952203210972900185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3600718634802140648600123 5401077952203210972900185)
            ·
              refine ⟨4050808464152408229675139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5401077952203210972900185 4050808464152408229675139)
              ·
                refine ⟨6076212696228612344512709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4050808464152408229675139 6076212696228612344512709)
                ·
                  refine ⟨1139289880542864814596133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6076212696228612344512709 1139289880542864814596133)
                  ·
                    refine ⟨213616852601787152736775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1139289880542864814596133 213616852601787152736775)
                    ·
                      rfl

theorem cell22_624026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 2, 1, 4, 4].length) (baseStart_624026 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_624026 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_624026 prefixEnd_624026 := by exact prefixLift 624026
  have htrace : WordTrace (prefixWord ++ tailWord_624026) baseStart_624026 baseEnd_624026 := by
    simpa [prefixWord, tailWord_624026, baseEnd_624026] using wordTrace_append hprefix tailTrace_624026
  have hstable : (prefixWord ++ tailWord_624026).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_624026).length < 2 ^ (prefixWord ++ tailWord_624026).sum := by decide
  have hdescent : baseEnd_624026 < baseStart_624026 := by decide
  rcases family_descends (prefixWord ++ tailWord_624026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_624030 : List Nat := [4, 3, 1, 2, 2, 1, 2, 1, 6]
def baseStart_624030 : Nat := 118140960795 + 624030 * 2 ^ 59
def prefixEnd_624030 : Nat := 4983230072969 + 3 ^ 40 * 624030 * 2
def baseEnd_624030 : Nat := 71206073961177491878921

theorem tailTrace_624030 : CollatzResearch.WordTrace tailWord_624030 prefixEnd_624030 71206073961177491878921 := by
  unfold tailWord_624030
  simp only [CollatzResearch.WordTrace]
  refine ⟨2845030491156670085521693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15173495952835573789449029 2845030491156670085521693)
  ·
    refine ⟨1066886434183751282070635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2845030491156670085521693 1066886434183751282070635)
    ·
      refine ⟨1600329651275626923105953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1066886434183751282070635 1600329651275626923105953)
      ·
        refine ⟨1200247238456720192329465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1600329651275626923105953 1200247238456720192329465)
        ·
          refine ⟨900185428842540144247099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1200247238456720192329465 900185428842540144247099)
          ·
            refine ⟨1350278143263810216370649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 900185428842540144247099 1350278143263810216370649)
            ·
              refine ⟨1012708607447857662277987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1350278143263810216370649 1012708607447857662277987)
              ·
                refine ⟨1519062911171786493416981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1012708607447857662277987 1519062911171786493416981)
                ·
                  refine ⟨71206073961177491878921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1519062911171786493416981 71206073961177491878921)
                  ·
                    rfl

theorem cell22_624030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 2, 1, 6].length) (baseStart_624030 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_624030 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_624030 prefixEnd_624030 := by exact prefixLift 624030
  have htrace : WordTrace (prefixWord ++ tailWord_624030) baseStart_624030 baseEnd_624030 := by
    simpa [prefixWord, tailWord_624030, baseEnd_624030] using wordTrace_append hprefix tailTrace_624030
  have hstable : (prefixWord ++ tailWord_624030).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_624030).length < 2 ^ (prefixWord ++ tailWord_624030).sum := by decide
  have hdescent : baseEnd_624030 < baseStart_624030 := by decide
  rcases family_descends (prefixWord ++ tailWord_624030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_624045 : List Nat := [1, 5, 2, 2, 1, 3, 1, 1, 1, 5]
def baseStart_624045 : Nat := 118140960795 + 624045 * 2 ^ 59
def prefixEnd_624045 : Nat := 4983230072969 + 3 ^ 40 * 624045 * 2
def baseEnd_624045 : Nat := 213623356690077436511717

theorem tailTrace_624045 : CollatzResearch.WordTrace tailWord_624045 prefixEnd_624045 213623356690077436511717 := by
  unfold tailWord_624045
  simp only [CollatzResearch.WordTrace]
  refine ⟨22760791024199018245969589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15173860682799345497313059 22760791024199018245969589)
  ·
    refine ⟨2133824158518657960559649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 22760791024199018245969589 2133824158518657960559649)
    ·
      refine ⟨1600368118888993470419737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2133824158518657960559649 1600368118888993470419737)
      ·
        refine ⟨1200276089166745102814803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1600368118888993470419737 1200276089166745102814803)
        ·
          refine ⟨1800414133750117654222205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1200276089166745102814803 1800414133750117654222205)
          ·
            refine ⟨675155300156294120333327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1800414133750117654222205 675155300156294120333327)
            ·
              refine ⟨1012732950234441180499991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 675155300156294120333327 1012732950234441180499991)
              ·
                refine ⟨1519099425351661770749987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1012732950234441180499991 1519099425351661770749987)
                ·
                  refine ⟨2278649138027492656124981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1519099425351661770749987 2278649138027492656124981)
                  ·
                    refine ⟨213623356690077436511717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2278649138027492656124981 213623356690077436511717)
                    ·
                      rfl

theorem cell22_624045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 3, 1, 1, 1, 5].length) (baseStart_624045 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_624045 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_624045 prefixEnd_624045 := by exact prefixLift 624045
  have htrace : WordTrace (prefixWord ++ tailWord_624045) baseStart_624045 baseEnd_624045 := by
    simpa [prefixWord, tailWord_624045, baseEnd_624045] using wordTrace_append hprefix tailTrace_624045
  have hstable : (prefixWord ++ tailWord_624045).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_624045).length < 2 ^ (prefixWord ++ tailWord_624045).sum := by decide
  have hdescent : baseEnd_624045 < baseStart_624045 := by decide
  rcases family_descends (prefixWord ++ tailWord_624045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_624090 : List Nat := [3, 1, 1, 2, 3, 4, 1, 1, 3, 3]
def baseStart_624090 : Nat := 118140960795 + 624090 * 2 ^ 59
def prefixEnd_624090 : Nat := 4983230072969 + 3 ^ 40 * 624090 * 2
def baseEnd_624090 : Nat := 213638761109712319136579

theorem tailTrace_624090 : CollatzResearch.WordTrace tailWord_624090 prefixEnd_624090 213638761109712319136579 := by
  unfold tailWord_624090
  simp only [CollatzResearch.WordTrace]
  refine ⟨5690608077258997732839431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15174954872690660620905149 5690608077258997732839431)
  ·
    refine ⟨8535912115888496599259147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5690608077258997732839431 8535912115888496599259147)
    ·
      refine ⟨12803868173832744898888721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8535912115888496599259147 12803868173832744898888721)
      ·
        refine ⟨9602901130374558674166541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12803868173832744898888721 9602901130374558674166541)
        ·
          refine ⟨3601087923890459502812453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9602901130374558674166541 3601087923890459502812453)
          ·
            refine ⟨675203985729461156777335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3601087923890459502812453 675203985729461156777335)
            ·
              refine ⟨1012805978594191735166003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 675203985729461156777335 1012805978594191735166003)
              ·
                refine ⟨1519208967891287602749005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1012805978594191735166003 1519208967891287602749005)
                ·
                  refine ⟨569703362959232851030877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1519208967891287602749005 569703362959232851030877)
                  ·
                    refine ⟨213638761109712319136579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 569703362959232851030877 213638761109712319136579)
                    ·
                      rfl

theorem cell22_624090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 4, 1, 1, 3, 3].length) (baseStart_624090 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_624090 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_624090 prefixEnd_624090 := by exact prefixLift 624090
  have htrace : WordTrace (prefixWord ++ tailWord_624090) baseStart_624090 baseEnd_624090 := by
    simpa [prefixWord, tailWord_624090, baseEnd_624090] using wordTrace_append hprefix tailTrace_624090
  have hstable : (prefixWord ++ tailWord_624090).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_624090).length < 2 ^ (prefixWord ++ tailWord_624090).sum := by decide
  have hdescent : baseEnd_624090 < baseStart_624090 := by decide
  rcases family_descends (prefixWord ++ tailWord_624090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_624103 : List Nat := [1, 1, 5, 2, 1, 3, 1, 3, 5]
def baseStart_624103 : Nat := 118140960795 + 624103 * 2 ^ 59
def prefixEnd_624103 : Nat := 4983230072969 + 3 ^ 40 * 624103 * 2
def baseEnd_624103 : Nat := 71214403758461539520513

theorem tailTrace_624103 : CollatzResearch.WordTrace tailWord_624103 prefixEnd_624103 71214403758461539520513 := by
  unfold tailWord_624103
  simp only [CollatzResearch.WordTrace]
  refine ⟨22762906457988894151580963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15175270971992596101053975 22762906457988894151580963)
  ·
    refine ⟨34144359686983341227371445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22762906457988894151580963 34144359686983341227371445)
    ·
      refine ⟨3201033720654688240066073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 34144359686983341227371445 3201033720654688240066073)
      ·
        refine ⟨2400775290491016180049555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3201033720654688240066073 2400775290491016180049555)
        ·
          refine ⟨3601162935736524270074333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2400775290491016180049555 3601162935736524270074333)
          ·
            refine ⟨1350436100901196601277875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3601162935736524270074333 1350436100901196601277875)
            ·
              refine ⟨2025654151351794901916813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1350436100901196601277875 2025654151351794901916813)
              ·
                refine ⟨759620306756923088218805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2025654151351794901916813 759620306756923088218805)
                ·
                  refine ⟨71214403758461539520513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 759620306756923088218805 71214403758461539520513)
                  ·
                    rfl

theorem cell22_624103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 1, 3, 5].length) (baseStart_624103 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_624103 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_624103 prefixEnd_624103 := by exact prefixLift 624103
  have htrace : WordTrace (prefixWord ++ tailWord_624103) baseStart_624103 baseEnd_624103 := by
    simpa [prefixWord, tailWord_624103, baseEnd_624103] using wordTrace_append hprefix tailTrace_624103
  have hstable : (prefixWord ++ tailWord_624103).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_624103).length < 2 ^ (prefixWord ++ tailWord_624103).sum := by decide
  have hdescent : baseEnd_624103 < baseStart_624103 := by decide
  rcases family_descends (prefixWord ++ tailWord_624103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_624141 : List Nat := [1, 7, 1, 1, 2, 1, 1, 4, 1, 3]
def baseStart_624141 : Nat := 118140960795 + 624141 * 2 ^ 59
def prefixEnd_624141 : Nat := 4983230072969 + 3 ^ 40 * 624141 * 2
def baseEnd_624141 : Nat := 213656219451965186111423

theorem tailTrace_624141 : CollatzResearch.WordTrace tailWord_624141 prefixEnd_624141 213656219451965186111423 := by
  unfold tailWord_624141
  simp only [CollatzResearch.WordTrace]
  refine ⟨22764292431851226641464277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15176194954567484427642851 22764292431851226641464277)
  ·
    refine ⟨533538103871513124409319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 22764292431851226641464277 533538103871513124409319)
    ·
      refine ⟨800307155807269686613979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 533538103871513124409319 800307155807269686613979)
      ·
        refine ⟨1200460733710904529920969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 800307155807269686613979 1200460733710904529920969)
        ·
          refine ⟨900345550283178397440727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1200460733710904529920969 900345550283178397440727)
          ·
            refine ⟨1350518325424767596161091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 900345550283178397440727 1350518325424767596161091)
            ·
              refine ⟨2025777488137151394241637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1350518325424767596161091 2025777488137151394241637)
              ·
                refine ⟨379833279025715886420307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2025777488137151394241637 379833279025715886420307)
                ·
                  refine ⟨569749918538573829630461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 379833279025715886420307 569749918538573829630461)
                  ·
                    refine ⟨213656219451965186111423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 569749918538573829630461 213656219451965186111423)
                    ·
                      rfl

theorem cell22_624141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 1, 4, 1, 3].length) (baseStart_624141 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_624141 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_624141 prefixEnd_624141 := by exact prefixLift 624141
  have htrace : WordTrace (prefixWord ++ tailWord_624141) baseStart_624141 baseEnd_624141 := by
    simpa [prefixWord, tailWord_624141, baseEnd_624141] using wordTrace_append hprefix tailTrace_624141
  have hstable : (prefixWord ++ tailWord_624141).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_624141).length < 2 ^ (prefixWord ++ tailWord_624141).sum := by decide
  have hdescent : baseEnd_624141 < baseStart_624141 := by decide
  rcases family_descends (prefixWord ++ tailWord_624141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_624268 : List Nat := [2, 2, 1, 2, 1, 1, 4, 2, 3, 4]
def baseStart_624268 : Nat := 118140960795 + 624268 * 2 ^ 59
def prefixEnd_624268 : Nat := 4983230072969 + 3 ^ 40 * 624268 * 2
def baseEnd_624268 : Nat := 213699694147379188186033

theorem tailTrace_624268 : CollatzResearch.WordTrace tailWord_624268 prefixEnd_624268 213699694147379188186033 := by
  unfold tailWord_624268
  simp only [CollatzResearch.WordTrace]
  refine ⟨11384462251195563665668729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15179283001594084887558305 11384462251195563665668729)
  ·
    refine ⟨8538346688396672749251547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11384462251195563665668729 8538346688396672749251547)
    ·
      refine ⟨12807520032595009123877321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8538346688396672749251547 12807520032595009123877321)
      ·
        refine ⟨9605640024446256842907991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12807520032595009123877321 9605640024446256842907991)
        ·
          refine ⟨14408460036669385264361987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9605640024446256842907991 14408460036669385264361987)
          ·
            refine ⟨21612690055004077896542981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14408460036669385264361987 21612690055004077896542981)
            ·
              refine ⟨4052379385313264605601809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21612690055004077896542981 4052379385313264605601809)
              ·
                refine ⟨3039284538984948454201357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4052379385313264605601809 3039284538984948454201357)
                ·
                  refine ⟨1139731702119355670325509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3039284538984948454201357 1139731702119355670325509)
                  ·
                    refine ⟨213699694147379188186033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1139731702119355670325509 213699694147379188186033)
                    ·
                      rfl

theorem cell22_624268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 4, 2, 3, 4].length) (baseStart_624268 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_624268 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_624268 prefixEnd_624268 := by exact prefixLift 624268
  have htrace : WordTrace (prefixWord ++ tailWord_624268) baseStart_624268 baseEnd_624268 := by
    simpa [prefixWord, tailWord_624268, baseEnd_624268] using wordTrace_append hprefix tailTrace_624268
  have hstable : (prefixWord ++ tailWord_624268).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_624268).length < 2 ^ (prefixWord ++ tailWord_624268).sum := by decide
  have hdescent : baseEnd_624268 < baseStart_624268 := by decide
  rcases family_descends (prefixWord ++ tailWord_624268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_624332 : List Nat := [2, 2, 1, 5, 2, 1, 2, 1, 1, 5]
def baseStart_624332 : Nat := 118140960795 + 624332 * 2 ^ 59
def prefixEnd_624332 : Nat := 4983230072969 + 3 ^ 40 * 624332 * 2
def baseEnd_624332 : Nat := 213721602655304354585837

theorem tailTrace_624332 : CollatzResearch.WordTrace tailWord_624332 prefixEnd_624332 213721602655304354585837 := by
  unfold tailWord_624332
  simp only [CollatzResearch.WordTrace]
  refine ⟨11385629387079633130833625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15180839182772844174444833 11385629387079633130833625)
  ·
    refine ⟨8539222040309724848125219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11385629387079633130833625 8539222040309724848125219)
    ·
      refine ⟨12808833060464587272187829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8539222040309724848125219 12808833060464587272187829)
      ·
        refine ⟨1200828099418555056767609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 12808833060464587272187829 1200828099418555056767609)
        ·
          refine ⟨900621074563916292575707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1200828099418555056767609 900621074563916292575707)
          ·
            refine ⟨1350931611845874438863561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 900621074563916292575707 1350931611845874438863561)
            ·
              refine ⟨1013198708884405829147671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1350931611845874438863561 1013198708884405829147671)
              ·
                refine ⟨1519798063326608743721507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1013198708884405829147671 1519798063326608743721507)
                ·
                  refine ⟨2279697094989913115582261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1519798063326608743721507 2279697094989913115582261)
                  ·
                    refine ⟨213721602655304354585837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2279697094989913115582261 213721602655304354585837)
                    ·
                      rfl

theorem cell22_624332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 2, 1, 1, 5].length) (baseStart_624332 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_624332 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_624332 prefixEnd_624332 := by exact prefixLift 624332
  have htrace : WordTrace (prefixWord ++ tailWord_624332) baseStart_624332 baseEnd_624332 := by
    simpa [prefixWord, tailWord_624332, baseEnd_624332] using wordTrace_append hprefix tailTrace_624332
  have hstable : (prefixWord ++ tailWord_624332).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_624332).length < 2 ^ (prefixWord ++ tailWord_624332).sum := by decide
  have hdescent : baseEnd_624332 < baseStart_624332 := by decide
  rcases family_descends (prefixWord ++ tailWord_624332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_624345 : List Nat := [1, 2, 1, 2, 3, 4, 3, 6]
def baseStart_624345 : Nat := 118140960795 + 624345 * 2 ^ 59
def prefixEnd_624345 : Nat := 4983230072969 + 3 ^ 40 * 624345 * 2
def baseEnd_624345 : Nat := 23747339202330739334533

theorem tailTrace_624345 : CollatzResearch.WordTrace tailWord_624345 prefixEnd_624345 23747339202330739334533 := by
  unfold tailWord_624345
  simp only [CollatzResearch.WordTrace]
  refine ⟨22771732923112169481890489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15181155282074779654593659 22771732923112169481890489)
  ·
    refine ⟨17078799692334127111417867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22771732923112169481890489 17078799692334127111417867)
    ·
      refine ⟨25618199538501190667126801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17078799692334127111417867 25618199538501190667126801)
      ·
        refine ⟨19213649653875893000345101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25618199538501190667126801 19213649653875893000345101)
        ·
          refine ⟨7205118620203459875129413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19213649653875893000345101 7205118620203459875129413)
          ·
            refine ⟨1350959741288148726586765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7205118620203459875129413 1350959741288148726586765)
            ·
              refine ⟨506609902983055772470037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1350959741288148726586765 506609902983055772470037)
              ·
                refine ⟨23747339202330739334533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 506609902983055772470037 23747339202330739334533)
                ·
                  rfl

theorem cell22_624345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 3, 6].length) (baseStart_624345 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_624345 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_624345 prefixEnd_624345 := by exact prefixLift 624345
  have htrace : WordTrace (prefixWord ++ tailWord_624345) baseStart_624345 baseEnd_624345 := by
    simpa [prefixWord, tailWord_624345, baseEnd_624345] using wordTrace_append hprefix tailTrace_624345
  have hstable : (prefixWord ++ tailWord_624345).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_624345).length < 2 ^ (prefixWord ++ tailWord_624345).sum := by decide
  have hdescent : baseEnd_624345 < baseStart_624345 := by decide
  rcases family_descends (prefixWord ++ tailWord_624345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_624441 : List Nat := [1, 2, 1, 7, 1, 2, 2, 1, 5]
def baseStart_624441 : Nat := 118140960795 + 624441 * 2 ^ 59
def prefixEnd_624441 : Nat := 4983230072969 + 3 ^ 40 * 624441 * 2
def baseEnd_624441 : Nat := 71252971860954801203501

theorem tailTrace_624441 : CollatzResearch.WordTrace tailWord_624441 prefixEnd_624441 71252971860954801203501 := by
  unfold tailWord_624441
  simp only [CollatzResearch.WordTrace]
  refine ⟨22775234330764377877385177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15183489553842918584923451 22775234330764377877385177)
  ·
    refine ⟨17081425748073283408038883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22775234330764377877385177 17081425748073283408038883)
    ·
      refine ⟨25622138622109925112058325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17081425748073283408038883 25622138622109925112058325)
      ·
        refine ⟨600518873955701369813867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 25622138622109925112058325 600518873955701369813867)
        ·
          refine ⟨900778310933552054720801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 600518873955701369813867 900778310933552054720801)
          ·
            refine ⟨675583733200164041040601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 900778310933552054720801 675583733200164041040601)
            ·
              refine ⟨506687799900123030780451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 675583733200164041040601 506687799900123030780451)
              ·
                refine ⟨760031699850184546170677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 506687799900123030780451 760031699850184546170677)
                ·
                  refine ⟨71252971860954801203501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 760031699850184546170677 71252971860954801203501)
                  ·
                    rfl

theorem cell22_624441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 2, 2, 1, 5].length) (baseStart_624441 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_624441 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_624441 prefixEnd_624441 := by exact prefixLift 624441
  have htrace : WordTrace (prefixWord ++ tailWord_624441) baseStart_624441 baseEnd_624441 := by
    simpa [prefixWord, tailWord_624441, baseEnd_624441] using wordTrace_append hprefix tailTrace_624441
  have hstable : (prefixWord ++ tailWord_624441).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_624441).length < 2 ^ (prefixWord ++ tailWord_624441).sum := by decide
  have hdescent : baseEnd_624441 < baseStart_624441 := by decide
  rcases family_descends (prefixWord ++ tailWord_624441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_624512 : List Nat := [2, 1, 1, 2, 1, 2, 5, 2, 3, 3]
def baseStart_624512 : Nat := 118140960795 + 624512 * 2 ^ 59
def prefixEnd_624512 : Nat := 4983230072969 + 3 ^ 40 * 624512 * 2
def baseEnd_624512 : Nat := 213783220333843885085285

theorem tailTrace_624512 : CollatzResearch.WordTrace tailWord_624512 prefixEnd_624512 213783220333843885085285 := by
  unfold tailWord_624512
  simp only [CollatzResearch.WordTrace]
  refine ⟨11388911956753578501609895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15185215942338104668813193 11388911956753578501609895)
  ·
    refine ⟨17083367935130367752414843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11388911956753578501609895 17083367935130367752414843)
    ·
      refine ⟨25625051902695551628622265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17083367935130367752414843 25625051902695551628622265)
      ·
        refine ⟨19218788927021663721466699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25625051902695551628622265 19218788927021663721466699)
        ·
          refine ⟨28828183390532495582200049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19218788927021663721466699 28828183390532495582200049)
          ·
            refine ⟨21621137542899371686650037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28828183390532495582200049 21621137542899371686650037)
            ·
              refine ⟨2026981644646816095623441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 21621137542899371686650037 2026981644646816095623441)
              ·
                refine ⟨1520236233485112071717581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2026981644646816095623441 1520236233485112071717581)
                ·
                  refine ⟨570088587556917026894093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1520236233485112071717581 570088587556917026894093)
                  ·
                    refine ⟨213783220333843885085285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 570088587556917026894093 213783220333843885085285)
                    ·
                      rfl

theorem cell22_624512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 5, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 5, 2, 3, 3].length) (baseStart_624512 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_624512 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_624512 prefixEnd_624512 := by exact prefixLift 624512
  have htrace : WordTrace (prefixWord ++ tailWord_624512) baseStart_624512 baseEnd_624512 := by
    simpa [prefixWord, tailWord_624512, baseEnd_624512] using wordTrace_append hprefix tailTrace_624512
  have hstable : (prefixWord ++ tailWord_624512).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_624512).length < 2 ^ (prefixWord ++ tailWord_624512).sum := by decide
  have hdescent : baseEnd_624512 < baseStart_624512 := by decide
  rcases family_descends (prefixWord ++ tailWord_624512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_624529 : List Nat := [1, 2, 2, 1, 1, 1, 5, 5, 1, 3]
def baseStart_624529 : Nat := 118140960795 + 624529 * 2 ^ 59
def prefixEnd_624529 : Nat := 4983230072969 + 3 ^ 40 * 624529 * 2
def baseEnd_624529 : Nat := 213789039781261507410233

theorem tailTrace_624529 : CollatzResearch.WordTrace tailWord_624529 prefixEnd_624529 213789039781261507410233 := by
  unfold tailWord_624529
  simp only [CollatzResearch.WordTrace]
  refine ⟨22778443954445568906588641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15185629302963712604392427 22778443954445568906588641)
  ·
    refine ⟨17083832965834176679941481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22778443954445568906588641 17083832965834176679941481)
    ·
      refine ⟨12812874724375632509956111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17083832965834176679941481 12812874724375632509956111)
      ·
        refine ⟨19219312086563448764934167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12812874724375632509956111 19219312086563448764934167)
        ·
          refine ⟨28828968129845173147401251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19219312086563448764934167 28828968129845173147401251)
          ·
            refine ⟨43243452194767759721101877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28828968129845173147401251 43243452194767759721101877)
            ·
              refine ⟨4054073643259477473853301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 43243452194767759721101877 4054073643259477473853301)
              ·
                refine ⟨380069404055576013173747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4054073643259477473853301 380069404055576013173747)
                ·
                  refine ⟨570104106083364019760621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 380069404055576013173747 570104106083364019760621)
                  ·
                    refine ⟨213789039781261507410233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 570104106083364019760621 213789039781261507410233)
                    ·
                      rfl

theorem cell22_624529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 5, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 5, 5, 1, 3].length) (baseStart_624529 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_624529 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_624529 prefixEnd_624529 := by exact prefixLift 624529
  have htrace : WordTrace (prefixWord ++ tailWord_624529) baseStart_624529 baseEnd_624529 := by
    simpa [prefixWord, tailWord_624529, baseEnd_624529] using wordTrace_append hprefix tailTrace_624529
  have hstable : (prefixWord ++ tailWord_624529).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_624529).length < 2 ^ (prefixWord ++ tailWord_624529).sum := by decide
  have hdescent : baseEnd_624529 < baseStart_624529 := by decide
  rcases family_descends (prefixWord ++ tailWord_624529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_624546 : List Nat := [3, 3, 1, 2, 3, 1, 2, 1, 3, 3]
def baseStart_624546 : Nat := 118140960795 + 624546 * 2 ^ 59
def prefixEnd_624546 : Nat := 4983230072969 + 3 ^ 40 * 624546 * 2
def baseEnd_624546 : Nat := 213794859228679129735181

theorem tailTrace_624546 : CollatzResearch.WordTrace tailWord_624546 prefixEnd_624546 213794859228679129735181 := by
  unfold tailWord_624546
  simp only [CollatzResearch.WordTrace]
  refine ⟨5694765998845995202489373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15186042663589320539971661 5694765998845995202489373)
  ·
    refine ⟨2135537249567248200933515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5694765998845995202489373 2135537249567248200933515)
    ·
      refine ⟨3203305874350872301400273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2135537249567248200933515 3203305874350872301400273)
      ·
        refine ⟨2402479405763154226050205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3203305874350872301400273 2402479405763154226050205)
        ·
          refine ⟨900929777161182834768827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2402479405763154226050205 900929777161182834768827)
          ·
            refine ⟨1351394665741774252153241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 900929777161182834768827 1351394665741774252153241)
            ·
              refine ⟨1013545999306330689114931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1351394665741774252153241 1013545999306330689114931)
              ·
                refine ⟨1520318998959496033672397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1013545999306330689114931 1520318998959496033672397)
                ·
                  refine ⟨570119624609811012627149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1520318998959496033672397 570119624609811012627149)
                  ·
                    refine ⟨213794859228679129735181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 570119624609811012627149 213794859228679129735181)
                    ·
                      rfl

theorem cell22_624546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 2, 1, 3, 3].length) (baseStart_624546 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_624546 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_624546 prefixEnd_624546 := by exact prefixLift 624546
  have htrace : WordTrace (prefixWord ++ tailWord_624546) baseStart_624546 baseEnd_624546 := by
    simpa [prefixWord, tailWord_624546, baseEnd_624546] using wordTrace_append hprefix tailTrace_624546
  have hstable : (prefixWord ++ tailWord_624546).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_624546).length < 2 ^ (prefixWord ++ tailWord_624546).sum := by decide
  have hdescent : baseEnd_624546 < baseStart_624546 := by decide
  rcases family_descends (prefixWord ++ tailWord_624546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_624570 : List Nat := [3, 1, 1, 1, 2, 1, 2, 3, 8]
def baseStart_624570 : Nat := 118140960795 + 624570 * 2 ^ 59
def prefixEnd_624570 : Nat := 4983230072969 + 3 ^ 40 * 624570 * 2
def baseEnd_624570 : Nat := 71267691639717022378369

theorem tailTrace_624570 : CollatzResearch.WordTrace tailWord_624570 prefixEnd_624570 71267691639717022378369 := by
  unfold tailWord_624570
  simp only [CollatzResearch.WordTrace]
  refine ⟨5694984836824258227207791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15186626231531355272554109 5694984836824258227207791)
  ·
    refine ⟨8542477255236387340811687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5694984836824258227207791 8542477255236387340811687)
    ·
      refine ⟨12813715882854581011217531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8542477255236387340811687 12813715882854581011217531)
      ·
        refine ⟨19220573824281871516826297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12813715882854581011217531 19220573824281871516826297)
        ·
          refine ⟨14415430368211403637619723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19220573824281871516826297 14415430368211403637619723)
          ·
            refine ⟨21623145552317105456429585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14415430368211403637619723 21623145552317105456429585)
            ·
              refine ⟨16217359164237829092322189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21623145552317105456429585 16217359164237829092322189)
              ·
                refine ⟨6081509686589185909620821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16217359164237829092322189 6081509686589185909620821)
                ·
                  refine ⟨71267691639717022378369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 6081509686589185909620821 71267691639717022378369)
                  ·
                    rfl

theorem cell22_624570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 3, 8].length) (baseStart_624570 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_624570 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_624570 prefixEnd_624570 := by exact prefixLift 624570
  have htrace : WordTrace (prefixWord ++ tailWord_624570) baseStart_624570 baseEnd_624570 := by
    simpa [prefixWord, tailWord_624570, baseEnd_624570] using wordTrace_append hprefix tailTrace_624570
  have hstable : (prefixWord ++ tailWord_624570).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_624570).length < 2 ^ (prefixWord ++ tailWord_624570).sum := by decide
  have hdescent : baseEnd_624570 < baseStart_624570 := by decide
  rcases family_descends (prefixWord ++ tailWord_624570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_624610 : List Nat := [3, 3, 3, 1, 3, 1, 2, 1, 5]
def baseStart_624610 : Nat := 118140960795 + 624610 * 2 ^ 59
def prefixEnd_624610 : Nat := 4983230072969 + 3 ^ 40 * 624610 * 2
def baseEnd_624610 : Nat := 71272255912201432044995

theorem tailTrace_624610 : CollatzResearch.WordTrace tailWord_624610 prefixEnd_624610 71272255912201432044995 := by
  unfold tailWord_624610
  simp only [CollatzResearch.WordTrace]
  refine ⟨5695349566788029935071821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15187598844768079826858189 5695349566788029935071821)
  ·
    refine ⟨2135756087545511225651933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5695349566788029935071821 2135756087545511225651933)
    ·
      refine ⟨800908532829566709619475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2135756087545511225651933 800908532829566709619475)
      ·
        refine ⟨1201362799244350064429213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 800908532829566709619475 1201362799244350064429213)
        ·
          refine ⟨450511049716631274160955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1201362799244350064429213 450511049716631274160955)
          ·
            refine ⟨675766574574946911241433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 450511049716631274160955 675766574574946911241433)
            ·
              refine ⟨506824930931210183431075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 675766574574946911241433 506824930931210183431075)
              ·
                refine ⟨760237396396815275146613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 506824930931210183431075 760237396396815275146613)
                ·
                  refine ⟨71272255912201432044995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 760237396396815275146613 71272255912201432044995)
                  ·
                    rfl

theorem cell22_624610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 3, 1, 2, 1, 5].length) (baseStart_624610 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_624610 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_624610 prefixEnd_624610 := by exact prefixLift 624610
  have htrace : WordTrace (prefixWord ++ tailWord_624610) baseStart_624610 baseEnd_624610 := by
    simpa [prefixWord, tailWord_624610, baseEnd_624610] using wordTrace_append hprefix tailTrace_624610
  have hstable : (prefixWord ++ tailWord_624610).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_624610).length < 2 ^ (prefixWord ++ tailWord_624610).sum := by decide
  have hdescent : baseEnd_624610 < baseStart_624610 := by decide
  rcases family_descends (prefixWord ++ tailWord_624610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_624664 : List Nat := [2, 1, 2, 3, 2, 1, 2, 3, 3, 3]
def baseStart_624664 : Nat := 118140960795 + 624664 * 2 ^ 59
def prefixEnd_624664 : Nat := 4983230072969 + 3 ^ 40 * 624664 * 2
def baseEnd_624664 : Nat := 213835253040166155284819

theorem tailTrace_624664 : CollatzResearch.WordTrace tailWord_624664 prefixEnd_624664 213835253040166155284819 := by
  unfold tailWord_624664
  simp only [CollatzResearch.WordTrace]
  refine ⟨11391683904478243481376523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15188911872637657975168697 11391683904478243481376523)
  ·
    refine ⟨17087525856717365222064785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11391683904478243481376523 17087525856717365222064785)
    ·
      refine ⟨12815644392538023916548589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17087525856717365222064785 12815644392538023916548589)
      ·
        refine ⟨4805866647201758968705721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12815644392538023916548589 4805866647201758968705721)
        ·
          refine ⟨3604399985401319226529291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4805866647201758968705721 3604399985401319226529291)
          ·
            refine ⟨5406599978101978839793937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3604399985401319226529291 5406599978101978839793937)
            ·
              refine ⟨4054949983576484129845453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5406599978101978839793937 4054949983576484129845453)
              ·
                refine ⟨1520606243841181548692045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4054949983576484129845453 1520606243841181548692045)
                ·
                  refine ⟨570227341440443080759517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1520606243841181548692045 570227341440443080759517)
                  ·
                    refine ⟨213835253040166155284819, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 570227341440443080759517 213835253040166155284819)
                    ·
                      rfl

theorem cell22_624664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 2, 3, 3, 3].length) (baseStart_624664 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_624664 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_624664 prefixEnd_624664 := by exact prefixLift 624664
  have htrace : WordTrace (prefixWord ++ tailWord_624664) baseStart_624664 baseEnd_624664 := by
    simpa [prefixWord, tailWord_624664, baseEnd_624664] using wordTrace_append hprefix tailTrace_624664
  have hstable : (prefixWord ++ tailWord_624664).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_624664).length < 2 ^ (prefixWord ++ tailWord_624664).sum := by decide
  have hdescent : baseEnd_624664 < baseStart_624664 := by decide
  rcases family_descends (prefixWord ++ tailWord_624664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_624694 : List Nat := [5, 1, 2, 1, 1, 1, 2, 2, 7]
def baseStart_624694 : Nat := 118140960795 + 624694 * 2 ^ 59
def prefixEnd_624694 : Nat := 4983230072969 + 3 ^ 40 * 624694 * 2
def baseEnd_624694 : Nat := 71281840884418692344909

theorem tailTrace_624694 : CollatzResearch.WordTrace tailWord_624694 prefixEnd_624694 71281840884418692344909 := by
  unfold tailWord_624694
  simp only [CollatzResearch.WordTrace]
  refine ⟨1424028874927987630396571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 15189641332565201390896757 1424028874927987630396571)
  ·
    refine ⟨2136043312391981445594857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1424028874927987630396571 2136043312391981445594857)
    ·
      refine ⟨1602032484293986084196143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2136043312391981445594857 1602032484293986084196143)
      ·
        refine ⟨2403048726440979126294215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1602032484293986084196143 2403048726440979126294215)
        ·
          refine ⟨3604573089661468689441323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2403048726440979126294215 3604573089661468689441323)
          ·
            refine ⟨5406859634492203034161985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3604573089661468689441323 5406859634492203034161985)
            ·
              refine ⟨4055144725869152275621489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5406859634492203034161985 4055144725869152275621489)
              ·
                refine ⟨3041358544401864206716117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4055144725869152275621489 3041358544401864206716117)
                ·
                  refine ⟨71281840884418692344909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3041358544401864206716117 71281840884418692344909)
                  ·
                    rfl

theorem cell22_624694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 2, 2, 7].length) (baseStart_624694 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_624694 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_624694 prefixEnd_624694 := by exact prefixLift 624694
  have htrace : WordTrace (prefixWord ++ tailWord_624694) baseStart_624694 baseEnd_624694 := by
    simpa [prefixWord, tailWord_624694, baseEnd_624694] using wordTrace_append hprefix tailTrace_624694
  have hstable : (prefixWord ++ tailWord_624694).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_624694).length < 2 ^ (prefixWord ++ tailWord_624694).sum := by decide
  have hdescent : baseEnd_624694 < baseStart_624694 := by decide
  rcases family_descends (prefixWord ++ tailWord_624694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_624707 : List Nat := [1, 1, 1, 3, 1, 2, 2, 2, 5, 4]
def baseStart_624707 : Nat := 118140960795 + 624707 * 2 ^ 59
def prefixEnd_624707 : Nat := 4983230072969 + 3 ^ 40 * 624707 * 2
def baseEnd_624707 : Nat := 213849972818928376459687

theorem tailTrace_624707 : CollatzResearch.WordTrace tailWord_624707 prefixEnd_624707 213849972818928376459687 := by
  unfold tailWord_624707
  simp only [CollatzResearch.WordTrace]
  refine ⟨22784936147800705306568375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15189957431867136871045583 22784936147800705306568375)
  ·
    refine ⟨34177404221701057959852563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22784936147800705306568375 34177404221701057959852563)
    ·
      refine ⟨51266106332551586939778845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34177404221701057959852563 51266106332551586939778845)
      ·
        refine ⟨19224789874706845102417067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51266106332551586939778845 19224789874706845102417067)
        ·
          refine ⟨28837184812060267653625601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19224789874706845102417067 28837184812060267653625601)
          ·
            refine ⟨21627888609045200740219201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28837184812060267653625601 21627888609045200740219201)
            ·
              refine ⟨16220916456783900555164401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21627888609045200740219201 16220916456783900555164401)
              ·
                refine ⟨12165687342587925416373301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16220916456783900555164401 12165687342587925416373301)
                ·
                  refine ⟨1140533188367618007784997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 12165687342587925416373301 1140533188367618007784997)
                  ·
                    refine ⟨213849972818928376459687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1140533188367618007784997 213849972818928376459687)
                    ·
                      rfl

theorem cell22_624707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 2, 5, 4].length) (baseStart_624707 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_624707 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_624707 prefixEnd_624707 := by exact prefixLift 624707
  have htrace : WordTrace (prefixWord ++ tailWord_624707) baseStart_624707 baseEnd_624707 := by
    simpa [prefixWord, tailWord_624707, baseEnd_624707] using wordTrace_append hprefix tailTrace_624707
  have hstable : (prefixWord ++ tailWord_624707).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_624707).length < 2 ^ (prefixWord ++ tailWord_624707).sum := by decide
  have hdescent : baseEnd_624707 < baseStart_624707 := by decide
  rcases family_descends (prefixWord ++ tailWord_624707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_624741 : List Nat := [1, 3, 1, 3, 2, 3, 2, 2, 1, 4]
def baseStart_624741 : Nat := 118140960795 + 624741 * 2 ^ 59
def prefixEnd_624741 : Nat := 4983230072969 + 3 ^ 40 * 624741 * 2
def baseEnd_624741 : Nat := 213861611713763621109583

theorem tailTrace_624741 : CollatzResearch.WordTrace tailWord_624741 prefixEnd_624741 213861611713763621109583 := by
  unfold tailWord_624741
  simp only [CollatzResearch.WordTrace]
  refine ⟨22786176229677529113306077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15190784153118352742204051 22786176229677529113306077)
  ·
    refine ⟨8544816086129073417489779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22786176229677529113306077 8544816086129073417489779)
    ·
      refine ⟨12817224129193610126234669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8544816086129073417489779 12817224129193610126234669)
      ·
        refine ⟨4806459048447603797338001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12817224129193610126234669 4806459048447603797338001)
        ·
          refine ⟨3604844286335702848003501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4806459048447603797338001 3604844286335702848003501)
          ·
            refine ⟨1351816607375888568001313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3604844286335702848003501 1351816607375888568001313)
            ·
              refine ⟨1013862455531916426000985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1351816607375888568001313 1013862455531916426000985)
              ·
                refine ⟨760396841648937319500739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1013862455531916426000985 760396841648937319500739)
                ·
                  refine ⟨1140595262473405979251109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 760396841648937319500739 1140595262473405979251109)
                  ·
                    refine ⟨213861611713763621109583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1140595262473405979251109 213861611713763621109583)
                    ·
                      rfl

theorem cell22_624741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 2, 2, 1, 4].length) (baseStart_624741 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_624741 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_624741 prefixEnd_624741 := by exact prefixLift 624741
  have htrace : WordTrace (prefixWord ++ tailWord_624741) baseStart_624741 baseEnd_624741 := by
    simpa [prefixWord, tailWord_624741, baseEnd_624741] using wordTrace_append hprefix tailTrace_624741
  have hstable : (prefixWord ++ tailWord_624741).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_624741).length < 2 ^ (prefixWord ++ tailWord_624741).sum := by decide
  have hdescent : baseEnd_624741 < baseStart_624741 := by decide
  rcases family_descends (prefixWord ++ tailWord_624741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_624773 : List Nat := [1, 3, 1, 1, 5, 2, 3, 2, 4]
def baseStart_624773 : Nat := 118140960795 + 624773 * 2 ^ 59
def prefixEnd_624773 : Nat := 4983230072969 + 3 ^ 40 * 624773 * 2
def baseEnd_624773 : Nat := 71290855322575401436495

theorem tailTrace_624773 : CollatzResearch.WordTrace tailWord_624773 prefixEnd_624773 71290855322575401436495 := by
  unfold tailWord_624773
  simp only [CollatzResearch.WordTrace]
  refine ⟨22787343365561598578470973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15191562243707732385647315 22787343365561598578470973)
  ·
    refine ⟨8545253762085599466926615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22787343365561598578470973 8545253762085599466926615)
    ·
      refine ⟨12817880643128399200389923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8545253762085599466926615 12817880643128399200389923)
      ·
        refine ⟨19226820964692598800584885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12817880643128399200389923 19226820964692598800584885)
        ·
          refine ⟨1802514465439931137554833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 19226820964692598800584885 1802514465439931137554833)
          ·
            refine ⟨1351885849079948353166125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1802514465439931137554833 1351885849079948353166125)
            ·
              refine ⟨506957193404980632437297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1351885849079948353166125 506957193404980632437297)
              ·
                refine ⟨380217895053735474327973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 506957193404980632437297 380217895053735474327973)
                ·
                  refine ⟨71290855322575401436495, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 380217895053735474327973 71290855322575401436495)
                  ·
                    rfl

theorem cell22_624773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 3, 2, 4].length) (baseStart_624773 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_624773 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_624773 prefixEnd_624773 := by exact prefixLift 624773
  have htrace : WordTrace (prefixWord ++ tailWord_624773) baseStart_624773 baseEnd_624773 := by
    simpa [prefixWord, tailWord_624773, baseEnd_624773] using wordTrace_append hprefix tailTrace_624773
  have hstable : (prefixWord ++ tailWord_624773).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_624773).length < 2 ^ (prefixWord ++ tailWord_624773).sum := by decide
  have hdescent : baseEnd_624773 < baseStart_624773 := by decide
  rcases family_descends (prefixWord ++ tailWord_624773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_624846 : List Nat := [4, 1, 1, 1, 4, 1, 2, 3, 5]
def baseStart_624846 : Nat := 118140960795 + 624846 * 2 ^ 59
def prefixEnd_624846 : Nat := 4983230072969 + 3 ^ 40 * 624846 * 2
def baseEnd_624846 : Nat := 71299185119859449078087

theorem tailTrace_624846 : CollatzResearch.WordTrace tailWord_624846 prefixEnd_624846 71299185119859449078087 := by
  unfold tailWord_624846
  simp only [CollatzResearch.WordTrace]
  refine ⟨2848750736787141505734799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15193337262864754697252261 2848750736787141505734799)
  ·
    refine ⟨4273126105180712258602199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2848750736787141505734799 4273126105180712258602199)
    ·
      refine ⟨6409689157771068387903299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4273126105180712258602199 6409689157771068387903299)
      ·
        refine ⟨9614533736656602581854949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6409689157771068387903299 9614533736656602581854949)
        ·
          refine ⟨1802725075623112984097803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9614533736656602581854949 1802725075623112984097803)
          ·
            refine ⟨2704087613434669476146705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1802725075623112984097803 2704087613434669476146705)
            ·
              refine ⟨2028065710076002107110029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2704087613434669476146705 2028065710076002107110029)
              ·
                refine ⟨760524641278500790166261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2028065710076002107110029 760524641278500790166261)
                ·
                  refine ⟨71299185119859449078087, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 760524641278500790166261 71299185119859449078087)
                  ·
                    rfl

theorem cell22_624846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 2, 3, 5].length) (baseStart_624846 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_624846 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_624846 prefixEnd_624846 := by exact prefixLift 624846
  have htrace : WordTrace (prefixWord ++ tailWord_624846) baseStart_624846 baseEnd_624846 := by
    simpa [prefixWord, tailWord_624846, baseEnd_624846] using wordTrace_append hprefix tailTrace_624846
  have hstable : (prefixWord ++ tailWord_624846).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_624846).length < 2 ^ (prefixWord ++ tailWord_624846).sum := by decide
  have hdescent : baseEnd_624846 < baseStart_624846 := by decide
  rcases family_descends (prefixWord ++ tailWord_624846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_624867 : List Nat := [1, 1, 1, 8, 1, 1, 2, 3, 1, 3]
def baseStart_624867 : Nat := 118140960795 + 624867 * 2 ^ 59
def prefixEnd_624867 : Nat := 4983230072969 + 3 ^ 40 * 624867 * 2
def baseEnd_624867 : Nat := 213904744088741292459197

theorem tailTrace_624867 : CollatzResearch.WordTrace tailWord_624867 prefixEnd_624867 213904744088741292459197 := by
  unfold tailWord_624867
  simp only [CollatzResearch.WordTrace]
  refine ⟨22790771827221052632392855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15193847884814035088261903 22790771827221052632392855)
  ·
    refine ⟨34186157740831578948589283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22790771827221052632392855 34186157740831578948589283)
    ·
      refine ⟨51279236611247368422883925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34186157740831578948589283 51279236611247368422883925)
      ·
        refine ⟨600928554038055098705671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 51279236611247368422883925 600928554038055098705671)
        ·
          refine ⟨901392831057082648058507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 600928554038055098705671 901392831057082648058507)
          ·
            refine ⟨1352089246585623972087761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 901392831057082648058507 1352089246585623972087761)
            ·
              refine ⟨1014066934939217979065821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1352089246585623972087761 1014066934939217979065821)
              ·
                refine ⟨380275100602206742149683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1014066934939217979065821 380275100602206742149683)
                ·
                  refine ⟨570412650903310113224525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 380275100602206742149683 570412650903310113224525)
                  ·
                    refine ⟨213904744088741292459197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 570412650903310113224525 213904744088741292459197)
                    ·
                      rfl

theorem cell22_624867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 2, 3, 1, 3].length) (baseStart_624867 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_624867 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_624867 prefixEnd_624867 := by exact prefixLift 624867
  have htrace : WordTrace (prefixWord ++ tailWord_624867) baseStart_624867 baseEnd_624867 := by
    simpa [prefixWord, tailWord_624867, baseEnd_624867] using wordTrace_append hprefix tailTrace_624867
  have hstable : (prefixWord ++ tailWord_624867).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_624867).length < 2 ^ (prefixWord ++ tailWord_624867).sum := by decide
  have hdescent : baseEnd_624867 < baseStart_624867 := by decide
  rcases family_descends (prefixWord ++ tailWord_624867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_624874 : List Nat := [3, 1, 3, 1, 1, 2, 1, 2, 8]
def baseStart_624874 : Nat := 118140960795 + 624874 * 2 ^ 59
def prefixEnd_624874 : Nat := 4983230072969 + 3 ^ 40 * 624874 * 2
def baseEnd_624874 : Nat := 71302380110598535844725

theorem tailTrace_624874 : CollatzResearch.WordTrace tailWord_624874 prefixEnd_624874 71302380110598535844725 := by
  unfold tailWord_624874
  simp only [CollatzResearch.WordTrace]
  refine ⟨5697756784548923206974419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15194018092130461885265117 5697756784548923206974419)
  ·
    refine ⟨8546635176823384810461629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5697756784548923206974419 8546635176823384810461629)
    ·
      refine ⟨3204988191308769303923111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8546635176823384810461629 3204988191308769303923111)
      ·
        refine ⟨4807482286963153955884667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3204988191308769303923111 4807482286963153955884667)
        ·
          refine ⟨7211223430444730933827001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4807482286963153955884667 7211223430444730933827001)
          ·
            refine ⟨5408417572833548200370251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7211223430444730933827001 5408417572833548200370251)
            ·
              refine ⟨8112626359250322300555377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5408417572833548200370251 8112626359250322300555377)
              ·
                refine ⟨6084469769437741725416533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8112626359250322300555377 6084469769437741725416533)
                ·
                  refine ⟨71302380110598535844725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 6084469769437741725416533 71302380110598535844725)
                  ·
                    rfl

theorem cell22_624874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 2, 8].length) (baseStart_624874 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_624874 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_624874 prefixEnd_624874 := by exact prefixLift 624874
  have htrace : WordTrace (prefixWord ++ tailWord_624874) baseStart_624874 baseEnd_624874 := by
    simpa [prefixWord, tailWord_624874, baseEnd_624874] using wordTrace_append hprefix tailTrace_624874
  have hstable : (prefixWord ++ tailWord_624874).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_624874).length < 2 ^ (prefixWord ++ tailWord_624874).sum := by decide
  have hdescent : baseEnd_624874 < baseStart_624874 := by decide
  rcases family_descends (prefixWord ++ tailWord_624874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_624876 : List Nat := [2, 2, 1, 1, 2, 3, 3, 3, 1, 4]
def baseStart_624876 : Nat := 118140960795 + 624876 * 2 ^ 59
def prefixEnd_624876 : Nat := 4983230072969 + 3 ^ 40 * 624876 * 2
def baseEnd_624876 : Nat := 213907824972668268984169

theorem tailTrace_624876 : CollatzResearch.WordTrace tailWord_624876 prefixEnd_624876 213907824972668268984169 := by
  unfold tailWord_624876
  simp only [CollatzResearch.WordTrace]
  refine ⟨11395550042094223584735241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15194066722792298112980321 11395550042094223584735241)
  ·
    refine ⟨8546662531570667688551431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11395550042094223584735241 8546662531570667688551431)
    ·
      refine ⟨12819993797356001532827147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8546662531570667688551431 12819993797356001532827147)
      ·
        refine ⟨19229990696034002299240721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12819993797356001532827147 19229990696034002299240721)
        ·
          refine ⟨14422493022025501724430541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19229990696034002299240721 14422493022025501724430541)
          ·
            refine ⟨5408434883259563146661453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14422493022025501724430541 5408434883259563146661453)
            ·
              refine ⟨2028163081222336179998045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5408434883259563146661453 2028163081222336179998045)
              ·
                refine ⟨760561155458376067499267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2028163081222336179998045 760561155458376067499267)
                ·
                  refine ⟨1140841733187564101248901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 760561155458376067499267 1140841733187564101248901)
                  ·
                    refine ⟨213907824972668268984169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1140841733187564101248901 213907824972668268984169)
                    ·
                      rfl

theorem cell22_624876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 4].length) (baseStart_624876 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_624876 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_624876 prefixEnd_624876 := by exact prefixLift 624876
  have htrace : WordTrace (prefixWord ++ tailWord_624876) baseStart_624876 baseEnd_624876 := by
    simpa [prefixWord, tailWord_624876, baseEnd_624876] using wordTrace_append hprefix tailTrace_624876
  have hstable : (prefixWord ++ tailWord_624876).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_624876).length < 2 ^ (prefixWord ++ tailWord_624876).sum := by decide
  have hdescent : baseEnd_624876 < baseStart_624876 := by decide
  rcases family_descends (prefixWord ++ tailWord_624876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_624906 : List Nat := [3, 1, 2, 2, 1, 1, 5, 1, 1, 5]
def baseStart_624906 : Nat := 118140960795 + 624906 * 2 ^ 59
def prefixEnd_624906 : Nat := 4983230072969 + 3 ^ 40 * 624906 * 2
def baseEnd_624906 : Nat := 213918094585758190734077

theorem tailTrace_624906 : CollatzResearch.WordTrace tailWord_624906 prefixEnd_624906 213918094585758190734077 := by
  unfold tailWord_624906
  simp only [CollatzResearch.WordTrace]
  refine ⟨5698048568519940573265643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15194796182719841528708381 5698048568519940573265643)
  ·
    refine ⟨8547072852779910859898465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5698048568519940573265643 8547072852779910859898465)
    ·
      refine ⟨6410304639584933144923849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8547072852779910859898465 6410304639584933144923849)
      ·
        refine ⟨4807728479688699858692887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6410304639584933144923849 4807728479688699858692887)
        ·
          refine ⟨7211592719533049788039331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4807728479688699858692887 7211592719533049788039331)
          ·
            refine ⟨10817389079299574682058997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7211592719533049788039331 10817389079299574682058997)
            ·
              refine ⟨1014130226184335126443031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 10817389079299574682058997 1014130226184335126443031)
              ·
                refine ⟨1521195339276502689664547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1014130226184335126443031 1521195339276502689664547)
                ·
                  refine ⟨2281793008914754034496821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1521195339276502689664547 2281793008914754034496821)
                  ·
                    refine ⟨213918094585758190734077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2281793008914754034496821 213918094585758190734077)
                    ·
                      rfl

theorem cell22_624906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 5, 1, 1, 5].length) (baseStart_624906 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_624906 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_624906 prefixEnd_624906 := by exact prefixLift 624906
  have htrace : WordTrace (prefixWord ++ tailWord_624906) baseStart_624906 baseEnd_624906 := by
    simpa [prefixWord, tailWord_624906, baseEnd_624906] using wordTrace_append hprefix tailTrace_624906
  have hstable : (prefixWord ++ tailWord_624906).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_624906).length < 2 ^ (prefixWord ++ tailWord_624906).sum := by decide
  have hdescent : baseEnd_624906 < baseStart_624906 := by decide
  rcases family_descends (prefixWord ++ tailWord_624906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_624942 : List Nat := [4, 1, 3, 3, 2, 1, 1, 1, 6]
def baseStart_624942 : Nat := 118140960795 + 624942 * 2 ^ 59
def prefixEnd_624942 : Nat := 4983230072969 + 3 ^ 40 * 624942 * 2
def baseEnd_624942 : Nat := 71310139373822032277989

theorem tailTrace_624942 : CollatzResearch.WordTrace tailWord_624942 prefixEnd_624942 71310139373822032277989 := by
  unfold tailWord_624942
  simp only [CollatzResearch.WordTrace]
  refine ⟨2849188412743667555171635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15195671534632893627582053 2849188412743667555171635)
  ·
    refine ⟨4273782619115501332757453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2849188412743667555171635 4273782619115501332757453)
    ·
      refine ⟨1602668482168312999784045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4273782619115501332757453 1602668482168312999784045)
      ·
        refine ⟨601000680813117374919017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1602668482168312999784045 601000680813117374919017)
        ·
          refine ⟨450750510609838031189263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 601000680813117374919017 450750510609838031189263)
          ·
            refine ⟨676125765914757046783895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 450750510609838031189263 676125765914757046783895)
            ·
              refine ⟨1014188648872135570175843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 676125765914757046783895 1014188648872135570175843)
              ·
                refine ⟨1521282973308203355263765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1014188648872135570175843 1521282973308203355263765)
                ·
                  refine ⟨71310139373822032277989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1521282973308203355263765 71310139373822032277989)
                  ·
                    rfl

theorem cell22_624942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 2, 1, 1, 1, 6].length) (baseStart_624942 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_624942 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_624942 prefixEnd_624942 := by exact prefixLift 624942
  have htrace : WordTrace (prefixWord ++ tailWord_624942) baseStart_624942 baseEnd_624942 := by
    simpa [prefixWord, tailWord_624942, baseEnd_624942] using wordTrace_append hprefix tailTrace_624942
  have hstable : (prefixWord ++ tailWord_624942).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_624942).length < 2 ^ (prefixWord ++ tailWord_624942).sum := by decide
  have hdescent : baseEnd_624942 < baseStart_624942 := by decide
  rcases family_descends (prefixWord ++ tailWord_624942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_624979 : List Nat := [1, 1, 1, 2, 1, 1, 4, 1, 3, 7]
def baseStart_624979 : Nat := 118140960795 + 624979 * 2 ^ 59
def prefixEnd_624979 : Nat := 4983230072969 + 3 ^ 40 * 624979 * 2
def baseEnd_624979 : Nat := 213943083977610333658853

theorem tailTrace_624979 : CollatzResearch.WordTrace tailWord_624979 prefixEnd_624979 213943083977610333658853 := by
  unfold tailWord_624979
  simp only [CollatzResearch.WordTrace]
  refine ⟨22794856802815295760469991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15196571201876863840313327 22794856802815295760469991)
  ·
    refine ⟨34192285204222943640704987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22794856802815295760469991 34192285204222943640704987)
    ·
      refine ⟨51288427806334415461057481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34192285204222943640704987 51288427806334415461057481)
      ·
        refine ⟨38466320854750811595793111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51288427806334415461057481 38466320854750811595793111)
        ·
          refine ⟨57699481282126217393689667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38466320854750811595793111 57699481282126217393689667)
          ·
            refine ⟨86549221923189326090534501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57699481282126217393689667 86549221923189326090534501)
            ·
              refine ⟨16227979110597998641975219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 86549221923189326090534501 16227979110597998641975219)
              ·
                refine ⟨24341968665896997962962829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16227979110597998641975219 24341968665896997962962829)
                ·
                  refine ⟨9128238249711374236111061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24341968665896997962962829 9128238249711374236111061)
                  ·
                    refine ⟨213943083977610333658853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 9128238249711374236111061 213943083977610333658853)
                    ·
                      rfl

theorem cell22_624979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 1, 3, 7].length) (baseStart_624979 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_624979 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_624979 prefixEnd_624979 := by exact prefixLift 624979
  have htrace : WordTrace (prefixWord ++ tailWord_624979) baseStart_624979 baseEnd_624979 := by
    simpa [prefixWord, tailWord_624979, baseEnd_624979] using wordTrace_append hprefix tailTrace_624979
  have hstable : (prefixWord ++ tailWord_624979).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_624979).length < 2 ^ (prefixWord ++ tailWord_624979).sum := by decide
  have hdescent : baseEnd_624979 < baseStart_624979 := by decide
  rcases family_descends (prefixWord ++ tailWord_624979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_624996 : List Nat := [2, 3, 1, 1, 3, 1, 2, 2, 2, 5]
def baseStart_624996 : Nat := 118140960795 + 624996 * 2 ^ 59
def prefixEnd_624996 : Nat := 4983230072969 + 3 ^ 40 * 624996 * 2
def baseEnd_624996 : Nat := 213948903425027955983801

theorem tailTrace_624996 : CollatzResearch.WordTrace tailWord_624996 prefixEnd_624996 213948903425027955983801 := by
  unfold tailWord_624996
  simp only [CollatzResearch.WordTrace]
  refine ⟨11397738421876853831919421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15196984562502471775892561 11397738421876853831919421)
  ·
    refine ⟨4274151908203820186969783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11397738421876853831919421 4274151908203820186969783)
    ·
      refine ⟨6411227862305730280454675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4274151908203820186969783 6411227862305730280454675)
      ·
        refine ⟨9616841793458595420682013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6411227862305730280454675 9616841793458595420682013)
        ·
          refine ⟨3606315672546973282755755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9616841793458595420682013 3606315672546973282755755)
          ·
            refine ⟨5409473508820459924133633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3606315672546973282755755 5409473508820459924133633)
            ·
              refine ⟨4057105131615344943100225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5409473508820459924133633 4057105131615344943100225)
              ·
                refine ⟨3042828848711508707325169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4057105131615344943100225 3042828848711508707325169)
                ·
                  refine ⟨2282121636533631530493877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3042828848711508707325169 2282121636533631530493877)
                  ·
                    refine ⟨213948903425027955983801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2282121636533631530493877 213948903425027955983801)
                    ·
                      rfl

theorem cell22_624996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 2, 2, 2, 5].length) (baseStart_624996 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_624996 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_624996 prefixEnd_624996 := by exact prefixLift 624996
  have htrace : WordTrace (prefixWord ++ tailWord_624996) baseStart_624996 baseEnd_624996 := by
    simpa [prefixWord, tailWord_624996, baseEnd_624996] using wordTrace_append hprefix tailTrace_624996
  have hstable : (prefixWord ++ tailWord_624996).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_624996).length < 2 ^ (prefixWord ++ tailWord_624996).sum := by decide
  have hdescent : baseEnd_624996 < baseStart_624996 := by decide
  rcases family_descends (prefixWord ++ tailWord_624996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_625002 : List Nat := [3, 1, 3, 3, 1, 2, 1, 4, 1, 3]
def baseStart_625002 : Nat := 118140960795 + 625002 * 2 ^ 59
def prefixEnd_625002 : Nat := 4983230072969 + 3 ^ 40 * 625002 * 2
def baseEnd_625002 : Nat := 213950957347645940333783

theorem tailTrace_625002 : CollatzResearch.WordTrace tailWord_625002 prefixEnd_625002 213950957347645940333783 := by
  unfold tailWord_625002
  simp only [CollatzResearch.WordTrace]
  refine ⟨5698923920432992672139315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15197130454487980459038173 5698923920432992672139315)
  ·
    refine ⟨8548385880649489008208973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5698923920432992672139315 8548385880649489008208973)
    ·
      refine ⟨3205644705243558378078365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8548385880649489008208973 3205644705243558378078365)
      ·
        refine ⟨1202116764466334391779387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3205644705243558378078365 1202116764466334391779387)
        ·
          refine ⟨1803175146699501587669081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1202116764466334391779387 1803175146699501587669081)
          ·
            refine ⟨1352381360024626190751811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1803175146699501587669081 1352381360024626190751811)
            ·
              refine ⟨2028572040036939286127717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1352381360024626190751811 2028572040036939286127717)
              ·
                refine ⟨380357257506926116148947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2028572040036939286127717 380357257506926116148947)
                ·
                  refine ⟨570535886260389174223421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 380357257506926116148947 570535886260389174223421)
                  ·
                    refine ⟨213950957347645940333783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 570535886260389174223421 213950957347645940333783)
                    ·
                      rfl

theorem cell22_625002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 1, 4, 1, 3].length) (baseStart_625002 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_625002 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_625002 prefixEnd_625002 := by exact prefixLift 625002
  have htrace : WordTrace (prefixWord ++ tailWord_625002) baseStart_625002 baseEnd_625002 := by
    simpa [prefixWord, tailWord_625002, baseEnd_625002] using wordTrace_append hprefix tailTrace_625002
  have hstable : (prefixWord ++ tailWord_625002).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_625002).length < 2 ^ (prefixWord ++ tailWord_625002).sum := by decide
  have hdescent : baseEnd_625002 < baseStart_625002 := by decide
  rcases family_descends (prefixWord ++ tailWord_625002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_625013 : List Nat := [1, 3, 4, 1, 2, 2, 1, 1, 2, 5]
def baseStart_625013 : Nat := 118140960795 + 625013 * 2 ^ 59
def prefixEnd_625013 : Nat := 4983230072969 + 3 ^ 40 * 625013 * 2
def baseEnd_625013 : Nat := 213954722872445578308749

theorem tailTrace_625013 : CollatzResearch.WordTrace tailWord_625013 prefixEnd_625013 213954722872445578308749 := by
  unfold tailWord_625013
  simp only [CollatzResearch.WordTrace]
  refine ⟨22796096884692119567207693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15197397923128079711471795 22796096884692119567207693)
  ·
    refine ⟨8548536331759544837702885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22796096884692119567207693 8548536331759544837702885)
    ·
      refine ⟨1602850562204914657069291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8548536331759544837702885 1602850562204914657069291)
      ·
        refine ⟨2404275843307371985603937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1602850562204914657069291 2404275843307371985603937)
        ·
          refine ⟨1803206882480528989202953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2404275843307371985603937 1803206882480528989202953)
          ·
            refine ⟨1352405161860396741902215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1803206882480528989202953 1352405161860396741902215)
            ·
              refine ⟨2028607742790595112853323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1352405161860396741902215 2028607742790595112853323)
              ·
                refine ⟨3042911614185892669279985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2028607742790595112853323 3042911614185892669279985)
                ·
                  refine ⟨2282183710639419501959989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3042911614185892669279985 2282183710639419501959989)
                  ·
                    refine ⟨213954722872445578308749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2282183710639419501959989 213954722872445578308749)
                    ·
                      rfl

theorem cell22_625013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 1, 1, 2, 5].length) (baseStart_625013 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_625013 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_625013 prefixEnd_625013 := by exact prefixLift 625013
  have htrace : WordTrace (prefixWord ++ tailWord_625013) baseStart_625013 baseEnd_625013 := by
    simpa [prefixWord, tailWord_625013, baseEnd_625013] using wordTrace_append hprefix tailTrace_625013
  have hstable : (prefixWord ++ tailWord_625013).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_625013).length < 2 ^ (prefixWord ++ tailWord_625013).sum := by decide
  have hdescent : baseEnd_625013 < baseStart_625013 := by decide
  rcases family_descends (prefixWord ++ tailWord_625013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_625028 : List Nat := [2, 3, 2, 1, 1, 2, 2, 4, 1, 4]
def baseStart_625028 : Nat := 118140960795 + 625028 * 2 ^ 59
def prefixEnd_625028 : Nat := 4983230072969 + 3 ^ 40 * 625028 * 2
def baseEnd_625028 : Nat := 213959857678990539183703

theorem tailTrace_625028 : CollatzResearch.WordTrace tailWord_625028 prefixEnd_625028 213959857678990539183703 := by
  unfold tailWord_625028
  simp only [CollatzResearch.WordTrace]
  refine ⟨11398321989818888564501869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15197762653091851419335825 11398321989818888564501869)
  ·
    refine ⟨4274370746182083211688201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11398321989818888564501869 4274370746182083211688201)
    ·
      refine ⟨3205778059636562408766151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4274370746182083211688201 3205778059636562408766151)
      ·
        refine ⟨4808667089454843613149227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3205778059636562408766151 4808667089454843613149227)
        ·
          refine ⟨7213000634182265419723841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4808667089454843613149227 7213000634182265419723841)
          ·
            refine ⟨5409750475636699064792881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7213000634182265419723841 5409750475636699064792881)
            ·
              refine ⟨4057312856727524298594661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5409750475636699064792881 4057312856727524298594661)
              ·
                refine ⟨760746160636410805986499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4057312856727524298594661 760746160636410805986499)
                ·
                  refine ⟨1141119240954616208979749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 760746160636410805986499 1141119240954616208979749)
                  ·
                    refine ⟨213959857678990539183703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1141119240954616208979749 213959857678990539183703)
                    ·
                      rfl

theorem cell22_625028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 2, 4, 1, 4].length) (baseStart_625028 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_625028 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_625028 prefixEnd_625028 := by exact prefixLift 625028
  have htrace : WordTrace (prefixWord ++ tailWord_625028) baseStart_625028 baseEnd_625028 := by
    simpa [prefixWord, tailWord_625028, baseEnd_625028] using wordTrace_append hprefix tailTrace_625028
  have hstable : (prefixWord ++ tailWord_625028).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_625028).length < 2 ^ (prefixWord ++ tailWord_625028).sum := by decide
  have hdescent : baseEnd_625028 < baseStart_625028 := by decide
  rcases family_descends (prefixWord ++ tailWord_625028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_625122 : List Nat := [3, 3, 3, 2, 1, 1, 2, 7]
def baseStart_625122 : Nat := 118140960795 + 625122 * 2 ^ 59
def prefixEnd_625122 : Nat := 4983230072969 + 3 ^ 40 * 625122 * 2
def baseEnd_625122 : Nat := 23776892866667291925935

theorem tailTrace_625122 : CollatzResearch.WordTrace tailWord_625122 prefixEnd_625122 23776892866667291925935 := by
  unfold tailWord_625122
  simp only [CollatzResearch.WordTrace]
  refine ⟨5700018110324307795731405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15200048294198154121950413 5700018110324307795731405)
  ·
    refine ⟨2137506791371615423399277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5700018110324307795731405 2137506791371615423399277)
    ·
      refine ⟨801565046764355783774729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2137506791371615423399277 801565046764355783774729)
      ·
        refine ⟨601173785073266837831047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 801565046764355783774729 601173785073266837831047)
        ·
          refine ⟨901760677609900256746571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 601173785073266837831047 901760677609900256746571)
          ·
            refine ⟨1352641016414850385119857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 901760677609900256746571 1352641016414850385119857)
            ·
              refine ⟨1014480762311137788839893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1352641016414850385119857 1014480762311137788839893)
              ·
                refine ⟨23776892866667291925935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1014480762311137788839893 23776892866667291925935)
                ·
                  rfl

theorem cell22_625122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 2, 7].length) (baseStart_625122 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_625122 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_625122 prefixEnd_625122 := by exact prefixLift 625122
  have htrace : WordTrace (prefixWord ++ tailWord_625122) baseStart_625122 baseEnd_625122 := by
    simpa [prefixWord, tailWord_625122, baseEnd_625122] using wordTrace_append hprefix tailTrace_625122
  have hstable : (prefixWord ++ tailWord_625122).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_625122).length < 2 ^ (prefixWord ++ tailWord_625122).sum := by decide
  have hdescent : baseEnd_625122 < baseStart_625122 := by decide
  rcases family_descends (prefixWord ++ tailWord_625122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_625131 : List Nat := [1, 1, 1, 1, 2, 3, 4, 1, 1, 7]
def baseStart_625131 : Nat := 118140960795 + 625131 * 2 ^ 59
def prefixEnd_625131 : Nat := 4983230072969 + 3 ^ 40 * 625131 * 2
def baseEnd_625131 : Nat := 213995116683932603858387

theorem tailTrace_625131 : CollatzResearch.WordTrace tailWord_625131 prefixEnd_625131 213995116683932603858387 := by
  unfold tailWord_625131
  simp only [CollatzResearch.WordTrace]
  refine ⟨22800400698264625720003247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15200267132176417146668831 22800400698264625720003247)
  ·
    refine ⟨34200601047396938580004871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22800400698264625720003247 34200601047396938580004871)
    ·
      refine ⟨51300901571095407870007307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34200601047396938580004871 51300901571095407870007307)
      ·
        refine ⟨76951352356643111805010961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51300901571095407870007307 76951352356643111805010961)
        ·
          refine ⟨57713514267482333853758221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76951352356643111805010961 57713514267482333853758221)
          ·
            refine ⟨21642567850305875195159333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 57713514267482333853758221 21642567850305875195159333)
            ·
              refine ⟨4057981471932351599092375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21642567850305875195159333 4057981471932351599092375)
              ·
                refine ⟨6086972207898527398638563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4057981471932351599092375 6086972207898527398638563)
                ·
                  refine ⟨9130458311847791097957845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6086972207898527398638563 9130458311847791097957845)
                  ·
                    refine ⟨213995116683932603858387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 9130458311847791097957845 213995116683932603858387)
                    ·
                      rfl

theorem cell22_625131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 4, 1, 1, 7].length) (baseStart_625131 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_625131 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_625131 prefixEnd_625131 := by exact prefixLift 625131
  have htrace : WordTrace (prefixWord ++ tailWord_625131) baseStart_625131 baseEnd_625131 := by
    simpa [prefixWord, tailWord_625131, baseEnd_625131] using wordTrace_append hprefix tailTrace_625131
  have hstable : (prefixWord ++ tailWord_625131).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_625131).length < 2 ^ (prefixWord ++ tailWord_625131).sum := by decide
  have hdescent : baseEnd_625131 < baseStart_625131 := by decide
  rcases family_descends (prefixWord ++ tailWord_625131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_625161 : List Nat := [1, 2, 1, 1, 3, 1, 2, 1, 10]
def baseStart_625161 : Nat := 118140960795 + 625161 * 2 ^ 59
def prefixEnd_625161 : Nat := 4983230072969 + 3 ^ 40 * 625161 * 2
def baseEnd_625161 : Nat := 71335128765674175202765

theorem tailTrace_625161 : CollatzResearch.WordTrace tailWord_625161 prefixEnd_625161 71335128765674175202765 := by
  unfold tailWord_625161
  simp only [CollatzResearch.WordTrace]
  refine ⟨22801494888155940843595337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15200996592103960562396891 22801494888155940843595337)
  ·
    refine ⟨17101121166116955632696503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22801494888155940843595337 17101121166116955632696503)
    ·
      refine ⟨25651681749175433449044755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17101121166116955632696503 25651681749175433449044755)
      ·
        refine ⟨38477522623763150173567133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25651681749175433449044755 38477522623763150173567133)
        ·
          refine ⟨14429070983911181315087675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38477522623763150173567133 14429070983911181315087675)
          ·
            refine ⟨21643606475866771972631513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14429070983911181315087675 21643606475866771972631513)
            ·
              refine ⟨16232704856900078979473635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21643606475866771972631513 16232704856900078979473635)
              ·
                refine ⟨24349057285350118469210453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16232704856900078979473635 24349057285350118469210453)
                ·
                  refine ⟨71335128765674175202765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 24349057285350118469210453 71335128765674175202765)
                  ·
                    rfl

theorem cell22_625161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 1, 10].length) (baseStart_625161 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_625161 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_625161 prefixEnd_625161 := by exact prefixLift 625161
  have htrace : WordTrace (prefixWord ++ tailWord_625161) baseStart_625161 baseEnd_625161 := by
    simpa [prefixWord, tailWord_625161, baseEnd_625161] using wordTrace_append hprefix tailTrace_625161
  have hstable : (prefixWord ++ tailWord_625161).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_625161).length < 2 ^ (prefixWord ++ tailWord_625161).sum := by decide
  have hdescent : baseEnd_625161 < baseStart_625161 := by decide
  rcases family_descends (prefixWord ++ tailWord_625161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_625208 : List Nat := [2, 1, 2, 1, 4, 1, 3, 1, 1, 6]
def baseStart_625208 : Nat := 118140960795 + 625208 * 2 ^ 59
def prefixEnd_625208 : Nat := 4983230072969 + 3 ^ 40 * 625208 * 2
def baseEnd_625208 : Nat := 214021475357530069683151

theorem tailTrace_625208 : CollatzResearch.WordTrace tailWord_625208 prefixEnd_625208 214021475357530069683151 := by
  unfold tailWord_625208
  simp only [CollatzResearch.WordTrace]
  refine ⟨11401604559492833935278139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15202139412657111913704185 11401604559492833935278139)
  ·
    refine ⟨17102406839239250902917209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11401604559492833935278139 17102406839239250902917209)
    ·
      refine ⟨12826805129429438177187907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17102406839239250902917209 12826805129429438177187907)
      ·
        refine ⟨19240207694144157265781861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12826805129429438177187907 19240207694144157265781861)
        ·
          refine ⟨3607538942652029487334099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19240207694144157265781861 3607538942652029487334099)
          ·
            refine ⟨5411308413978044231001149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3607538942652029487334099 5411308413978044231001149)
            ·
              refine ⟨2029240655241766586625431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5411308413978044231001149 2029240655241766586625431)
              ·
                refine ⟨3043860982862649879938147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2029240655241766586625431 3043860982862649879938147)
                ·
                  refine ⟨4565791474293974819907221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3043860982862649879938147 4565791474293974819907221)
                  ·
                    refine ⟨214021475357530069683151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4565791474293974819907221 214021475357530069683151)
                    ·
                      rfl

theorem cell22_625208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 3, 1, 1, 6].length) (baseStart_625208 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_625208 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_625208 prefixEnd_625208 := by exact prefixLift 625208
  have htrace : WordTrace (prefixWord ++ tailWord_625208) baseStart_625208 baseEnd_625208 := by
    simpa [prefixWord, tailWord_625208, baseEnd_625208] using wordTrace_append hprefix tailTrace_625208
  have hstable : (prefixWord ++ tailWord_625208).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_625208).length < 2 ^ (prefixWord ++ tailWord_625208).sum := by decide
  have hdescent : baseEnd_625208 < baseStart_625208 := by decide
  rcases family_descends (prefixWord ++ tailWord_625208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_625212 : List Nat := [2, 2, 2, 2, 3, 2, 2, 3, 4]
def baseStart_625212 : Nat := 118140960795 + 625212 * 2 ^ 59
def prefixEnd_625212 : Nat := 4983230072969 + 3 ^ 40 * 625212 * 2
def baseEnd_625212 : Nat := 71340948213091797527713

theorem tailTrace_625212 : CollatzResearch.WordTrace tailWord_625212 prefixEnd_625212 71340948213091797527713 := by
  unfold tailWord_625212
  simp only [CollatzResearch.WordTrace]
  refine ⟨11401677505485588276850945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15202236673980784369134593 11401677505485588276850945)
  ·
    refine ⟨8551258129114191207638209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11401677505485588276850945 8551258129114191207638209)
    ·
      refine ⟨6413443596835643405728657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8551258129114191207638209 6413443596835643405728657)
      ·
        refine ⟨4810082697626732554296493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6413443596835643405728657 4810082697626732554296493)
        ·
          refine ⟨1803781011610024707861185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4810082697626732554296493 1803781011610024707861185)
          ·
            refine ⟨1352835758707518530895889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1803781011610024707861185 1352835758707518530895889)
            ·
              refine ⟨1014626819030638898171917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1352835758707518530895889 1014626819030638898171917)
              ·
                refine ⟨380485057136489586814469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1014626819030638898171917 380485057136489586814469)
                ·
                  refine ⟨71340948213091797527713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 380485057136489586814469 71340948213091797527713)
                  ·
                    rfl

theorem cell22_625212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 2, 3, 4].length) (baseStart_625212 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_625212 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_625212 prefixEnd_625212 := by exact prefixLift 625212
  have htrace : WordTrace (prefixWord ++ tailWord_625212) baseStart_625212 baseEnd_625212 := by
    simpa [prefixWord, tailWord_625212, baseEnd_625212] using wordTrace_append hprefix tailTrace_625212
  have hstable : (prefixWord ++ tailWord_625212).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_625212).length < 2 ^ (prefixWord ++ tailWord_625212).sum := by decide
  have hdescent : baseEnd_625212 < baseStart_625212 := by decide
  rcases family_descends (prefixWord ++ tailWord_625212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_625214 : List Nat := [4, 2, 1, 4, 1, 1, 1, 3, 1, 4]
def baseStart_625214 : Nat := 118140960795 + 625214 * 2 ^ 59
def prefixEnd_625214 : Nat := 4983230072969 + 3 ^ 40 * 625214 * 2
def baseEnd_625214 : Nat := 214023529280148054033133

theorem tailTrace_625214 : CollatzResearch.WordTrace tailWord_625214 prefixEnd_625214 214023529280148054033133 := by
  unfold tailWord_625214
  simp only [CollatzResearch.WordTrace]
  refine ⟨2850428494620491361909337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15202285304642620596849797 2850428494620491361909337)
  ·
    refine ⟨2137821370965368521432003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2850428494620491361909337 2137821370965368521432003)
    ·
      refine ⟨3206732056448052782148005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2137821370965368521432003 3206732056448052782148005)
      ·
        refine ⟨601262260584009896652751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3206732056448052782148005 601262260584009896652751)
        ·
          refine ⟨901893390876014844979127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 601262260584009896652751 901893390876014844979127)
          ·
            refine ⟨1352840086314022267468691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 901893390876014844979127 1352840086314022267468691)
            ·
              refine ⟨2029260129471033401203037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1352840086314022267468691 2029260129471033401203037)
              ·
                refine ⟨760972548551637525451139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2029260129471033401203037 760972548551637525451139)
                ·
                  refine ⟨1141458822827456288176709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 760972548551637525451139 1141458822827456288176709)
                  ·
                    refine ⟨214023529280148054033133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1141458822827456288176709 214023529280148054033133)
                    ·
                      rfl

theorem cell22_625214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 1, 3, 1, 4].length) (baseStart_625214 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_625214 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_625214 prefixEnd_625214 := by exact prefixLift 625214
  have htrace : WordTrace (prefixWord ++ tailWord_625214) baseStart_625214 baseEnd_625214 := by
    simpa [prefixWord, tailWord_625214, baseEnd_625214] using wordTrace_append hprefix tailTrace_625214
  have hstable : (prefixWord ++ tailWord_625214).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_625214).length < 2 ^ (prefixWord ++ tailWord_625214).sum := by decide
  have hdescent : baseEnd_625214 < baseStart_625214 := by decide
  rcases family_descends (prefixWord ++ tailWord_625214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_625223 : List Nat := [1, 1, 4, 1, 4, 2, 9]
def baseStart_625223 : Nat := 118140960795 + 625223 * 2 ^ 59
def prefixEnd_625223 : Nat := 4983230072969 + 3 ^ 40 * 625223 * 2
def baseEnd_625223 : Nat := 7926911487558334465115

theorem tailTrace_625223 : CollatzResearch.WordTrace tailWord_625223 prefixEnd_625223 7926911487558334465115 := by
  unfold tailWord_625223
  simp only [CollatzResearch.WordTrace]
  refine ⟨22803756213931325432352323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15202504142620883621568215 22803756213931325432352323)
  ·
    refine ⟨34205634320896988148528485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22803756213931325432352323 34205634320896988148528485)
    ·
      refine ⟨6413556435168185277849091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 34205634320896988148528485 6413556435168185277849091)
      ·
        refine ⟨9620334652752277916773637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6413556435168185277849091 9620334652752277916773637)
        ·
          refine ⟨1803812747391052109395057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9620334652752277916773637 1803812747391052109395057)
          ·
            refine ⟨1352859560543289082046293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1803812747391052109395057 1352859560543289082046293)
            ·
              refine ⟨7926911487558334465115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1352859560543289082046293 7926911487558334465115)
              ·
                rfl

theorem cell22_625223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 9].length) (baseStart_625223 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_625223 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_625223 prefixEnd_625223 := by exact prefixLift 625223
  have htrace : WordTrace (prefixWord ++ tailWord_625223) baseStart_625223 baseEnd_625223 := by
    simpa [prefixWord, tailWord_625223, baseEnd_625223] using wordTrace_append hprefix tailTrace_625223
  have hstable : (prefixWord ++ tailWord_625223).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_625223).length < 2 ^ (prefixWord ++ tailWord_625223).sum := by decide
  have hdescent : baseEnd_625223 < baseStart_625223 := by decide
  rcases family_descends (prefixWord ++ tailWord_625223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_625244 : List Nat := [2, 2, 4, 1, 4, 1, 1, 1, 1, 5]
def baseStart_625244 : Nat := 118140960795 + 625244 * 2 ^ 59
def prefixEnd_625244 : Nat := 4983230072969 + 3 ^ 40 * 625244 * 2
def baseEnd_625244 : Nat := 214033798893237975783041

theorem tailTrace_625244 : CollatzResearch.WordTrace tailWord_625244 prefixEnd_625244 214033798893237975783041 := by
  unfold tailWord_625244
  simp only [CollatzResearch.WordTrace]
  refine ⟨11402261073427623009433393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15203014764570164012577857 11402261073427623009433393)
  ·
    refine ⟨8551695805070717257075045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11402261073427623009433393 8551695805070717257075045)
    ·
      refine ⟨1603442963450759485701571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8551695805070717257075045 1603442963450759485701571)
      ·
        refine ⟨2405164445176139228552357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1603442963450759485701571 2405164445176139228552357)
        ·
          refine ⟨450968333470526105353567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2405164445176139228552357 450968333470526105353567)
          ·
            refine ⟨676452500205789158030351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 450968333470526105353567 676452500205789158030351)
            ·
              refine ⟨1014678750308683737045527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 676452500205789158030351 1014678750308683737045527)
              ·
                refine ⟨1522018125463025605568291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1014678750308683737045527 1522018125463025605568291)
                ·
                  refine ⟨2283027188194538408352437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1522018125463025605568291 2283027188194538408352437)
                  ·
                    refine ⟨214033798893237975783041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2283027188194538408352437 214033798893237975783041)
                    ·
                      rfl

theorem cell22_625244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 4, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 4, 1, 1, 1, 1, 5].length) (baseStart_625244 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_625244 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_625244 prefixEnd_625244 := by exact prefixLift 625244
  have htrace : WordTrace (prefixWord ++ tailWord_625244) baseStart_625244 baseEnd_625244 := by
    simpa [prefixWord, tailWord_625244, baseEnd_625244] using wordTrace_append hprefix tailTrace_625244
  have hstable : (prefixWord ++ tailWord_625244).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_625244).length < 2 ^ (prefixWord ++ tailWord_625244).sum := by decide
  have hdescent : baseEnd_625244 < baseStart_625244 := by decide
  rcases family_descends (prefixWord ++ tailWord_625244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_625283 : List Nat := [1, 1, 1, 3, 3, 1, 2, 1, 4, 5]
def baseStart_625283 : Nat := 118140960795 + 625283 * 2 ^ 59
def prefixEnd_625283 : Nat := 4983230072969 + 3 ^ 40 * 625283 * 2
def baseEnd_625283 : Nat := 214047149390254874057921

theorem tailTrace_625283 : CollatzResearch.WordTrace tailWord_625283 prefixEnd_625283 214047149390254874057921 := by
  unfold tailWord_625283
  simp only [CollatzResearch.WordTrace]
  refine ⟨22805944593713955679536503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15203963062475970453024335 22805944593713955679536503)
  ·
    refine ⟨34208916890570933519304755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22805944593713955679536503 34208916890570933519304755)
    ·
      refine ⟨51313375335856400278957133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34208916890570933519304755 51313375335856400278957133)
      ·
        refine ⟨19242515750946150104608925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51313375335856400278957133 19242515750946150104608925)
        ·
          refine ⟨7215943406604806289228347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19242515750946150104608925 7215943406604806289228347)
          ·
            refine ⟨10823915109907209433842521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7215943406604806289228347 10823915109907209433842521)
            ·
              refine ⟨8117936332430407075381891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10823915109907209433842521 8117936332430407075381891)
              ·
                refine ⟨12176904498645610613072837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8117936332430407075381891 12176904498645610613072837)
                ·
                  refine ⟨2283169593496051989951157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12176904498645610613072837 2283169593496051989951157)
                  ·
                    refine ⟨214047149390254874057921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2283169593496051989951157 214047149390254874057921)
                    ·
                      rfl

theorem cell22_625283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 1, 4, 5].length) (baseStart_625283 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_625283 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_625283 prefixEnd_625283 := by exact prefixLift 625283
  have htrace : WordTrace (prefixWord ++ tailWord_625283) baseStart_625283 baseEnd_625283 := by
    simpa [prefixWord, tailWord_625283, baseEnd_625283] using wordTrace_append hprefix tailTrace_625283
  have hstable : (prefixWord ++ tailWord_625283).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_625283).length < 2 ^ (prefixWord ++ tailWord_625283).sum := by decide
  have hdescent : baseEnd_625283 < baseStart_625283 := by decide
  rcases family_descends (prefixWord ++ tailWord_625283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_625315 : List Nat := [1, 1, 1, 4, 1, 1, 2, 6, 1, 4]
def baseStart_625315 : Nat := 118140960795 + 625315 * 2 ^ 59
def prefixEnd_625315 : Nat := 4983230072969 + 3 ^ 40 * 625315 * 2
def baseEnd_625315 : Nat := 214058103644217457257823

theorem tailTrace_625315 : CollatzResearch.WordTrace tailWord_625315 prefixEnd_625315 214058103644217457257823 := by
  unfold tailWord_625315
  simp only [CollatzResearch.WordTrace]
  refine ⟨22807111729598025144701399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15204741153065350096467599 22807111729598025144701399)
  ·
    refine ⟨34210667594397037717052099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22807111729598025144701399 34210667594397037717052099)
    ·
      refine ⟨51316001391595556575578149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34210667594397037717052099 51316001391595556575578149)
      ·
        refine ⟨9621750260924166857920903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 51316001391595556575578149 9621750260924166857920903)
        ·
          refine ⟨14432625391386250286881355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9621750260924166857920903 14432625391386250286881355)
          ·
            refine ⟨21648938087079375430322033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14432625391386250286881355 21648938087079375430322033)
            ·
              refine ⟨16236703565309531572741525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21648938087079375430322033 16236703565309531572741525)
              ·
                refine ⟨761095479623884292472259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 16236703565309531572741525 761095479623884292472259)
                ·
                  refine ⟨1141643219435826438708389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 761095479623884292472259 1141643219435826438708389)
                  ·
                    refine ⟨214058103644217457257823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1141643219435826438708389 214058103644217457257823)
                    ·
                      rfl

theorem cell22_625315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 6, 1, 4].length) (baseStart_625315 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_625315 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_625315 prefixEnd_625315 := by exact prefixLift 625315
  have htrace : WordTrace (prefixWord ++ tailWord_625315) baseStart_625315 baseEnd_625315 := by
    simpa [prefixWord, tailWord_625315, baseEnd_625315] using wordTrace_append hprefix tailTrace_625315
  have hstable : (prefixWord ++ tailWord_625315).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_625315).length < 2 ^ (prefixWord ++ tailWord_625315).sum := by decide
  have hdescent : baseEnd_625315 < baseStart_625315 := by decide
  rcases family_descends (prefixWord ++ tailWord_625315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_625377 : List Nat := [1, 2, 3, 1, 4, 1, 3, 1, 2, 4]
def baseStart_625377 : Nat := 118140960795 + 625377 * 2 ^ 59
def prefixEnd_625377 : Nat := 4983230072969 + 3 ^ 40 * 625377 * 2
def baseEnd_625377 : Nat := 214079327511269962207633

theorem tailTrace_625377 : CollatzResearch.WordTrace tailWord_625377 prefixEnd_625377 214079327511269962207633 := by
  unfold tailWord_625377
  simp only [CollatzResearch.WordTrace]
  refine ⟨22809373055373409733458385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15206248703582273155638923 22809373055373409733458385)
  ·
    refine ⟨17107029791530057300093789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22809373055373409733458385 17107029791530057300093789)
    ·
      refine ⟨6415136171823771487535171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17107029791530057300093789 6415136171823771487535171)
      ·
        refine ⟨9622704257735657231302757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6415136171823771487535171 9622704257735657231302757)
        ·
          refine ⟨1804257048325435730869267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9622704257735657231302757 1804257048325435730869267)
          ·
            refine ⟨2706385572488153596303901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1804257048325435730869267 2706385572488153596303901)
            ·
              refine ⟨1014894589683057598613963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2706385572488153596303901 1014894589683057598613963)
              ·
                refine ⟨1522341884524586397920945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1014894589683057598613963 1522341884524586397920945)
                ·
                  refine ⟨1141756413393439798440709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1522341884524586397920945 1141756413393439798440709)
                  ·
                    refine ⟨214079327511269962207633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1141756413393439798440709 214079327511269962207633)
                    ·
                      rfl

theorem cell22_625377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 3, 1, 2, 4].length) (baseStart_625377 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_625377 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_625377 prefixEnd_625377 := by exact prefixLift 625377
  have htrace : WordTrace (prefixWord ++ tailWord_625377) baseStart_625377 baseEnd_625377 := by
    simpa [prefixWord, tailWord_625377, baseEnd_625377] using wordTrace_append hprefix tailTrace_625377
  have hstable : (prefixWord ++ tailWord_625377).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_625377).length < 2 ^ (prefixWord ++ tailWord_625377).sum := by decide
  have hdescent : baseEnd_625377 < baseStart_625377 := by decide
  rcases family_descends (prefixWord ++ tailWord_625377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_625426 : List Nat := [3, 2, 4, 1, 2, 2, 2, 6]
def baseStart_625426 : Nat := 118140960795 + 625426 * 2 ^ 59
def prefixEnd_625426 : Nat := 4983230072969 + 3 ^ 40 * 625426 * 2
def baseEnd_625426 : Nat := 23788455690294463081387

theorem tailTrace_625426 : CollatzResearch.WordTrace tailWord_625426 prefixEnd_625426 23788455690294463081387 := by
  unfold tailWord_625426
  simp only [CollatzResearch.WordTrace]
  refine ⟨5702790058048972775498033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15207440154797260734661421 5702790058048972775498033)
  ·
    refine ⟨4277092543536729581623525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5702790058048972775498033 4277092543536729581623525)
    ·
      refine ⟨801954851913136796554411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4277092543536729581623525 801954851913136796554411)
      ·
        refine ⟨1202932277869705194831617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 801954851913136796554411 1202932277869705194831617)
        ·
          refine ⟨902199208402278896123713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1202932277869705194831617 902199208402278896123713)
          ·
            refine ⟨676649406301709172092785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 902199208402278896123713 676649406301709172092785)
            ·
              refine ⟨507487054726281879069589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 676649406301709172092785 507487054726281879069589)
              ·
                refine ⟨23788455690294463081387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 507487054726281879069589 23788455690294463081387)
                ·
                  rfl

theorem cell22_625426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 2, 2, 6].length) (baseStart_625426 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_625426 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_625426 prefixEnd_625426 := by exact prefixLift 625426
  have htrace : WordTrace (prefixWord ++ tailWord_625426) baseStart_625426 baseEnd_625426 := by
    simpa [prefixWord, tailWord_625426, baseEnd_625426] using wordTrace_append hprefix tailTrace_625426
  have hstable : (prefixWord ++ tailWord_625426).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_625426).length < 2 ^ (prefixWord ++ tailWord_625426).sum := by decide
  have hdescent : baseEnd_625426 < baseStart_625426 := by decide
  rcases family_descends (prefixWord ++ tailWord_625426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_625484 : List Nat := [2, 2, 1, 3, 3, 1, 3, 2, 1, 4]
def baseStart_625484 : Nat := 118140960795 + 625484 * 2 ^ 59
def prefixEnd_625484 : Nat := 4983230072969 + 3 ^ 40 * 625484 * 2
def baseEnd_625484 : Nat := 214115955797957349782305

theorem tailTrace_625484 : CollatzResearch.WordTrace tailWord_625484 prefixEnd_625484 214115955797957349782305 := by
  unfold tailWord_625484
  simp only [CollatzResearch.WordTrace]
  refine ⟨11406637832992883503801753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15208850443990511338402337 11406637832992883503801753)
  ·
    refine ⟨8554978374744662627851315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11406637832992883503801753 8554978374744662627851315)
    ·
      refine ⟨12832467562116993941776973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8554978374744662627851315 12832467562116993941776973)
      ·
        refine ⟨4812175335793872728166365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12832467562116993941776973 4812175335793872728166365)
        ·
          refine ⟨1804565750922702273062387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4812175335793872728166365 1804565750922702273062387)
          ·
            refine ⟨2706848626384053409593581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1804565750922702273062387 2706848626384053409593581)
            ·
              refine ⟨1015068234894020028597593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2706848626384053409593581 1015068234894020028597593)
              ·
                refine ⟨761301176170515021448195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1015068234894020028597593 761301176170515021448195)
                ·
                  refine ⟨1141951764255772532172293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 761301176170515021448195 1141951764255772532172293)
                  ·
                    refine ⟨214115955797957349782305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1141951764255772532172293 214115955797957349782305)
                    ·
                      rfl

theorem cell22_625484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 3, 2, 1, 4].length) (baseStart_625484 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_625484 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_625484 prefixEnd_625484 := by exact prefixLift 625484
  have htrace : WordTrace (prefixWord ++ tailWord_625484) baseStart_625484 baseEnd_625484 := by
    simpa [prefixWord, tailWord_625484, baseEnd_625484] using wordTrace_append hprefix tailTrace_625484
  have hstable : (prefixWord ++ tailWord_625484).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_625484).length < 2 ^ (prefixWord ++ tailWord_625484).sum := by decide
  have hdescent : baseEnd_625484 < baseStart_625484 := by decide
  rcases family_descends (prefixWord ++ tailWord_625484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_625497 : List Nat := [1, 2, 1, 2, 2, 5, 1, 2, 1, 5]
def baseStart_625497 : Nat := 118140960795 + 625497 * 2 ^ 59
def prefixEnd_625497 : Nat := 4983230072969 + 3 ^ 40 * 625497 * 2
def baseEnd_625497 : Nat := 214120405963629649207265

theorem tailTrace_625497 : CollatzResearch.WordTrace tailWord_625497 prefixEnd_625497 214120405963629649207265 := by
  unfold tailWord_625497
  simp only [CollatzResearch.WordTrace]
  refine ⟨22813749814938670227826745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15209166543292446818551163 22813749814938670227826745)
  ·
    refine ⟨17110312361204002670870059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22813749814938670227826745 17110312361204002670870059)
    ·
      refine ⟨25665468541806004006305089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17110312361204002670870059 25665468541806004006305089)
      ·
        refine ⟨19249101406354503004728817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25665468541806004006305089 19249101406354503004728817)
        ·
          refine ⟨14436826054765877253546613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19249101406354503004728817 14436826054765877253546613)
          ·
            refine ⟨1353452442634300992519995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 14436826054765877253546613 1353452442634300992519995)
            ·
              refine ⟨2030178663951451488779993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1353452442634300992519995 2030178663951451488779993)
              ·
                refine ⟨1522633997963588616584995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2030178663951451488779993 1522633997963588616584995)
                ·
                  refine ⟨2283950996945382924877493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1522633997963588616584995 2283950996945382924877493)
                  ·
                    refine ⟨214120405963629649207265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2283950996945382924877493 214120405963629649207265)
                    ·
                      rfl

theorem cell22_625497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 1, 2, 1, 5].length) (baseStart_625497 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_625497 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_625497 prefixEnd_625497 := by exact prefixLift 625497
  have htrace : WordTrace (prefixWord ++ tailWord_625497) baseStart_625497 baseEnd_625497 := by
    simpa [prefixWord, tailWord_625497, baseEnd_625497] using wordTrace_append hprefix tailTrace_625497
  have hstable : (prefixWord ++ tailWord_625497).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_625497).length < 2 ^ (prefixWord ++ tailWord_625497).sum := by decide
  have hdescent : baseEnd_625497 < baseStart_625497 := by decide
  rcases family_descends (prefixWord ++ tailWord_625497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_625544 : List Nat := [2, 1, 3, 3, 2, 2, 3, 6]
def baseStart_625544 : Nat := 118140960795 + 625544 * 2 ^ 59
def prefixEnd_625544 : Nat := 4983230072969 + 3 ^ 40 * 625544 * 2
def baseEnd_625544 : Nat := 23792943891570799253569

theorem tailTrace_625544 : CollatzResearch.WordTrace tailWord_625544 prefixEnd_625544 23792943891570799253569 := by
  unfold tailWord_625544
  simp only [CollatzResearch.WordTrace]
  refine ⟨11407732022884198627393843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15210309363845598169858457 11407732022884198627393843)
  ·
    refine ⟨17111598034326297941090765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11407732022884198627393843 17111598034326297941090765)
    ·
      refine ⟨6416849262872361727909037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17111598034326297941090765 6416849262872361727909037)
      ·
        refine ⟨2406318473577135647965889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6416849262872361727909037 2406318473577135647965889)
        ·
          refine ⟨1804738855182851735974417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2406318473577135647965889 1804738855182851735974417)
          ·
            refine ⟨1353554141387138801980813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1804738855182851735974417 1353554141387138801980813)
            ·
              refine ⟨507582803020177050742805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1353554141387138801980813 507582803020177050742805)
              ·
                refine ⟨23792943891570799253569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 507582803020177050742805 23792943891570799253569)
                ·
                  rfl

theorem cell22_625544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 3, 6].length) (baseStart_625544 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_625544 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_625544 prefixEnd_625544 := by exact prefixLift 625544
  have htrace : WordTrace (prefixWord ++ tailWord_625544) baseStart_625544 baseEnd_625544 := by
    simpa [prefixWord, tailWord_625544, baseEnd_625544] using wordTrace_append hprefix tailTrace_625544
  have hstable : (prefixWord ++ tailWord_625544).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_625544).length < 2 ^ (prefixWord ++ tailWord_625544).sum := by decide
  have hdescent : baseEnd_625544 < baseStart_625544 := by decide
  rcases family_descends (prefixWord ++ tailWord_625544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_625546 : List Nat := [3, 1, 2, 4, 1, 3, 1, 1, 2, 4]
def baseStart_625546 : Nat := 118140960795 + 625546 * 2 ^ 59
def prefixEnd_625546 : Nat := 4983230072969 + 3 ^ 40 * 625546 * 2
def baseEnd_625546 : Nat := 214137179665009854732115

theorem tailTrace_625546 : CollatzResearch.WordTrace tailWord_625546 prefixEnd_625546 214137179665009854732115 := by
  unfold tailWord_625546
  simp only [CollatzResearch.WordTrace]
  refine ⟨5703884247940287899090123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15210357994507434397573661 5703884247940287899090123)
  ·
    refine ⟨8555826371910431848635185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5703884247940287899090123 8555826371910431848635185)
    ·
      refine ⟨6416869778932823886476389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8555826371910431848635185 6416869778932823886476389)
      ·
        refine ⟨1203163083549904478714323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6416869778932823886476389 1203163083549904478714323)
        ·
          refine ⟨1804744625324856718071485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1203163083549904478714323 1804744625324856718071485)
          ·
            refine ⟨676779234496821269276807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1804744625324856718071485 676779234496821269276807)
            ·
              refine ⟨1015168851745231903915211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 676779234496821269276807 1015168851745231903915211)
              ·
                refine ⟨1522753277617847855872817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1015168851745231903915211 1522753277617847855872817)
                ·
                  refine ⟨1142064958213385891904613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1522753277617847855872817 1142064958213385891904613)
                  ·
                    refine ⟨214137179665009854732115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1142064958213385891904613 214137179665009854732115)
                    ·
                      rfl

theorem cell22_625546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 3, 1, 1, 2, 4].length) (baseStart_625546 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_625546 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_625546 prefixEnd_625546 := by exact prefixLift 625546
  have htrace : WordTrace (prefixWord ++ tailWord_625546) baseStart_625546 baseEnd_625546 := by
    simpa [prefixWord, tailWord_625546, baseEnd_625546] using wordTrace_append hprefix tailTrace_625546
  have hstable : (prefixWord ++ tailWord_625546).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_625546).length < 2 ^ (prefixWord ++ tailWord_625546).sum := by decide
  have hdescent : baseEnd_625546 < baseStart_625546 := by decide
  rcases family_descends (prefixWord ++ tailWord_625546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_625572 : List Nat := [2, 3, 1, 2, 1, 2, 3, 1, 7]
def baseStart_625572 : Nat := 118140960795 + 625572 * 2 ^ 59
def prefixEnd_625572 : Nat := 4983230072969 + 3 ^ 40 * 625572 * 2
def baseEnd_625572 : Nat := 71382026665451484527345

theorem tailTrace_625572 : CollatzResearch.WordTrace tailWord_625572 prefixEnd_625572 71382026665451484527345 := by
  unfold tailWord_625572
  simp only [CollatzResearch.WordTrace]
  refine ⟨11408242644833479018403485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15210990193111305357871313 11408242644833479018403485)
  ·
    refine ⟨4278090991812554631901307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11408242644833479018403485 4278090991812554631901307)
    ·
      refine ⟨6417136487718831947851961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4278090991812554631901307 6417136487718831947851961)
      ·
        refine ⟨4812852365789123960888971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6417136487718831947851961 4812852365789123960888971)
        ·
          refine ⟨7219278548683685941333457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4812852365789123960888971 7219278548683685941333457)
          ·
            refine ⟨5414458911512764456000093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7219278548683685941333457 5414458911512764456000093)
            ·
              refine ⟨2030422091817286671000035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5414458911512764456000093 2030422091817286671000035)
              ·
                refine ⟨3045633137725930006500053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2030422091817286671000035 3045633137725930006500053)
                ·
                  refine ⟨71382026665451484527345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3045633137725930006500053 71382026665451484527345)
                  ·
                    rfl

theorem cell22_625572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 3, 1, 7].length) (baseStart_625572 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_625572 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_625572 prefixEnd_625572 := by exact prefixLift 625572
  have htrace : WordTrace (prefixWord ++ tailWord_625572) baseStart_625572 baseEnd_625572 := by
    simpa [prefixWord, tailWord_625572, baseEnd_625572] using wordTrace_append hprefix tailTrace_625572
  have hstable : (prefixWord ++ tailWord_625572).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_625572).length < 2 ^ (prefixWord ++ tailWord_625572).sum := by decide
  have hdescent : baseEnd_625572 < baseStart_625572 := by decide
  rcases family_descends (prefixWord ++ tailWord_625572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_625653 : List Nat := [1, 3, 5, 2, 1, 1, 1, 1, 3, 4]
def baseStart_625653 : Nat := 118140960795 + 625653 * 2 ^ 59
def prefixEnd_625653 : Nat := 4983230072969 + 3 ^ 40 * 625653 * 2
def baseEnd_625653 : Nat := 214173807951697242306787

theorem tailTrace_625653 : CollatzResearch.WordTrace tailWord_625653 prefixEnd_625653 214173807951697242306787 := by
  unfold tailWord_625653
  simp only [CollatzResearch.WordTrace]
  refine ⟨22819439602373508870505613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15212959734915672580337075 22819439602373508870505613)
  ·
    refine ⟨8557289850890065826439605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22819439602373508870505613 8557289850890065826439605)
    ·
      refine ⟨802245923520943671228713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 8557289850890065826439605 802245923520943671228713)
      ·
        refine ⟨601684442640707753421535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 802245923520943671228713 601684442640707753421535)
        ·
          refine ⟨902526663961061630132303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 601684442640707753421535 902526663961061630132303)
          ·
            refine ⟨1353789995941592445198455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 902526663961061630132303 1353789995941592445198455)
            ·
              refine ⟨2030684993912388667797683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1353789995941592445198455 2030684993912388667797683)
              ·
                refine ⟨3046027490868583001696525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2030684993912388667797683 3046027490868583001696525)
                ·
                  refine ⟨1142260309075718625636197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3046027490868583001696525 1142260309075718625636197)
                  ·
                    refine ⟨214173807951697242306787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1142260309075718625636197 214173807951697242306787)
                    ·
                      rfl

theorem cell22_625653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 1, 1, 3, 4].length) (baseStart_625653 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_625653 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_625653 prefixEnd_625653 := by exact prefixLift 625653
  have htrace : WordTrace (prefixWord ++ tailWord_625653) baseStart_625653 baseEnd_625653 := by
    simpa [prefixWord, tailWord_625653, baseEnd_625653] using wordTrace_append hprefix tailTrace_625653
  have hstable : (prefixWord ++ tailWord_625653).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_625653).length < 2 ^ (prefixWord ++ tailWord_625653).sum := by decide
  have hdescent : baseEnd_625653 < baseStart_625653 := by decide
  rcases family_descends (prefixWord ++ tailWord_625653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_625728 : List Nat := [2, 1, 1, 2, 2, 3, 4, 3, 1, 3]
def baseStart_625728 : Nat := 118140960795 + 625728 * 2 ^ 59
def prefixEnd_625728 : Nat := 4983230072969 + 3 ^ 40 * 625728 * 2
def baseEnd_625728 : Nat := 214199481984422046681557

theorem tailTrace_625728 : CollatzResearch.WordTrace tailWord_625728 prefixEnd_625728 214199481984422046681557 := by
  unfold tailWord_625728
  simp only [CollatzResearch.WordTrace]
  refine ⟨11411087538550898339742919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15214783384734531119657225 11411087538550898339742919)
  ·
    refine ⟨17116631307826347509614379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11411087538550898339742919 17116631307826347509614379)
    ·
      refine ⟨25674946961739521264421569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17116631307826347509614379 25674946961739521264421569)
      ·
        refine ⟨19256210221304640948316177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25674946961739521264421569 19256210221304640948316177)
        ·
          refine ⟨14442157665978480711237133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19256210221304640948316177 14442157665978480711237133)
          ·
            refine ⟨5415809124741930266713925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14442157665978480711237133 5415809124741930266713925)
            ·
              refine ⟨1015464210889111925008861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5415809124741930266713925 1015464210889111925008861)
              ·
                refine ⟨380799079083416971878323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1015464210889111925008861 380799079083416971878323)
                ·
                  refine ⟨571198618625125457817485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 380799079083416971878323 571198618625125457817485)
                  ·
                    refine ⟨214199481984422046681557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 571198618625125457817485 214199481984422046681557)
                    ·
                      rfl

theorem cell22_625728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 4, 3, 1, 3].length) (baseStart_625728 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_625728 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_625728 prefixEnd_625728 := by exact prefixLift 625728
  have htrace : WordTrace (prefixWord ++ tailWord_625728) baseStart_625728 baseEnd_625728 := by
    simpa [prefixWord, tailWord_625728, baseEnd_625728] using wordTrace_append hprefix tailTrace_625728
  have hstable : (prefixWord ++ tailWord_625728).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_625728).length < 2 ^ (prefixWord ++ tailWord_625728).sum := by decide
  have hdescent : baseEnd_625728 < baseStart_625728 := by decide
  rcases family_descends (prefixWord ++ tailWord_625728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_625741 : List Nat := [1, 6, 1, 1, 1, 3, 1, 1, 7]
def baseStart_625741 : Nat := 118140960795 + 625741 * 2 ^ 59
def prefixEnd_625741 : Nat := 4983230072969 + 3 ^ 40 * 625741 * 2
def baseEnd_625741 : Nat := 71401310716698115368839

theorem tailTrace_625741 : CollatzResearch.WordTrace tailWord_625741 prefixEnd_625741 71401310716698115368839 := by
  unfold tailWord_625741
  simp only [CollatzResearch.WordTrace]
  refine ⟨22822649226054699899709077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15215099484036466599806051 22822649226054699899709077)
  ·
    refine ⟨1069811682471314057798863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 22822649226054699899709077 1069811682471314057798863)
    ·
      refine ⟨1604717523706971086698295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1069811682471314057798863 1604717523706971086698295)
      ·
        refine ⟨2407076285560456630047443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1604717523706971086698295 2407076285560456630047443)
        ·
          refine ⟨3610614428340684945071165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2407076285560456630047443 3610614428340684945071165)
          ·
            refine ⟨1353980410627756854401687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3610614428340684945071165 1353980410627756854401687)
            ·
              refine ⟨2030970615941635281602531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1353980410627756854401687 2030970615941635281602531)
              ·
                refine ⟨3046455923912452922403797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2030970615941635281602531 3046455923912452922403797)
                ·
                  refine ⟨71401310716698115368839, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3046455923912452922403797 71401310716698115368839)
                  ·
                    rfl

theorem cell22_625741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 1, 1, 7].length) (baseStart_625741 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_625741 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_625741 prefixEnd_625741 := by exact prefixLift 625741
  have htrace : WordTrace (prefixWord ++ tailWord_625741) baseStart_625741 baseEnd_625741 := by
    simpa [prefixWord, tailWord_625741, baseEnd_625741] using wordTrace_append hprefix tailTrace_625741
  have hstable : (prefixWord ++ tailWord_625741).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_625741).length < 2 ^ (prefixWord ++ tailWord_625741).sum := by decide
  have hdescent : baseEnd_625741 < baseStart_625741 := by decide
  rcases family_descends (prefixWord ++ tailWord_625741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_625754 : List Nat := [3, 1, 1, 2, 1, 1, 2, 4, 3, 4]
def baseStart_625754 : Nat := 118140960795 + 625754 * 2 ^ 59
def prefixEnd_625754 : Nat := 4983230072969 + 3 ^ 40 * 625754 * 2
def baseEnd_625754 : Nat := 214208382315766645531477

theorem tailTrace_625754 : CollatzResearch.WordTrace tailWord_625754 prefixEnd_625754 214208382315766645531477 := by
  unfold tailWord_625754
  simp only [CollatzResearch.WordTrace]
  refine ⟨5705780843751900779983079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15215415583338402079954877 5705780843751900779983079)
  ·
    refine ⟨8558671265627851169974619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5705780843751900779983079 8558671265627851169974619)
    ·
      refine ⟨12838006898441776754961929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8558671265627851169974619 12838006898441776754961929)
      ·
        refine ⟨9628505173831332566221447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12838006898441776754961929 9628505173831332566221447)
        ·
          refine ⟨14442757760746998849332171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9628505173831332566221447 14442757760746998849332171)
          ·
            refine ⟨21664136641120498273998257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14442757760746998849332171 21664136641120498273998257)
            ·
              refine ⟨16248102480840373705498693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21664136641120498273998257 16248102480840373705498693)
              ·
                refine ⟨3046519215157570069781005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16248102480840373705498693 3046519215157570069781005)
                ·
                  refine ⟨1142444705684088776167877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3046519215157570069781005 1142444705684088776167877)
                  ·
                    refine ⟨214208382315766645531477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1142444705684088776167877 214208382315766645531477)
                    ·
                      rfl

theorem cell22_625754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 4, 3, 4].length) (baseStart_625754 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_625754 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_625754 prefixEnd_625754 := by exact prefixLift 625754
  have htrace : WordTrace (prefixWord ++ tailWord_625754) baseStart_625754 baseEnd_625754 := by
    simpa [prefixWord, tailWord_625754, baseEnd_625754] using wordTrace_append hprefix tailTrace_625754
  have hstable : (prefixWord ++ tailWord_625754).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_625754).length < 2 ^ (prefixWord ++ tailWord_625754).sum := by decide
  have hdescent : baseEnd_625754 < baseStart_625754 := by decide
  rcases family_descends (prefixWord ++ tailWord_625754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_625769 : List Nat := [1, 2, 1, 1, 1, 6, 2, 2, 6]
def baseStart_625769 : Nat := 118140960795 + 625769 * 2 ^ 59
def prefixEnd_625769 : Nat := 4983230072969 + 3 ^ 40 * 625769 * 2
def baseEnd_625769 : Nat := 71404505707437202135477

theorem tailTrace_625769 : CollatzResearch.WordTrace tailWord_625769 prefixEnd_625769 71404505707437202135477 := by
  unfold tailWord_625769
  simp only [CollatzResearch.WordTrace]
  refine ⟨22823670469953260681728361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15215780313302173787818907 22823670469953260681728361)
  ·
    refine ⟨17117752852464945511296271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22823670469953260681728361 17117752852464945511296271)
    ·
      refine ⟨25676629278697418266944407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17117752852464945511296271 25676629278697418266944407)
      ·
        refine ⟨38514943918046127400416611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25676629278697418266944407 38514943918046127400416611)
        ·
          refine ⟨57772415877069191100624917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38514943918046127400416611 57772415877069191100624917)
          ·
            refine ⟨2708081994237618332841793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 57772415877069191100624917 2708081994237618332841793)
            ·
              refine ⟨2031061495678213749631345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2708081994237618332841793 2031061495678213749631345)
              ·
                refine ⟨1523296121758660312223509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2031061495678213749631345 1523296121758660312223509)
                ·
                  refine ⟨71404505707437202135477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1523296121758660312223509 71404505707437202135477)
                  ·
                    rfl

theorem cell22_625769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 2, 2, 6].length) (baseStart_625769 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_625769 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_625769 prefixEnd_625769 := by exact prefixLift 625769
  have htrace : WordTrace (prefixWord ++ tailWord_625769) baseStart_625769 baseEnd_625769 := by
    simpa [prefixWord, tailWord_625769, baseEnd_625769] using wordTrace_append hprefix tailTrace_625769
  have hstable : (prefixWord ++ tailWord_625769).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_625769).length < 2 ^ (prefixWord ++ tailWord_625769).sum := by decide
  have hdescent : baseEnd_625769 < baseStart_625769 := by decide
  rcases family_descends (prefixWord ++ tailWord_625769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_625784 : List Nat := [2, 1, 2, 1, 1, 1, 4, 4, 1, 5]
def baseStart_625784 : Nat := 118140960795 + 625784 * 2 ^ 59
def prefixEnd_625784 : Nat := 4983230072969 + 3 ^ 40 * 625784 * 2
def baseEnd_625784 : Nat := 214218651928856567281385

theorem tailTrace_625784 : CollatzResearch.WordTrace tailWord_625784 prefixEnd_625784 214218651928856567281385 := by
  unfold tailWord_625784
  simp only [CollatzResearch.WordTrace]
  refine ⟨11412108782449459121762203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15216145043265945495682937 11412108782449459121762203)
  ·
    refine ⟨17118163173674188682643305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11412108782449459121762203 17118163173674188682643305)
    ·
      refine ⟨12838622380255641511982479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17118163173674188682643305 12838622380255641511982479)
      ·
        refine ⟨19257933570383462267973719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12838622380255641511982479 19257933570383462267973719)
        ·
          refine ⟨28886900355575193401960579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19257933570383462267973719 28886900355575193401960579)
          ·
            refine ⟨43330350533362790102940869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28886900355575193401960579 43330350533362790102940869)
            ·
              refine ⟨8124440725005523144301413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 43330350533362790102940869 8124440725005523144301413)
              ·
                refine ⟨1523332635938535589556515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8124440725005523144301413 1523332635938535589556515)
                ·
                  refine ⟨2284998953907803384334773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1523332635938535589556515 2284998953907803384334773)
                  ·
                    refine ⟨214218651928856567281385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2284998953907803384334773 214218651928856567281385)
                    ·
                      rfl

theorem cell22_625784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 4, 1, 5].length) (baseStart_625784 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_625784 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_625784 prefixEnd_625784 := by exact prefixLift 625784
  have htrace : WordTrace (prefixWord ++ tailWord_625784) baseStart_625784 baseEnd_625784 := by
    simpa [prefixWord, tailWord_625784, baseEnd_625784] using wordTrace_append hprefix tailTrace_625784
  have hstable : (prefixWord ++ tailWord_625784).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_625784).length < 2 ^ (prefixWord ++ tailWord_625784).sum := by decide
  have hdescent : baseEnd_625784 < baseStart_625784 := by decide
  rcases family_descends (prefixWord ++ tailWord_625784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_625801 : List Nat := [1, 2, 1, 1, 4, 3, 2, 1, 4, 3]
def baseStart_625801 : Nat := 118140960795 + 625801 * 2 ^ 59
def prefixEnd_625801 : Nat := 4983230072969 + 3 ^ 40 * 625801 * 2
def baseEnd_625801 : Nat := 214224471376274189606333

theorem tailTrace_625801 : CollatzResearch.WordTrace tailWord_625801 prefixEnd_625801 214224471376274189606333 := by
  unfold tailWord_625801
  simp only [CollatzResearch.WordTrace]
  refine ⟨22824837605837330146893257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15216558403891553431262171 22824837605837330146893257)
  ·
    refine ⟨17118628204377997610169943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22824837605837330146893257 17118628204377997610169943)
    ·
      refine ⟨25677942306566996415254915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17118628204377997610169943 25677942306566996415254915)
      ·
        refine ⟨38516913459850494622882373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25677942306566996415254915 38516913459850494622882373)
        ·
          refine ⟨7221921273721967741790445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 38516913459850494622882373 7221921273721967741790445)
          ·
            refine ⟨2708220477645737903171417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7221921273721967741790445 2708220477645737903171417)
            ·
              refine ⟨2031165358234303427378563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2708220477645737903171417 2031165358234303427378563)
              ·
                refine ⟨3046748037351455141067845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2031165358234303427378563 3046748037351455141067845)
                ·
                  refine ⟨571265257003397838950221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3046748037351455141067845 571265257003397838950221)
                  ·
                    refine ⟨214224471376274189606333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 571265257003397838950221 214224471376274189606333)
                    ·
                      rfl

theorem cell22_625801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 2, 1, 4, 3].length) (baseStart_625801 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_625801 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_625801 prefixEnd_625801 := by exact prefixLift 625801
  have htrace : WordTrace (prefixWord ++ tailWord_625801) baseStart_625801 baseEnd_625801 := by
    simpa [prefixWord, tailWord_625801, baseEnd_625801] using wordTrace_append hprefix tailTrace_625801
  have hstable : (prefixWord ++ tailWord_625801).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_625801).length < 2 ^ (prefixWord ++ tailWord_625801).sum := by decide
  have hdescent : baseEnd_625801 < baseStart_625801 := by decide
  rcases family_descends (prefixWord ++ tailWord_625801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_625831 : List Nat := [1, 1, 6, 2, 1, 1, 2, 8]
def baseStart_625831 : Nat := 118140960795 + 625831 * 2 ^ 59
def prefixEnd_625831 : Nat := 4983230072969 + 3 ^ 40 * 625831 * 2
def baseEnd_625831 : Nat := 23803860109929345706249

theorem tailTrace_625831 : CollatzResearch.WordTrace tailWord_625831 prefixEnd_625831 23803860109929345706249 := by
  unfold tailWord_625831
  simp only [CollatzResearch.WordTrace]
  refine ⟨22825931795728645270485347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15217287863819096846990231 22825931795728645270485347)
  ·
    refine ⟨34238897693592967905728021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22825931795728645270485347 34238897693592967905728021)
    ·
      refine ⟨1604948329387170370581001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 34238897693592967905728021 1604948329387170370581001)
      ·
        refine ⟨1203711247040377777935751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1604948329387170370581001 1203711247040377777935751)
        ·
          refine ⟨1805566870560566666903627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1203711247040377777935751 1805566870560566666903627)
          ·
            refine ⟨2708350305840850000355441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1805566870560566666903627 2708350305840850000355441)
            ·
              refine ⟨2031262729380637500266581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2708350305840850000355441 2031262729380637500266581)
              ·
                refine ⟨23803860109929345706249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2031262729380637500266581 23803860109929345706249)
                ·
                  rfl

theorem cell22_625831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 2, 8].length) (baseStart_625831 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_625831 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_625831 prefixEnd_625831 := by exact prefixLift 625831
  have htrace : WordTrace (prefixWord ++ tailWord_625831) baseStart_625831 baseEnd_625831 := by
    simpa [prefixWord, tailWord_625831, baseEnd_625831] using wordTrace_append hprefix tailTrace_625831
  have hstable : (prefixWord ++ tailWord_625831).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_625831).length < 2 ^ (prefixWord ++ tailWord_625831).sum := by decide
  have hdescent : baseEnd_625831 < baseStart_625831 := by decide
  rcases family_descends (prefixWord ++ tailWord_625831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_625921 : List Nat := [1, 2, 4, 1, 1, 3, 1, 3, 6]
def baseStart_625921 : Nat := 118140960795 + 625921 * 2 ^ 59
def prefixEnd_625921 : Nat := 4983230072969 + 3 ^ 40 * 625921 * 2
def baseEnd_625921 : Nat := 71421849942877958868655

theorem tailTrace_625921 : CollatzResearch.WordTrace tailWord_625921 prefixEnd_625921 71421849942877958868655 := by
  unfold tailWord_625921
  simp only [CollatzResearch.WordTrace]
  refine ⟨22829214365402590641261617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15219476243601727094174411 22829214365402590641261617)
  ·
    refine ⟨17121910774051942980946213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22829214365402590641261617 17121910774051942980946213)
    ·
      refine ⟨3210358270134739308927415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17121910774051942980946213 3210358270134739308927415)
      ·
        refine ⟨4815537405202108963391123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3210358270134739308927415 4815537405202108963391123)
        ·
          refine ⟨7223306107803163445086685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4815537405202108963391123 7223306107803163445086685)
          ·
            refine ⟨2708739790426186291907507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7223306107803163445086685 2708739790426186291907507)
            ·
              refine ⟨4063109685639279437861261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2708739790426186291907507 4063109685639279437861261)
              ·
                refine ⟨1523666132114729789197973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4063109685639279437861261 1523666132114729789197973)
                ·
                  refine ⟨71421849942877958868655, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1523666132114729789197973 71421849942877958868655)
                  ·
                    rfl

theorem cell22_625921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 1, 3, 6].length) (baseStart_625921 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_625921 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_625921 prefixEnd_625921 := by exact prefixLift 625921
  have htrace : WordTrace (prefixWord ++ tailWord_625921) baseStart_625921 baseEnd_625921 := by
    simpa [prefixWord, tailWord_625921, baseEnd_625921] using wordTrace_append hprefix tailTrace_625921
  have hstable : (prefixWord ++ tailWord_625921).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_625921).length < 2 ^ (prefixWord ++ tailWord_625921).sum := by decide
  have hdescent : baseEnd_625921 < baseStart_625921 := by decide
  rcases family_descends (prefixWord ++ tailWord_625921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_625955 : List Nat := [1, 1, 1, 4, 2, 5, 1, 3, 4]
def baseStart_625955 : Nat := 118140960795 + 625955 * 2 ^ 59
def prefixEnd_625955 : Nat := 4983230072969 + 3 ^ 40 * 625955 * 2
def baseEnd_625955 : Nat := 71425729574489707085287

theorem tailTrace_625955 : CollatzResearch.WordTrace tailWord_625955 prefixEnd_625955 71425729574489707085287 := by
  unfold tailWord_625955
  simp only [CollatzResearch.WordTrace]
  refine ⟨22830454447279414447999319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15220302964852942965332879 22830454447279414447999319)
  ·
    refine ⟨34245681670919121671998979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22830454447279414447999319 34245681670919121671998979)
    ·
      refine ⟨51368522506378682507998469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34245681670919121671998979 51368522506378682507998469)
      ·
        refine ⟨9631597969946002970249713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 51368522506378682507998469 9631597969946002970249713)
        ·
          refine ⟨7223698477459502227687285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9631597969946002970249713 7223698477459502227687285)
          ·
            refine ⟨677221732261828333845683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 7223698477459502227687285 677221732261828333845683)
            ·
              refine ⟨1015832598392742500768525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 677221732261828333845683 1015832598392742500768525)
              ·
                refine ⟨380937224397278437788197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1015832598392742500768525 380937224397278437788197)
                ·
                  refine ⟨71425729574489707085287, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 380937224397278437788197 71425729574489707085287)
                  ·
                    rfl

theorem cell22_625955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 5, 1, 3, 4].length) (baseStart_625955 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_625955 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_625955 prefixEnd_625955 := by exact prefixLift 625955
  have htrace : WordTrace (prefixWord ++ tailWord_625955) baseStart_625955 baseEnd_625955 := by
    simpa [prefixWord, tailWord_625955, baseEnd_625955] using wordTrace_append hprefix tailTrace_625955
  have hstable : (prefixWord ++ tailWord_625955).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_625955).length < 2 ^ (prefixWord ++ tailWord_625955).sum := by decide
  have hdescent : baseEnd_625955 < baseStart_625955 := by decide
  rcases family_descends (prefixWord ++ tailWord_625955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_625972 : List Nat := [2, 5, 1, 1, 1, 1, 5, 2, 4]
def baseStart_625972 : Nat := 118140960795 + 625972 * 2 ^ 59
def prefixEnd_625972 : Nat := 4983230072969 + 3 ^ 40 * 625972 * 2
def baseEnd_625972 : Nat := 71427669390295581193603

theorem tailTrace_625972 : CollatzResearch.WordTrace tailWord_625972 prefixEnd_625972 71427669390295581193603 := by
  unfold tailWord_625972
  simp only [CollatzResearch.WordTrace]
  refine ⟨11415537244108913175684085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15220716325478550900912113 11415537244108913175684085)
  ·
    refine ⟨1070206616635210610220383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 11415537244108913175684085 1070206616635210610220383)
    ·
      refine ⟨1605309924952815915330575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1070206616635210610220383 1605309924952815915330575)
      ·
        refine ⟨2407964887429223872995863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1605309924952815915330575 2407964887429223872995863)
        ·
          refine ⟨3611947331143835809493795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2407964887429223872995863 3611947331143835809493795)
          ·
            refine ⟨5417920996715753714240693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3611947331143835809493795 5417920996715753714240693)
            ·
              refine ⟨507930093442101910710065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5417920996715753714240693 507930093442101910710065)
              ·
                refine ⟨380947570081576433032549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 507930093442101910710065 380947570081576433032549)
                ·
                  refine ⟨71427669390295581193603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 380947570081576433032549 71427669390295581193603)
                  ·
                    rfl

theorem cell22_625972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 5, 2, 4].length) (baseStart_625972 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_625972 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_625972 prefixEnd_625972 := by exact prefixLift 625972
  have htrace : WordTrace (prefixWord ++ tailWord_625972) baseStart_625972 baseEnd_625972 := by
    simpa [prefixWord, tailWord_625972, baseEnd_625972] using wordTrace_append hprefix tailTrace_625972
  have hstable : (prefixWord ++ tailWord_625972).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_625972).length < 2 ^ (prefixWord ++ tailWord_625972).sum := by decide
  have hdescent : baseEnd_625972 < baseStart_625972 := by decide
  rcases family_descends (prefixWord ++ tailWord_625972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_625998 : List Nat := [4, 1, 1, 1, 1, 1, 4, 1, 5, 3]
def baseStart_625998 : Nat := 118140960795 + 625998 * 2 ^ 59
def prefixEnd_625998 : Nat := 4983230072969 + 3 ^ 40 * 625998 * 2
def baseEnd_625998 : Nat := 214291908502231342430729

theorem tailTrace_625998 : CollatzResearch.WordTrace tailWord_625998 prefixEnd_625998 214291908502231342430729 := by
  unfold tailWord_625998
  simp only [CollatzResearch.WordTrace]
  refine ⟨2854002848265454098976831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15221348524082421861209765 2854002848265454098976831)
  ·
    refine ⟨4281004272398181148465247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2854002848265454098976831 4281004272398181148465247)
    ·
      refine ⟨6421506408597271722697871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4281004272398181148465247 6421506408597271722697871)
      ·
        refine ⟨9632259612895907584046807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6421506408597271722697871 9632259612895907584046807)
        ·
          refine ⟨14448389419343861376070211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9632259612895907584046807 14448389419343861376070211)
          ·
            refine ⟨21672584129015792064105317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14448389419343861376070211 21672584129015792064105317)
            ·
              refine ⟨4063609524190461012019747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21672584129015792064105317 4063609524190461012019747)
              ·
                refine ⟨6095414286285691518029621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4063609524190461012019747 6095414286285691518029621)
                ·
                  refine ⟨571445089339283579815277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 6095414286285691518029621 571445089339283579815277)
                  ·
                    refine ⟨214291908502231342430729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 571445089339283579815277 214291908502231342430729)
                    ·
                      rfl

theorem cell22_625998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 4, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 4, 1, 5, 3].length) (baseStart_625998 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_625998 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_625998 prefixEnd_625998 := by exact prefixLift 625998
  have htrace : WordTrace (prefixWord ++ tailWord_625998) baseStart_625998 baseEnd_625998 := by
    simpa [prefixWord, tailWord_625998, baseEnd_625998] using wordTrace_append hprefix tailTrace_625998
  have hstable : (prefixWord ++ tailWord_625998).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_625998).length < 2 ^ (prefixWord ++ tailWord_625998).sum := by decide
  have hdescent : baseEnd_625998 < baseStart_625998 := by decide
  rcases family_descends (prefixWord ++ tailWord_625998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_626015 : List Nat := [1, 1, 2, 3, 1, 2, 1, 7, 1, 3]
def baseStart_626015 : Nat := 118140960795 + 626015 * 2 ^ 59
def prefixEnd_626015 : Nat := 4983230072969 + 3 ^ 40 * 626015 * 2
def baseEnd_626015 : Nat := 214297727949648964755677

theorem tailTrace_626015 : CollatzResearch.WordTrace tailWord_626015 prefixEnd_626015 214297727949648964755677 := by
  unfold tailWord_626015
  simp only [CollatzResearch.WordTrace]
  refine ⟨22832642827062044695183499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15221761884708029796788999 22832642827062044695183499)
  ·
    refine ⟨34248964240593067042775249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22832642827062044695183499 34248964240593067042775249)
    ·
      refine ⟨25686723180444800282081437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34248964240593067042775249 25686723180444800282081437)
      ·
        refine ⟨9632521192666800105780539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25686723180444800282081437 9632521192666800105780539)
        ·
          refine ⟨14448781789000200158670809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9632521192666800105780539 14448781789000200158670809)
          ·
            refine ⟨10836586341750150119003107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14448781789000200158670809 10836586341750150119003107)
            ·
              refine ⟨16254879512625225178504661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10836586341750150119003107 16254879512625225178504661)
              ·
                refine ⟨380973738577153715121203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 16254879512625225178504661 380973738577153715121203)
                ·
                  refine ⟨571460607865730572681805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 380973738577153715121203 571460607865730572681805)
                  ·
                    refine ⟨214297727949648964755677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 571460607865730572681805 214297727949648964755677)
                    ·
                      rfl

theorem cell22_626015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 7, 1, 3].length) (baseStart_626015 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_626015 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_626015 prefixEnd_626015 := by exact prefixLift 626015
  have htrace : WordTrace (prefixWord ++ tailWord_626015) baseStart_626015 baseEnd_626015 := by
    simpa [prefixWord, tailWord_626015, baseEnd_626015] using wordTrace_append hprefix tailTrace_626015
  have hstable : (prefixWord ++ tailWord_626015).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_626015).length < 2 ^ (prefixWord ++ tailWord_626015).sum := by decide
  have hdescent : baseEnd_626015 < baseStart_626015 := by decide
  rcases family_descends (prefixWord ++ tailWord_626015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_626028 : List Nat := [2, 2, 1, 1, 5, 1, 1, 4, 5]
def baseStart_626028 : Nat := 118140960795 + 626028 * 2 ^ 59
def prefixEnd_626028 : Nat := 4983230072969 + 3 ^ 40 * 626028 * 2
def baseEnd_626028 : Nat := 71434059371773754726879

theorem tailTrace_626028 : CollatzResearch.WordTrace tailWord_626028 prefixEnd_626028 71434059371773754726879 := by
  unfold tailWord_626028
  simp only [CollatzResearch.WordTrace]
  refine ⟨11416558488007473957703369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15222077984009965276937825 11416558488007473957703369)
  ·
    refine ⟨8562418866005605468277527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11416558488007473957703369 8562418866005605468277527)
    ·
      refine ⟨12843628299008408202416291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8562418866005605468277527 12843628299008408202416291)
      ·
        refine ⟨19265442448512612303624437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12843628299008408202416291 19265442448512612303624437)
        ·
          refine ⟨1806135229548057403464791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 19265442448512612303624437 1806135229548057403464791)
          ·
            refine ⟨2709202844322086105197187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1806135229548057403464791 2709202844322086105197187)
            ·
              refine ⟨4063804266483129157795781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2709202844322086105197187 4063804266483129157795781)
              ·
                refine ⟨761963299965586717086709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4063804266483129157795781 761963299965586717086709)
                ·
                  refine ⟨71434059371773754726879, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 761963299965586717086709 71434059371773754726879)
                  ·
                    rfl

theorem cell22_626028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 5].length) (baseStart_626028 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_626028 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_626028 prefixEnd_626028 := by exact prefixLift 626028
  have htrace : WordTrace (prefixWord ++ tailWord_626028) baseStart_626028 baseEnd_626028 := by
    simpa [prefixWord, tailWord_626028, baseEnd_626028] using wordTrace_append hprefix tailTrace_626028
  have hstable : (prefixWord ++ tailWord_626028).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_626028).length < 2 ^ (prefixWord ++ tailWord_626028).sum := by decide
  have hdescent : baseEnd_626028 < baseStart_626028 := by decide
  rcases family_descends (prefixWord ++ tailWord_626028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_626066 : List Nat := [3, 2, 3, 3, 1, 1, 2, 3, 1, 3]
def baseStart_626066 : Nat := 118140960795 + 626066 * 2 ^ 59
def prefixEnd_626066 : Nat := 4983230072969 + 3 ^ 40 * 626066 * 2
def baseEnd_626066 : Nat := 214315186291901831730521

theorem tailTrace_626066 : CollatzResearch.WordTrace tailWord_626066 prefixEnd_626066 214315186291901831730521 := by
  unfold tailWord_626066
  simp only [CollatzResearch.WordTrace]
  refine ⟨5708625737469320101322513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15223001966584853603526701 5708625737469320101322513)
  ·
    refine ⟨4281469303101990075991885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5708625737469320101322513 4281469303101990075991885)
    ·
      refine ⟨1605550988663246278496957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4281469303101990075991885 1605550988663246278496957)
      ·
        refine ⟨602081620748717354436359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1605550988663246278496957 602081620748717354436359)
        ·
          refine ⟨903122431123076031654539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 602081620748717354436359 903122431123076031654539)
          ·
            refine ⟨1354683646684614047481809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 903122431123076031654539 1354683646684614047481809)
            ·
              refine ⟨1016012735013460535611357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1354683646684614047481809 1016012735013460535611357)
              ·
                refine ⟨381004775630047700854259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1016012735013460535611357 381004775630047700854259)
                ·
                  refine ⟨571507163445071551281389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 381004775630047700854259 571507163445071551281389)
                  ·
                    refine ⟨214315186291901831730521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 571507163445071551281389 214315186291901831730521)
                    ·
                      rfl

theorem cell22_626066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 2, 3, 1, 3].length) (baseStart_626066 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_626066 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_626066 prefixEnd_626066 := by exact prefixLift 626066
  have htrace : WordTrace (prefixWord ++ tailWord_626066) baseStart_626066 baseEnd_626066 := by
    simpa [prefixWord, tailWord_626066, baseEnd_626066] using wordTrace_append hprefix tailTrace_626066
  have hstable : (prefixWord ++ tailWord_626066).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_626066).length < 2 ^ (prefixWord ++ tailWord_626066).sum := by decide
  have hdescent : baseEnd_626066 < baseStart_626066 := by decide
  rcases family_descends (prefixWord ++ tailWord_626066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_626210 : List Nat := [3, 3, 1, 1, 1, 1, 3, 2, 3, 4]
def baseStart_626210 : Nat := 118140960795 + 626210 * 2 ^ 59
def prefixEnd_626210 : Nat := 4983230072969 + 3 ^ 40 * 626210 * 2
def baseEnd_626210 : Nat := 214364480434733456130079

theorem tailTrace_626210 : CollatzResearch.WordTrace tailWord_626210 prefixEnd_626210 214364480434733456130079 := by
  unfold tailWord_626210
  simp only [CollatzResearch.WordTrace]
  refine ⟨5709938765338898249633021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15226503374237061999021389 5709938765338898249633021)
  ·
    refine ⟨2141227037002086843612383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5709938765338898249633021 2141227037002086843612383)
    ·
      refine ⟨3211840555503130265418575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2141227037002086843612383 3211840555503130265418575)
      ·
        refine ⟨4817760833254695398127863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3211840555503130265418575 4817760833254695398127863)
        ·
          refine ⟨7226641249882043097191795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4817760833254695398127863 7226641249882043097191795)
          ·
            refine ⟨10839961874823064645787693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7226641249882043097191795 10839961874823064645787693)
            ·
              refine ⟨4064985703058649242170385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10839961874823064645787693 4064985703058649242170385)
              ·
                refine ⟨3048739277293986931627789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4064985703058649242170385 3048739277293986931627789)
                ·
                  refine ⟨1143277228985245099360421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3048739277293986931627789 1143277228985245099360421)
                  ·
                    refine ⟨214364480434733456130079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1143277228985245099360421 214364480434733456130079)
                    ·
                      rfl

theorem cell22_626210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 3, 2, 3, 4].length) (baseStart_626210 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_626210 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_626210 prefixEnd_626210 := by exact prefixLift 626210
  have htrace : WordTrace (prefixWord ++ tailWord_626210) baseStart_626210 baseEnd_626210 := by
    simpa [prefixWord, tailWord_626210, baseEnd_626210] using wordTrace_append hprefix tailTrace_626210
  have hstable : (prefixWord ++ tailWord_626210).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_626210).length < 2 ^ (prefixWord ++ tailWord_626210).sum := by decide
  have hdescent : baseEnd_626210 < baseStart_626210 := by decide
  rcases family_descends (prefixWord ++ tailWord_626210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_626240 : List Nat := [2, 1, 1, 2, 2, 2, 1, 4, 4, 3]
def baseStart_626240 : Nat := 118140960795 + 626240 * 2 ^ 59
def prefixEnd_626240 : Nat := 4983230072969 + 3 ^ 40 * 626240 * 2
def baseEnd_626240 : Nat := 214374750047823377879987

theorem tailTrace_626240 : CollatzResearch.WordTrace tailWord_626240 prefixEnd_626240 214374750047823377879987 := by
  unfold tailWord_626240
  simp only [CollatzResearch.WordTrace]
  refine ⟨11420424625623454061062087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15227232834164605414749449 11420424625623454061062087)
  ·
    refine ⟨17130636938435181091593131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11420424625623454061062087 17130636938435181091593131)
    ·
      refine ⟨25695955407652771637389697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17130636938435181091593131 25695955407652771637389697)
      ·
        refine ⟨19271966555739578728042273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25695955407652771637389697 19271966555739578728042273)
        ·
          refine ⟨14453974916804684046031705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19271966555739578728042273 14453974916804684046031705)
          ·
            refine ⟨10840481187603513034523779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14453974916804684046031705 10840481187603513034523779)
            ·
              refine ⟨16260721781405269551785669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10840481187603513034523779 16260721781405269551785669)
              ·
                refine ⟨3048885334013488040959813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16260721781405269551785669 3048885334013488040959813)
                ·
                  refine ⟨571666000127529007679965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3048885334013488040959813 571666000127529007679965)
                  ·
                    refine ⟨214374750047823377879987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 571666000127529007679965 214374750047823377879987)
                    ·
                      rfl

theorem cell22_626240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 4, 4, 3].length) (baseStart_626240 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_626240 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_626240 prefixEnd_626240 := by exact prefixLift 626240
  have htrace : WordTrace (prefixWord ++ tailWord_626240) baseStart_626240 baseEnd_626240 := by
    simpa [prefixWord, tailWord_626240, baseEnd_626240] using wordTrace_append hprefix tailTrace_626240
  have hstable : (prefixWord ++ tailWord_626240).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_626240).length < 2 ^ (prefixWord ++ tailWord_626240).sum := by decide
  have hdescent : baseEnd_626240 < baseStart_626240 := by decide
  rcases family_descends (prefixWord ++ tailWord_626240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_626283 : List Nat := [1, 1, 1, 1, 2, 2, 1, 2, 3, 8]
def baseStart_626283 : Nat := 118140960795 + 626283 * 2 ^ 59
def prefixEnd_626283 : Nat := 4983230072969 + 3 ^ 40 * 626283 * 2
def baseEnd_626283 : Nat := 214389469826585599054855

theorem tailTrace_626283 : CollatzResearch.WordTrace tailWord_626283 prefixEnd_626283 214389469826585599054855 := by
  unfold tailWord_626283
  simp only [CollatzResearch.WordTrace]
  refine ⟨22842417590091126465939503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15228278393394084310626335 22842417590091126465939503)
  ·
    refine ⟨34263626385136689698909255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22842417590091126465939503 34263626385136689698909255)
    ·
      refine ⟨51395439577705034548363883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34263626385136689698909255 51395439577705034548363883)
      ·
        refine ⟨77093159366557551822545825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51395439577705034548363883 77093159366557551822545825)
        ·
          refine ⟨57819869524918163866909369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77093159366557551822545825 57819869524918163866909369)
          ·
            refine ⟨43364902143688622900182027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57819869524918163866909369 43364902143688622900182027)
            ·
              refine ⟨65047353215532934350273041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43364902143688622900182027 65047353215532934350273041)
              ·
                refine ⟨48785514911649700762704781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 65047353215532934350273041 48785514911649700762704781)
                ·
                  refine ⟨18294568091868637786014293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 48785514911649700762704781 18294568091868637786014293)
                  ·
                    refine ⟨214389469826585599054855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 18294568091868637786014293 214389469826585599054855)
                    ·
                      rfl

theorem cell22_626283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 2, 3, 8].length) (baseStart_626283 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_626283 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_626283 prefixEnd_626283 := by exact prefixLift 626283
  have htrace : WordTrace (prefixWord ++ tailWord_626283) baseStart_626283 baseEnd_626283 := by
    simpa [prefixWord, tailWord_626283, baseEnd_626283] using wordTrace_append hprefix tailTrace_626283
  have hstable : (prefixWord ++ tailWord_626283).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_626283).length < 2 ^ (prefixWord ++ tailWord_626283).sum := by decide
  have hdescent : baseEnd_626283 < baseStart_626283 := by decide
  rcases family_descends (prefixWord ++ tailWord_626283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_626315 : List Nat := [1, 1, 1, 1, 4, 1, 4, 4, 5]
def baseStart_626315 : Nat := 118140960795 + 626315 * 2 ^ 59
def prefixEnd_626315 : Nat := 4983230072969 + 3 ^ 40 * 626315 * 2
def baseEnd_626315 : Nat := 71466808026849394084919

theorem tailTrace_626315 : CollatzResearch.WordTrace tailWord_626315 prefixEnd_626315 71466808026849394084919 := by
  unfold tailWord_626315
  simp only [CollatzResearch.WordTrace]
  refine ⟨22843584725975195931104399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15229056483983463954069599 22843584725975195931104399)
  ·
    refine ⟨34265377088962793896656599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22843584725975195931104399 34265377088962793896656599)
    ·
      refine ⟨51398065633444190844984899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34265377088962793896656599 51398065633444190844984899)
      ·
        refine ⟨77097098450166286267477349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51398065633444190844984899 77097098450166286267477349)
        ·
          refine ⟨14455705959406178675152003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 77097098450166286267477349 14455705959406178675152003)
          ·
            refine ⟨21683558939109268012728005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14455705959406178675152003 21683558939109268012728005)
            ·
              refine ⟨4065667301082987752386501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21683558939109268012728005 4065667301082987752386501)
              ·
                refine ⟨762312618953060203572469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4065667301082987752386501 762312618953060203572469)
                ·
                  refine ⟨71466808026849394084919, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 762312618953060203572469 71466808026849394084919)
                  ·
                    rfl

theorem cell22_626315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 4, 4, 5].length) (baseStart_626315 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_626315 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_626315 prefixEnd_626315 := by exact prefixLift 626315
  have htrace : WordTrace (prefixWord ++ tailWord_626315) baseStart_626315 baseEnd_626315 := by
    simpa [prefixWord, tailWord_626315, baseEnd_626315] using wordTrace_append hprefix tailTrace_626315
  have hstable : (prefixWord ++ tailWord_626315).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_626315).length < 2 ^ (prefixWord ++ tailWord_626315).sum := by decide
  have hdescent : baseEnd_626315 < baseStart_626315 := by decide
  rcases family_descends (prefixWord ++ tailWord_626315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_626375 : List Nat := [1, 1, 4, 1, 1, 1, 3, 2, 3, 5]
def baseStart_626375 : Nat := 118140960795 + 626375 * 2 ^ 59
def prefixEnd_626375 : Nat := 4983230072969 + 3 ^ 40 * 626375 * 2
def baseEnd_626375 : Nat := 214420963306728025754573

theorem tailTrace_626375 : CollatzResearch.WordTrace tailWord_626375 prefixEnd_626375 214420963306728025754573 := by
  unfold tailWord_626375
  simp only [CollatzResearch.WordTrace]
  refine ⟨22845773105757826178288579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15230515403838550785525719 22845773105757826178288579)
  ·
    refine ⟨34268659658636739267432869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22845773105757826178288579 34268659658636739267432869)
    ·
      refine ⟨6425373685994388612643663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 34268659658636739267432869 6425373685994388612643663)
      ·
        refine ⟨9638060528991582918965495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6425373685994388612643663 9638060528991582918965495)
        ·
          refine ⟨14457090793487374378448243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9638060528991582918965495 14457090793487374378448243)
          ·
            refine ⟨21685636190231061567672365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14457090793487374378448243 21685636190231061567672365)
            ·
              refine ⟨8132113571336648087877137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21685636190231061567672365 8132113571336648087877137)
              ·
                refine ⟨6099085178502486065907853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8132113571336648087877137 6099085178502486065907853)
                ·
                  refine ⟨2287156941938432274715445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6099085178502486065907853 2287156941938432274715445)
                  ·
                    refine ⟨214420963306728025754573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2287156941938432274715445 214420963306728025754573)
                    ·
                      rfl

theorem cell22_626375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 2, 3, 5].length) (baseStart_626375 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_626375 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_626375 prefixEnd_626375 := by exact prefixLift 626375
  have htrace : WordTrace (prefixWord ++ tailWord_626375) baseStart_626375 baseEnd_626375 := by
    simpa [prefixWord, tailWord_626375, baseEnd_626375] using wordTrace_append hprefix tailTrace_626375
  have hstable : (prefixWord ++ tailWord_626375).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_626375).length < 2 ^ (prefixWord ++ tailWord_626375).sum := by decide
  have hdescent : baseEnd_626375 < baseStart_626375 := by decide
  rcases family_descends (prefixWord ++ tailWord_626375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_626392 : List Nat := [2, 1, 2, 2, 3, 1, 4, 1, 1, 5]
def baseStart_626392 : Nat := 118140960795 + 626392 * 2 ^ 59
def prefixEnd_626392 : Nat := 4983230072969 + 3 ^ 40 * 626392 * 2
def baseEnd_626392 : Nat := 214426782754145648079521

theorem tailTrace_626392 : CollatzResearch.WordTrace tailWord_626392 prefixEnd_626392 214426782754145648079521 := by
  unfold tailWord_626392
  simp only [CollatzResearch.WordTrace]
  refine ⟨11423196573348119040828715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15230928764464158721104953 11423196573348119040828715)
  ·
    refine ⟨17134794860022178561243073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11423196573348119040828715 17134794860022178561243073)
    ·
      refine ⟨12851096145016633920932305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17134794860022178561243073 12851096145016633920932305)
      ·
        refine ⟨9638322108762475440699229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12851096145016633920932305 9638322108762475440699229)
        ·
          refine ⟨3614370790785928290262211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9638322108762475440699229 3614370790785928290262211)
          ·
            refine ⟨5421556186178892435393317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3614370790785928290262211 5421556186178892435393317)
            ·
              refine ⟨1016541784908542331636247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5421556186178892435393317 1016541784908542331636247)
              ·
                refine ⟨1524812677362813497454371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1016541784908542331636247 1524812677362813497454371)
                ·
                  refine ⟨2287219016044220246181557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1524812677362813497454371 2287219016044220246181557)
                  ·
                    refine ⟨214426782754145648079521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2287219016044220246181557 214426782754145648079521)
                    ·
                      rfl

theorem cell22_626392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 4, 1, 1, 5].length) (baseStart_626392 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_626392 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_626392 prefixEnd_626392 := by exact prefixLift 626392
  have htrace : WordTrace (prefixWord ++ tailWord_626392) baseStart_626392 baseEnd_626392 := by
    simpa [prefixWord, tailWord_626392, baseEnd_626392] using wordTrace_append hprefix tailTrace_626392
  have hstable : (prefixWord ++ tailWord_626392).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_626392).length < 2 ^ (prefixWord ++ tailWord_626392).sum := by decide
  have hdescent : baseEnd_626392 < baseStart_626392 := by decide
  rcases family_descends (prefixWord ++ tailWord_626392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_626422 : List Nat := [5, 1, 1, 1, 1, 4, 9]
def baseStart_626422 : Nat := 118140960795 + 626422 * 2 ^ 59
def prefixEnd_626422 : Nat := 4983230072969 + 3 ^ 40 * 626422 * 2
def baseEnd_626422 : Nat := 7942113050638354438127

theorem tailTrace_626422 : CollatzResearch.WordTrace tailWord_626422 prefixEnd_626422 7942113050638354438127 := by
  unfold tailWord_626422
  simp only [CollatzResearch.WordTrace]
  refine ⟨1427967958536722075328095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 15231658224391702136833013 1427967958536722075328095)
  ·
    refine ⟨2141951937805083112992143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1427967958536722075328095 2141951937805083112992143)
    ·
      refine ⟨3212927906707624669488215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2141951937805083112992143 3212927906707624669488215)
      ·
        refine ⟨4819391860061437004232323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3212927906707624669488215 4819391860061437004232323)
        ·
          refine ⟨7229087790092155506348485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4819391860061437004232323 7229087790092155506348485)
          ·
            refine ⟨1355453960642279157440341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7229087790092155506348485 1355453960642279157440341)
            ·
              refine ⟨7942113050638354438127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1355453960642279157440341 7942113050638354438127)
              ·
                rfl

theorem cell22_626422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 9].length) (baseStart_626422 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_626422 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_626422 prefixEnd_626422 := by exact prefixLift 626422
  have htrace : WordTrace (prefixWord ++ tailWord_626422) baseStart_626422 baseEnd_626422 := by
    simpa [prefixWord, tailWord_626422, baseEnd_626422] using wordTrace_append hprefix tailTrace_626422
  have hstable : (prefixWord ++ tailWord_626422).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_626422).length < 2 ^ (prefixWord ++ tailWord_626422).sum := by decide
  have hdescent : baseEnd_626422 < baseStart_626422 := by decide
  rcases family_descends (prefixWord ++ tailWord_626422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_626435 : List Nat := [1, 1, 1, 3, 2, 2, 2, 1, 1, 8]
def baseStart_626435 : Nat := 118140960795 + 626435 * 2 ^ 59
def prefixEnd_626435 : Nat := 4983230072969 + 3 ^ 40 * 626435 * 2
def baseEnd_626435 : Nat := 214441502532907869254389

theorem tailTrace_626435 : CollatzResearch.WordTrace tailWord_626435 prefixEnd_626435 214441502532907869254389 := by
  unfold tailWord_626435
  simp only [CollatzResearch.WordTrace]
  refine ⟨22847961485540456425472759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15231974323693637616981839 22847961485540456425472759)
  ·
    refine ⟨34271942228310684638209139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22847961485540456425472759 34271942228310684638209139)
    ·
      refine ⟨51407913342466026957313709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34271942228310684638209139 51407913342466026957313709)
      ·
        refine ⟨19277967503424760108992641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51407913342466026957313709 19277967503424760108992641)
        ·
          refine ⟨14458475627568570081744481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19277967503424760108992641 14458475627568570081744481)
          ·
            refine ⟨10843856720676427561308361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14458475627568570081744481 10843856720676427561308361)
            ·
              refine ⟨8132892540507320670981271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10843856720676427561308361 8132892540507320670981271)
              ·
                refine ⟨12199338810760981006471907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8132892540507320670981271 12199338810760981006471907)
                ·
                  refine ⟨18299008216141471509707861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12199338810760981006471907 18299008216141471509707861)
                  ·
                    refine ⟨214441502532907869254389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 18299008216141471509707861 214441502532907869254389)
                    ·
                      rfl

theorem cell22_626435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 1, 1, 8].length) (baseStart_626435 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_626435 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_626435 prefixEnd_626435 := by exact prefixLift 626435
  have htrace : WordTrace (prefixWord ++ tailWord_626435) baseStart_626435 baseEnd_626435 := by
    simpa [prefixWord, tailWord_626435, baseEnd_626435] using wordTrace_append hprefix tailTrace_626435
  have hstable : (prefixWord ++ tailWord_626435).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_626435).length < 2 ^ (prefixWord ++ tailWord_626435).sum := by decide
  have hdescent : baseEnd_626435 < baseStart_626435 := by decide
  rcases family_descends (prefixWord ++ tailWord_626435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_626462 : List Nat := [4, 3, 2, 2, 2, 1, 1, 3, 4]
def baseStart_626462 : Nat := 118140960795 + 626462 * 2 ^ 59
def prefixEnd_626462 : Nat := 4983230072969 + 3 ^ 40 * 626462 * 2
def baseEnd_626462 : Nat := 71483581728229599609769

theorem tailTrace_626462 : CollatzResearch.WordTrace tailWord_626462 prefixEnd_626462 71483581728229599609769 := by
  unfold tailWord_626462
  simp only [CollatzResearch.WordTrace]
  refine ⟨2856118282055330004588205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15232630837628426691137093 2856118282055330004588205)
  ·
    refine ⟨1071044355770748751720577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2856118282055330004588205 1071044355770748751720577)
    ·
      refine ⟨803283266828061563790433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1071044355770748751720577 803283266828061563790433)
      ·
        refine ⟨602462450121046172842825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 803283266828061563790433 602462450121046172842825)
        ·
          refine ⟨451846837590784629632119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 602462450121046172842825 451846837590784629632119)
          ·
            refine ⟨677770256386176944448179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 451846837590784629632119 677770256386176944448179)
            ·
              refine ⟨1016655384579265416672269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 677770256386176944448179 1016655384579265416672269)
              ·
                refine ⟨381245769217224531252101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1016655384579265416672269 381245769217224531252101)
                ·
                  refine ⟨71483581728229599609769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 381245769217224531252101 71483581728229599609769)
                  ·
                    rfl

theorem cell22_626462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 2, 1, 1, 3, 4].length) (baseStart_626462 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_626462 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_626462 prefixEnd_626462 := by exact prefixLift 626462
  have htrace : WordTrace (prefixWord ++ tailWord_626462) baseStart_626462 baseEnd_626462 := by
    simpa [prefixWord, tailWord_626462, baseEnd_626462] using wordTrace_append hprefix tailTrace_626462
  have hstable : (prefixWord ++ tailWord_626462).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_626462).length < 2 ^ (prefixWord ++ tailWord_626462).sum := by decide
  have hdescent : baseEnd_626462 < baseStart_626462 := by decide
  rcases family_descends (prefixWord ++ tailWord_626462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_626484 : List Nat := [2, 5, 1, 1, 2, 1, 2, 1, 7]
def baseStart_626484 : Nat := 118140960795 + 626484 * 2 ^ 59
def prefixEnd_626484 : Nat := 4983230072969 + 3 ^ 40 * 626484 * 2
def baseEnd_626484 : Nat := 71486092078096024926413

theorem tailTrace_626484 : CollatzResearch.WordTrace tailWord_626484 prefixEnd_626484 71486092078096024926413 := by
  unfold tailWord_626484
  simp only [CollatzResearch.WordTrace]
  refine ⟨11424874331181468897003253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15233165774908625196004337 11424874331181468897003253)
  ·
    refine ⟨1071081968548262709094055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 11424874331181468897003253 1071081968548262709094055)
    ·
      refine ⟨1606622952822394063641083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1071081968548262709094055 1606622952822394063641083)
      ·
        refine ⟨2409934429233591095461625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1606622952822394063641083 2409934429233591095461625)
        ·
          refine ⟨1807450821925193321596219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2409934429233591095461625 1807450821925193321596219)
          ·
            refine ⟨2711176232887789982394329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1807450821925193321596219 2711176232887789982394329)
            ·
              refine ⟨2033382174665842486795747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2711176232887789982394329 2033382174665842486795747)
              ·
                refine ⟨3050073261998763730193621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2033382174665842486795747 3050073261998763730193621)
                ·
                  refine ⟨71486092078096024926413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3050073261998763730193621 71486092078096024926413)
                  ·
                    rfl

theorem cell22_626484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 2, 1, 7].length) (baseStart_626484 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_626484 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_626484 prefixEnd_626484 := by exact prefixLift 626484
  have htrace : WordTrace (prefixWord ++ tailWord_626484) baseStart_626484 baseEnd_626484 := by
    simpa [prefixWord, tailWord_626484, baseEnd_626484] using wordTrace_append hprefix tailTrace_626484
  have hstable : (prefixWord ++ tailWord_626484).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_626484).length < 2 ^ (prefixWord ++ tailWord_626484).sum := by decide
  have hdescent : baseEnd_626484 < baseStart_626484 := by decide
  rcases family_descends (prefixWord ++ tailWord_626484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_626488 : List Nat := [2, 1, 2, 1, 3, 4, 3, 2, 1, 3]
def baseStart_626488 : Nat := 118140960795 + 626488 * 2 ^ 59
def prefixEnd_626488 : Nat := 4983230072969 + 3 ^ 40 * 626488 * 2
def baseEnd_626488 : Nat := 214459645516033397679227

theorem tailTrace_626488 : CollatzResearch.WordTrace tailWord_626488 prefixEnd_626488 214459645516033397679227 := by
  unfold tailWord_626488
  simp only [CollatzResearch.WordTrace]
  refine ⟨11424947277174223238576059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15233263036232297651434745 11424947277174223238576059)
  ·
    refine ⟨17137420915761334857864089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11424947277174223238576059 17137420915761334857864089)
    ·
      refine ⟨12853065686821001143398067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17137420915761334857864089 12853065686821001143398067)
      ·
        refine ⟨19279598530231501715097101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12853065686821001143398067 19279598530231501715097101)
        ·
          refine ⟨7229849448836813143161413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19279598530231501715097101 7229849448836813143161413)
          ·
            refine ⟨1355596771656902464342765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7229849448836813143161413 1355596771656902464342765)
            ·
              refine ⟨508348789371338424128537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1355596771656902464342765 508348789371338424128537)
              ·
                refine ⟨381261592028503818096403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 508348789371338424128537 381261592028503818096403)
                ·
                  refine ⟨571892388042755727144605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 381261592028503818096403 571892388042755727144605)
                  ·
                    refine ⟨214459645516033397679227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 571892388042755727144605 214459645516033397679227)
                    ·
                      rfl

theorem cell22_626488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 3, 2, 1, 3].length) (baseStart_626488 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_626488 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_626488 prefixEnd_626488 := by exact prefixLift 626488
  have htrace : WordTrace (prefixWord ++ tailWord_626488) baseStart_626488 baseEnd_626488 := by
    simpa [prefixWord, tailWord_626488, baseEnd_626488] using wordTrace_append hprefix tailTrace_626488
  have hstable : (prefixWord ++ tailWord_626488).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_626488).length < 2 ^ (prefixWord ++ tailWord_626488).sum := by decide
  have hdescent : baseEnd_626488 < baseStart_626488 := by decide
  rcases family_descends (prefixWord ++ tailWord_626488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_626514 : List Nat := [3, 2, 2, 1, 1, 4, 1, 1, 3, 4]
def baseStart_626514 : Nat := 118140960795 + 626514 * 2 ^ 59
def prefixEnd_626514 : Nat := 4983230072969 + 3 ^ 40 * 626514 * 2
def baseEnd_626514 : Nat := 214468545847377996529147

theorem tailTrace_626514 : CollatzResearch.WordTrace tailWord_626514 prefixEnd_626514 214468545847377996529147 := by
  unfold tailWord_626514
  simp only [CollatzResearch.WordTrace]
  refine ⟨5712710713063563229399649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15233895234836168611732397 5712710713063563229399649)
  ·
    refine ⟨4284533034797672422049737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5712710713063563229399649 4284533034797672422049737)
    ·
      refine ⟨3213399776098254316537303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4284533034797672422049737 3213399776098254316537303)
      ·
        refine ⟨4820099664147381474805955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3213399776098254316537303 4820099664147381474805955)
        ·
          refine ⟨7230149496221072212208933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4820099664147381474805955 7230149496221072212208933)
          ·
            refine ⟨1355653030541451039789175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7230149496221072212208933 1355653030541451039789175)
            ·
              refine ⟨2033479545812176559683763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1355653030541451039789175 2033479545812176559683763)
              ·
                refine ⟨3050219318718264839525645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2033479545812176559683763 3050219318718264839525645)
                ·
                  refine ⟨1143832244519349314822117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3050219318718264839525645 1143832244519349314822117)
                  ·
                    refine ⟨214468545847377996529147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1143832244519349314822117 214468545847377996529147)
                    ·
                      rfl

theorem cell22_626514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 1, 1, 3, 4].length) (baseStart_626514 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_626514 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_626514 prefixEnd_626514 := by exact prefixLift 626514
  have htrace : WordTrace (prefixWord ++ tailWord_626514) baseStart_626514 baseEnd_626514 := by
    simpa [prefixWord, tailWord_626514, baseEnd_626514] using wordTrace_append hprefix tailTrace_626514
  have hstable : (prefixWord ++ tailWord_626514).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_626514).length < 2 ^ (prefixWord ++ tailWord_626514).sum := by decide
  have hdescent : baseEnd_626514 < baseStart_626514 := by decide
  rcases family_descends (prefixWord ++ tailWord_626514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_626527 : List Nat := [1, 1, 2, 3, 1, 4, 1, 1, 3, 5]
def baseStart_626527 : Nat := 118140960795 + 626527 * 2 ^ 59
def prefixEnd_626527 : Nat := 4983230072969 + 3 ^ 40 * 626527 * 2
def baseEnd_626527 : Nat := 214472996013050295954107

theorem tailTrace_626527 : CollatzResearch.WordTrace tailWord_626527 prefixEnd_626527 214472996013050295954107 := by
  unfold tailWord_626527
  simp only [CollatzResearch.WordTrace]
  refine ⟨22851317001207156137821835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15234211334138104091881223 22851317001207156137821835)
  ·
    refine ⟨34276975501810734206732753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22851317001207156137821835 34276975501810734206732753)
    ·
      refine ⟨25707731626358050655049565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34276975501810734206732753 25707731626358050655049565)
      ·
        refine ⟨9640399359884268995643587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25707731626358050655049565 9640399359884268995643587)
        ·
          refine ⟨14460599039826403493465381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9640399359884268995643587 14460599039826403493465381)
          ·
            refine ⟨2711362319967450655024759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14460599039826403493465381 2711362319967450655024759)
            ·
              refine ⟨4067043479951175982537139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2711362319967450655024759 4067043479951175982537139)
              ·
                refine ⟨6100565219926763973805709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4067043479951175982537139 6100565219926763973805709)
                ·
                  refine ⟨2287711957472536490177141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6100565219926763973805709 2287711957472536490177141)
                  ·
                    refine ⟨214472996013050295954107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2287711957472536490177141 214472996013050295954107)
                    ·
                      rfl

theorem cell22_626527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 1, 1, 3, 5].length) (baseStart_626527 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_626527 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_626527 prefixEnd_626527 := by exact prefixLift 626527
  have htrace : WordTrace (prefixWord ++ tailWord_626527) baseStart_626527 baseEnd_626527 := by
    simpa [prefixWord, tailWord_626527, baseEnd_626527] using wordTrace_append hprefix tailTrace_626527
  have hstable : (prefixWord ++ tailWord_626527).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_626527).length < 2 ^ (prefixWord ++ tailWord_626527).sum := by decide
  have hdescent : baseEnd_626527 < baseStart_626527 := by decide
  rcases family_descends (prefixWord ++ tailWord_626527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_626529 : List Nat := [1, 2, 3, 1, 1, 1, 4, 5, 4]
def baseStart_626529 : Nat := 118140960795 + 626529 * 2 ^ 59
def prefixEnd_626529 : Nat := 4983230072969 + 3 ^ 40 * 626529 * 2
def baseEnd_626529 : Nat := 71491226884640985801367

theorem tailTrace_626529 : CollatzResearch.WordTrace tailWord_626529 prefixEnd_626529 71491226884640985801367 := by
  unfold tailWord_626529
  simp only [CollatzResearch.WordTrace]
  refine ⟨22851389947199910479394641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15234259964799940319596427 22851389947199910479394641)
  ·
    refine ⟨17138542460399932859545981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22851389947199910479394641 17138542460399932859545981)
    ·
      refine ⟨6426953422649974822329743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17138542460399932859545981 6426953422649974822329743)
      ·
        refine ⟨9640430133974962233494615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6426953422649974822329743 9640430133974962233494615)
        ·
          refine ⟨14460645200962443350241923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9640430133974962233494615 14460645200962443350241923)
          ·
            refine ⟨21690967801443665025362885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14460645200962443350241923 21690967801443665025362885)
            ·
              refine ⟨4067056462770687192255541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21690967801443665025362885 4067056462770687192255541)
              ·
                refine ⟨381286543384751924273957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4067056462770687192255541 381286543384751924273957)
                ·
                  refine ⟨71491226884640985801367, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 381286543384751924273957 71491226884640985801367)
                  ·
                    rfl

theorem cell22_626529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 4, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 4, 5, 4].length) (baseStart_626529 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_626529 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_626529 prefixEnd_626529 := by exact prefixLift 626529
  have htrace : WordTrace (prefixWord ++ tailWord_626529) baseStart_626529 baseEnd_626529 := by
    simpa [prefixWord, tailWord_626529, baseEnd_626529] using wordTrace_append hprefix tailTrace_626529
  have hstable : (prefixWord ++ tailWord_626529).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_626529).length < 2 ^ (prefixWord ++ tailWord_626529).sum := by decide
  have hdescent : baseEnd_626529 < baseStart_626529 := by decide
  rcases family_descends (prefixWord ++ tailWord_626529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_626612 : List Nat := [2, 5, 2, 1, 2, 1, 3, 1, 2, 3]
def baseStart_626612 : Nat := 118140960795 + 626612 * 2 ^ 59
def prefixEnd_626612 : Nat := 4983230072969 + 3 ^ 40 * 626612 * 2
def baseEnd_626612 : Nat := 214502093250138407578847

theorem tailTrace_626612 : CollatzResearch.WordTrace tailWord_626612 prefixEnd_626612 214502093250138407578847 := by
  unfold tailWord_626612
  simp only [CollatzResearch.WordTrace]
  refine ⟨11427208602949607827333045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15236278137266143769777393 11427208602949607827333045)
  ·
    refine ⟨1071300806526525733812473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 11427208602949607827333045 1071300806526525733812473)
    ·
      refine ⟨803475604894894300359355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1071300806526525733812473 803475604894894300359355)
      ·
        refine ⟨1205213407342341450539033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 803475604894894300359355 1205213407342341450539033)
        ·
          refine ⟨903910055506756087904275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1205213407342341450539033 903910055506756087904275)
          ·
            refine ⟨1355865083260134131856413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 903910055506756087904275 1355865083260134131856413)
            ·
              refine ⟨508449406222550299446155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1355865083260134131856413 508449406222550299446155)
              ·
                refine ⟨762674109333825449169233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 508449406222550299446155 762674109333825449169233)
                ·
                  refine ⟨572005582000369086876925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 762674109333825449169233 572005582000369086876925)
                  ·
                    refine ⟨214502093250138407578847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 572005582000369086876925 214502093250138407578847)
                    ·
                      rfl

theorem cell22_626612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 3, 1, 2, 3].length) (baseStart_626612 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_626612 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_626612 prefixEnd_626612 := by exact prefixLift 626612
  have htrace : WordTrace (prefixWord ++ tailWord_626612) baseStart_626612 baseEnd_626612 := by
    simpa [prefixWord, tailWord_626612, baseEnd_626612] using wordTrace_append hprefix tailTrace_626612
  have hstable : (prefixWord ++ tailWord_626612).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_626612).length < 2 ^ (prefixWord ++ tailWord_626612).sum := by decide
  have hdescent : baseEnd_626612 < baseStart_626612 := by decide
  rcases family_descends (prefixWord ++ tailWord_626612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_626709 : List Nat := [1, 3, 2, 1, 5, 10]
def baseStart_626709 : Nat := 118140960795 + 626709 * 2 ^ 59
def prefixEnd_626709 : Nat := 4983230072969 + 3 ^ 40 * 626709 * 2
def baseEnd_626709 : Nat := 2648583930030401085229

theorem tailTrace_626709 : CollatzResearch.WordTrace tailWord_626709 prefixEnd_626709 2648583930030401085229 := by
  unfold tailWord_626709
  simp only [CollatzResearch.WordTrace]
  refine ⟨22857955086547801220947181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15238636724365200813964787 22857955086547801220947181)
  ·
    refine ⟨8571733157455425457855193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22857955086547801220947181 8571733157455425457855193)
    ·
      refine ⟨6428799868091569093391395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8571733157455425457855193 6428799868091569093391395)
      ·
        refine ⟨9643199802137353640087093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6428799868091569093391395 9643199802137353640087093)
        ·
          refine ⟨904049981450376903758165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 9643199802137353640087093 904049981450376903758165)
          ·
            refine ⟨2648583930030401085229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 904049981450376903758165 2648583930030401085229)
            ·
              rfl

theorem cell22_626709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 10].length) (baseStart_626709 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_626709 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_626709 prefixEnd_626709 := by exact prefixLift 626709
  have htrace : WordTrace (prefixWord ++ tailWord_626709) baseStart_626709 baseEnd_626709 := by
    simpa [prefixWord, tailWord_626709, baseEnd_626709] using wordTrace_append hprefix tailTrace_626709
  have hstable : (prefixWord ++ tailWord_626709).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_626709).length < 2 ^ (prefixWord ++ tailWord_626709).sum := by decide
  have hdescent : baseEnd_626709 < baseStart_626709 := by decide
  rcases family_descends (prefixWord ++ tailWord_626709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_626741 : List Nat := [1, 3, 3, 1, 1, 1, 3, 1, 5, 3]
def baseStart_626741 : Nat := 118140960795 + 626741 * 2 ^ 59
def prefixEnd_626741 : Nat := 4983230072969 + 3 ^ 40 * 626741 * 2
def baseEnd_626741 : Nat := 214546252586425071103451

theorem tailTrace_626741 : CollatzResearch.WordTrace tailWord_626741 prefixEnd_626741 214546252586425071103451 := by
  unfold tailWord_626741
  simp only [CollatzResearch.WordTrace]
  refine ⟨22859122222431870686112077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15239414814954580457408051 22859122222431870686112077)
  ·
    refine ⟨8572170833411951507292029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22859122222431870686112077 8572170833411951507292029)
    ·
      refine ⟨3214564062529481815234511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8572170833411951507292029 3214564062529481815234511)
      ·
        refine ⟨4821846093794222722851767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3214564062529481815234511 4821846093794222722851767)
        ·
          refine ⟨7232769140691334084277651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4821846093794222722851767 7232769140691334084277651)
          ·
            refine ⟨10849153711037001126416477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7232769140691334084277651 10849153711037001126416477)
            ·
              refine ⟨4068432641638875422406179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10849153711037001126416477 4068432641638875422406179)
              ·
                refine ⟨6102648962458313133609269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4068432641638875422406179 6102648962458313133609269)
                ·
                  refine ⟨572123340230466856275869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 6102648962458313133609269 572123340230466856275869)
                  ·
                    refine ⟨214546252586425071103451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 572123340230466856275869 214546252586425071103451)
                    ·
                      rfl

theorem cell22_626741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 3, 1, 5, 3].length) (baseStart_626741 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_626741 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_626741 prefixEnd_626741 := by exact prefixLift 626741
  have htrace : WordTrace (prefixWord ++ tailWord_626741) baseStart_626741 baseEnd_626741 := by
    simpa [prefixWord, tailWord_626741, baseEnd_626741] using wordTrace_append hprefix tailTrace_626741
  have hstable : (prefixWord ++ tailWord_626741).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_626741).length < 2 ^ (prefixWord ++ tailWord_626741).sum := by decide
  have hdescent : baseEnd_626741 < baseStart_626741 := by decide
  rcases family_descends (prefixWord ++ tailWord_626741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_626745 : List Nat := [1, 2, 1, 5, 4, 1, 1, 1, 2, 4]
def baseStart_626745 : Nat := 118140960795 + 626745 * 2 ^ 59
def prefixEnd_626745 : Nat := 4983230072969 + 3 ^ 40 * 626745 * 2
def baseEnd_626745 : Nat := 214547621868170394003439

theorem tailTrace_626745 : CollatzResearch.WordTrace tailWord_626745 prefixEnd_626745 214547621868170394003439 := by
  unfold tailWord_626745
  simp only [CollatzResearch.WordTrace]
  refine ⟨22859268114417379369257689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15239512076278252912838459 22859268114417379369257689)
  ·
    refine ⟨17144451085813034526943267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22859268114417379369257689 17144451085813034526943267)
    ·
      refine ⟨25716676628719551790414901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17144451085813034526943267 25716676628719551790414901)
      ·
        refine ⟨2410938433942457980351397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 25716676628719551790414901 2410938433942457980351397)
        ·
          refine ⟨452050956364210871315887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2410938433942457980351397 452050956364210871315887)
          ·
            refine ⟨678076434546316306973831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 452050956364210871315887 678076434546316306973831)
            ·
              refine ⟨1017114651819474460460747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 678076434546316306973831 1017114651819474460460747)
              ·
                refine ⟨1525671977729211690691121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1017114651819474460460747 1525671977729211690691121)
                ·
                  refine ⟨1144253983296908768018341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1525671977729211690691121 1144253983296908768018341)
                  ·
                    refine ⟨214547621868170394003439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1144253983296908768018341 214547621868170394003439)
                    ·
                      rfl

theorem cell22_626745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 4, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 4, 1, 1, 1, 2, 4].length) (baseStart_626745 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_626745 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_626745 prefixEnd_626745 := by exact prefixLift 626745
  have htrace : WordTrace (prefixWord ++ tailWord_626745) baseStart_626745 baseEnd_626745 := by
    simpa [prefixWord, tailWord_626745, baseEnd_626745] using wordTrace_append hprefix tailTrace_626745
  have hstable : (prefixWord ++ tailWord_626745).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_626745).length < 2 ^ (prefixWord ++ tailWord_626745).sum := by decide
  have hdescent : baseEnd_626745 < baseStart_626745 := by decide
  rcases family_descends (prefixWord ++ tailWord_626745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_626852 : List Nat := [2, 3, 1, 2, 5, 1, 1, 2, 1, 4]
def baseStart_626852 : Nat := 118140960795 + 626852 * 2 ^ 59
def prefixEnd_626852 : Nat := 4983230072969 + 3 ^ 40 * 626852 * 2
def baseEnd_626852 : Nat := 214584250154857781578111

theorem tailTrace_626852 : CollatzResearch.WordTrace tailWord_626852 prefixEnd_626852 214584250154857781578111 := by
  unfold tailWord_626852
  simp only [CollatzResearch.WordTrace]
  refine ⟨11431585362514868321701405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15242113816686491095601873 11431585362514868321701405)
  ·
    refine ⟨4286844510943075620638027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11431585362514868321701405 4286844510943075620638027)
    ·
      refine ⟨6430266766414613430957041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4286844510943075620638027 6430266766414613430957041)
      ·
        refine ⟨4822700074810960073217781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6430266766414613430957041 4822700074810960073217781)
        ·
          refine ⟨452128132013527506864167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 4822700074810960073217781 452128132013527506864167)
          ·
            refine ⟨678192198020291260296251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 452128132013527506864167 678192198020291260296251)
            ·
              refine ⟨1017288297030436890444377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 678192198020291260296251 1017288297030436890444377)
              ·
                refine ⟨762966222772827667833283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1017288297030436890444377 762966222772827667833283)
                ·
                  refine ⟨1144449334159241501749925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 762966222772827667833283 1144449334159241501749925)
                  ·
                    refine ⟨214584250154857781578111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1144449334159241501749925 214584250154857781578111)
                    ·
                      rfl

theorem cell22_626852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 5, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 5, 1, 1, 2, 1, 4].length) (baseStart_626852 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_626852 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_626852 prefixEnd_626852 := by exact prefixLift 626852
  have htrace : WordTrace (prefixWord ++ tailWord_626852) baseStart_626852 baseEnd_626852 := by
    simpa [prefixWord, tailWord_626852, baseEnd_626852] using wordTrace_append hprefix tailTrace_626852
  have hstable : (prefixWord ++ tailWord_626852).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_626852).length < 2 ^ (prefixWord ++ tailWord_626852).sum := by decide
  have hdescent : baseEnd_626852 < baseStart_626852 := by decide
  rcases family_descends (prefixWord ++ tailWord_626852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_626878 : List Nat := [4, 2, 1, 1, 5, 9]
def baseStart_626878 : Nat := 118140960795 + 626878 * 2 ^ 59
def prefixEnd_626878 : Nat := 4983230072969 + 3 ^ 40 * 626878 * 2
def baseEnd_626878 : Nat := 2649298154150646671951

theorem tailTrace_626878 : CollatzResearch.WordTrace tailWord_626878 prefixEnd_626878 2649298154150646671951 := by
  unfold tailWord_626878
  simp only [CollatzResearch.WordTrace]
  refine ⟨2858014877866942885481161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15242746015290362055899525 2858014877866942885481161)
  ·
    refine ⟨2143511158400207164110871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2858014877866942885481161 2143511158400207164110871)
    ·
      refine ⟨3215266737600310746166307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2143511158400207164110871 3215266737600310746166307)
      ·
        refine ⟨4822900106400466119249461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3215266737600310746166307 4822900106400466119249461)
        ·
          refine ⟨452146884975043698679637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 4822900106400466119249461 452146884975043698679637)
          ·
            refine ⟨2649298154150646671951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 452146884975043698679637 2649298154150646671951)
            ·
              rfl

theorem cell22_626878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 5, 9].length) (baseStart_626878 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_626878 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_626878 prefixEnd_626878 := by exact prefixLift 626878
  have htrace : WordTrace (prefixWord ++ tailWord_626878) baseStart_626878 baseEnd_626878 := by
    simpa [prefixWord, tailWord_626878, baseEnd_626878] using wordTrace_append hprefix tailTrace_626878
  have hstable : (prefixWord ++ tailWord_626878).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_626878).length < 2 ^ (prefixWord ++ tailWord_626878).sum := by decide
  have hdescent : baseEnd_626878 < baseStart_626878 := by decide
  rcases family_descends (prefixWord ++ tailWord_626878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_626927 : List Nat := [1, 1, 2, 1, 6, 2, 2, 3, 1, 3]
def baseStart_626927 : Nat := 118140960795 + 626927 * 2 ^ 59
def prefixEnd_626927 : Nat := 4983230072969 + 3 ^ 40 * 626927 * 2
def baseEnd_626927 : Nat := 214609924187582585952881

theorem tailTrace_626927 : CollatzResearch.WordTrace tailWord_626927 prefixEnd_626927 214609924187582585952881 := by
  unfold tailWord_626927
  simp only [CollatzResearch.WordTrace]
  refine ⟨22865906199758024452383035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15243937466505349634922023 22865906199758024452383035)
  ·
    refine ⟨34298859299637036678574553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22865906199758024452383035 34298859299637036678574553)
    ·
      refine ⟨25724144474727777508930915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34298859299637036678574553 25724144474727777508930915)
      ·
        refine ⟨38586216712091666263396373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25724144474727777508930915 38586216712091666263396373)
        ·
          refine ⟨1808728908379296856096705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 38586216712091666263396373 1808728908379296856096705)
          ·
            refine ⟨1356546681284472642072529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1808728908379296856096705 1356546681284472642072529)
            ·
              refine ⟨1017410010963354481554397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1356546681284472642072529 1017410010963354481554397)
              ·
                refine ⟨381528754111257930582899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1017410010963354481554397 381528754111257930582899)
                ·
                  refine ⟨572293131166886895874349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 381528754111257930582899 572293131166886895874349)
                  ·
                    refine ⟨214609924187582585952881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 572293131166886895874349 214609924187582585952881)
                    ·
                      rfl

theorem cell22_626927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 2, 3, 1, 3].length) (baseStart_626927 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_626927 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_626927 prefixEnd_626927 := by exact prefixLift 626927
  have htrace : WordTrace (prefixWord ++ tailWord_626927) baseStart_626927 baseEnd_626927 := by
    simpa [prefixWord, tailWord_626927, baseEnd_626927] using wordTrace_append hprefix tailTrace_626927
  have hstable : (prefixWord ++ tailWord_626927).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_626927).length < 2 ^ (prefixWord ++ tailWord_626927).sum := by decide
  have hdescent : baseEnd_626927 < baseStart_626927 := by decide
  rcases family_descends (prefixWord ++ tailWord_626927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_626940 : List Nat := [2, 2, 2, 1, 4, 3, 1, 2, 5]
def baseStart_626940 : Nat := 118140960795 + 626940 * 2 ^ 59
def prefixEnd_626940 : Nat := 4983230072969 + 3 ^ 40 * 626940 * 2
def baseEnd_626940 : Nat := 71538124784418295125947

theorem tailTrace_626940 : CollatzResearch.WordTrace tailWord_626940 prefixEnd_626940 71538124784418295125947 := by
  unfold tailWord_626940
  simp only [CollatzResearch.WordTrace]
  refine ⟨11433190174355463836303137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15244253565807285115070849 11433190174355463836303137)
  ·
    refine ⟨8574892630766597877227353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11433190174355463836303137 8574892630766597877227353)
    ·
      refine ⟨6431169473074948407920515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8574892630766597877227353 6431169473074948407920515)
      ·
        refine ⟨9646754209612422611880773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6431169473074948407920515 9646754209612422611880773)
        ·
          refine ⟨1808766414302329239727645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9646754209612422611880773 1808766414302329239727645)
          ·
            refine ⟨678287405363373464897867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1808766414302329239727645 678287405363373464897867)
            ·
              refine ⟨1017431108045060197346801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 678287405363373464897867 1017431108045060197346801)
              ·
                refine ⟨763073331033795148010101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1017431108045060197346801 763073331033795148010101)
                ·
                  refine ⟨71538124784418295125947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 763073331033795148010101 71538124784418295125947)
                  ·
                    rfl

theorem cell22_626940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 3, 1, 2, 5].length) (baseStart_626940 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_626940 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_626940 prefixEnd_626940 := by exact prefixLift 626940
  have htrace : WordTrace (prefixWord ++ tailWord_626940) baseStart_626940 baseEnd_626940 := by
    simpa [prefixWord, tailWord_626940, baseEnd_626940] using wordTrace_append hprefix tailTrace_626940
  have hstable : (prefixWord ++ tailWord_626940).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_626940).length < 2 ^ (prefixWord ++ tailWord_626940).sum := by decide
  have hdescent : baseEnd_626940 < baseStart_626940 := by decide
  rcases family_descends (prefixWord ++ tailWord_626940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_627002 : List Nat := [3, 1, 1, 1, 4, 3, 3, 2, 4]
def baseStart_627002 : Nat := 118140960795 + 627002 * 2 ^ 59
def prefixEnd_627002 : Nat := 4983230072969 + 3 ^ 40 * 627002 * 2
def baseEnd_627002 : Nat := 71545199406769130109217

theorem tailTrace_627002 : CollatzResearch.WordTrace tailWord_627002 prefixEnd_627002 71545199406769130109217 := by
  unfold tailWord_627002
  simp only [CollatzResearch.WordTrace]
  refine ⟨5717160418621578065340815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15245761116324208174242173 5717160418621578065340815)
  ·
    refine ⟨8575740627932367098011223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5717160418621578065340815 8575740627932367098011223)
    ·
      refine ⟨12863610941898550647016835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8575740627932367098011223 12863610941898550647016835)
      ·
        refine ⟨19295416412847825970525253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12863610941898550647016835 19295416412847825970525253)
        ·
          refine ⟨3617890577408967369473485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19295416412847825970525253 3617890577408967369473485)
          ·
            refine ⟨1356708966528362763552557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3617890577408967369473485 1356708966528362763552557)
            ·
              refine ⟨508765862448136036332209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1356708966528362763552557 508765862448136036332209)
              ·
                refine ⟨381574396836102027249157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 508765862448136036332209 381574396836102027249157)
                ·
                  refine ⟨71545199406769130109217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 381574396836102027249157 71545199406769130109217)
                  ·
                    rfl

theorem cell22_627002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 3, 2, 4].length) (baseStart_627002 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_627002 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_627002 prefixEnd_627002 := by exact prefixLift 627002
  have htrace : WordTrace (prefixWord ++ tailWord_627002) baseStart_627002 baseEnd_627002 := by
    simpa [prefixWord, tailWord_627002, baseEnd_627002] using wordTrace_append hprefix tailTrace_627002
  have hstable : (prefixWord ++ tailWord_627002).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_627002).length < 2 ^ (prefixWord ++ tailWord_627002).sum := by decide
  have hdescent : baseEnd_627002 < baseStart_627002 := by decide
  rcases family_descends (prefixWord ++ tailWord_627002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_627103 : List Nat := [1, 1, 2, 5, 1, 1, 1, 2, 8]
def baseStart_627103 : Nat := 118140960795 + 627103 * 2 ^ 59
def prefixEnd_627103 : Nat := 4983230072969 + 3 ^ 40 * 627103 * 2
def baseEnd_627103 : Nat := 71556724194792264517447

theorem tailTrace_627103 : CollatzResearch.WordTrace tailWord_627103 prefixEnd_627103 71556724194792264517447 := by
  unfold tailWord_627103
  simp only [CollatzResearch.WordTrace]
  refine ⟨22872325447120406510789963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15248216964746937673859975 22872325447120406510789963)
  ·
    refine ⟨34308488170680609766184945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22872325447120406510789963 34308488170680609766184945)
    ·
      refine ⟨25731366128010457324638709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34308488170680609766184945 25731366128010457324638709)
      ·
        refine ⟨2412315574500980374184879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 25731366128010457324638709 2412315574500980374184879)
        ·
          refine ⟨3618473361751470561277319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2412315574500980374184879 3618473361751470561277319)
          ·
            refine ⟨5427710042627205841915979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3618473361751470561277319 5427710042627205841915979)
            ·
              refine ⟨8141565063940808762873969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5427710042627205841915979 8141565063940808762873969)
              ·
                refine ⟨6106173797955606572155477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8141565063940808762873969 6106173797955606572155477)
                ·
                  refine ⟨71556724194792264517447, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 6106173797955606572155477 71556724194792264517447)
                  ·
                    rfl

theorem cell22_627103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 2, 8].length) (baseStart_627103 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_627103 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_627103 prefixEnd_627103 := by exact prefixLift 627103
  have htrace : WordTrace (prefixWord ++ tailWord_627103) baseStart_627103 baseEnd_627103 := by
    simpa [prefixWord, tailWord_627103, baseEnd_627103] using wordTrace_append hprefix tailTrace_627103
  have hstable : (prefixWord ++ tailWord_627103).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_627103).length < 2 ^ (prefixWord ++ tailWord_627103).sum := by decide
  have hdescent : baseEnd_627103 < baseStart_627103 := by decide
  rcases family_descends (prefixWord ++ tailWord_627103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_627150 : List Nat := [4, 1, 1, 1, 2, 1, 1, 5, 2, 4]
def baseStart_627150 : Nat := 118140960795 + 627150 * 2 ^ 59
def prefixEnd_627150 : Nat := 4983230072969 + 3 ^ 40 * 627150 * 2
def baseEnd_627150 : Nat := 214686261644884337627197

theorem tailTrace_627150 : CollatzResearch.WordTrace tailWord_627150 prefixEnd_627150 214686261644884337627197 := by
  unfold tailWord_627150
  simp only [CollatzResearch.WordTrace]
  refine ⟨2859254959743766692218863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15249359785300089025167269 2859254959743766692218863)
  ·
    refine ⟨4288882439615650038328295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2859254959743766692218863 4288882439615650038328295)
    ·
      refine ⟨6433323659423475057492443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4288882439615650038328295 6433323659423475057492443)
      ·
        refine ⟨9649985489135212586238665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6433323659423475057492443 9649985489135212586238665)
        ·
          refine ⟨7237489116851409439678999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9649985489135212586238665 7237489116851409439678999)
          ·
            refine ⟨10856233675277114159518499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7237489116851409439678999 10856233675277114159518499)
            ·
              refine ⟨16284350512915671239277749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10856233675277114159518499 16284350512915671239277749)
              ·
                refine ⟨1526657860585844178682289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 16284350512915671239277749 1526657860585844178682289)
                ·
                  refine ⟨1144993395439383134011717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1526657860585844178682289 1144993395439383134011717)
                  ·
                    refine ⟨214686261644884337627197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1144993395439383134011717 214686261644884337627197)
                    ·
                      rfl

theorem cell22_627150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 5, 2, 4].length) (baseStart_627150 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_627150 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_627150 prefixEnd_627150 := by exact prefixLift 627150
  have htrace : WordTrace (prefixWord ++ tailWord_627150) baseStart_627150 baseEnd_627150 := by
    simpa [prefixWord, tailWord_627150, baseEnd_627150] using wordTrace_append hprefix tailTrace_627150
  have hstable : (prefixWord ++ tailWord_627150).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_627150).length < 2 ^ (prefixWord ++ tailWord_627150).sum := by decide
  have hdescent : baseEnd_627150 < baseStart_627150 := by decide
  rcases family_descends (prefixWord ++ tailWord_627150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_627242 : List Nat := [3, 1, 4, 1, 1, 3, 1, 1, 2, 5]
def baseStart_627242 : Nat := 118140960795 + 627242 * 2 ^ 59
def prefixEnd_627242 : Nat := 4983230072969 + 3 ^ 40 * 627242 * 2
def baseEnd_627242 : Nat := 214717755125026764326915

theorem tailTrace_627242 : CollatzResearch.WordTrace tailWord_627242 prefixEnd_627242 214717755125026764326915 := by
  unfold tailWord_627242
  simp only [CollatzResearch.WordTrace]
  refine ⟨5719348798404208312524995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15251596795744555500066653 5719348798404208312524995)
  ·
    refine ⟨8579023197606312468787493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5719348798404208312524995 8579023197606312468787493)
    ·
      refine ⟨1608566849551183587897655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8579023197606312468787493 1608566849551183587897655)
      ·
        refine ⟨2412850274326775381846483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1608566849551183587897655 2412850274326775381846483)
        ·
          refine ⟨3619275411490163072769725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2412850274326775381846483 3619275411490163072769725)
          ·
            refine ⟨1357228279308811152288647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3619275411490163072769725 1357228279308811152288647)
            ·
              refine ⟨2035842418963216728432971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1357228279308811152288647 2035842418963216728432971)
              ·
                refine ⟨3053763628444825092649457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2035842418963216728432971 3053763628444825092649457)
                ·
                  refine ⟨2290322721333618819487093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3053763628444825092649457 2290322721333618819487093)
                  ·
                    refine ⟨214717755125026764326915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2290322721333618819487093 214717755125026764326915)
                    ·
                      rfl

theorem cell22_627242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 1, 1, 2, 5].length) (baseStart_627242 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_627242 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_627242 prefixEnd_627242 := by exact prefixLift 627242
  have htrace : WordTrace (prefixWord ++ tailWord_627242) baseStart_627242 baseEnd_627242 := by
    simpa [prefixWord, tailWord_627242, baseEnd_627242] using wordTrace_append hprefix tailTrace_627242
  have hstable : (prefixWord ++ tailWord_627242).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_627242).length < 2 ^ (prefixWord ++ tailWord_627242).sum := by decide
  have hdescent : baseEnd_627242 < baseStart_627242 := by decide
  rcases family_descends (prefixWord ++ tailWord_627242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_627255 : List Nat := [1, 1, 3, 1, 2, 3, 3, 2, 6]
def baseStart_627255 : Nat := 118140960795 + 627255 * 2 ^ 59
def prefixEnd_627255 : Nat := 4983230072969 + 3 ^ 40 * 627255 * 2
def baseEnd_627255 : Nat := 71574068430233021250625

theorem tailTrace_627255 : CollatzResearch.WordTrace tailWord_627255 prefixEnd_627255 71574068430233021250625 := by
  unfold tailWord_627255
  simp only [CollatzResearch.WordTrace]
  refine ⟨22877869342569736470323219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15251912895046490980215479 22877869342569736470323219)
  ·
    refine ⟨34316804013854604705484829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22877869342569736470323219 34316804013854604705484829)
    ·
      refine ⟨12868801505195476764556811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34316804013854604705484829 12868801505195476764556811)
      ·
        refine ⟨19303202257793215146835217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12868801505195476764556811 19303202257793215146835217)
        ·
          refine ⟨14477401693344911360126413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19303202257793215146835217 14477401693344911360126413)
          ·
            refine ⟨5429025635004341760047405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14477401693344911360126413 5429025635004341760047405)
            ·
              refine ⟨2035884613126628160017777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5429025635004341760047405 2035884613126628160017777)
              ·
                refine ⟨1526913459844971120013333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2035884613126628160017777 1526913459844971120013333)
                ·
                  refine ⟨71574068430233021250625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1526913459844971120013333 71574068430233021250625)
                  ·
                    rfl

theorem cell22_627255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 3, 2, 6].length) (baseStart_627255 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_627255 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_627255 prefixEnd_627255 := by exact prefixLift 627255
  have htrace : WordTrace (prefixWord ++ tailWord_627255) baseStart_627255 baseEnd_627255 := by
    simpa [prefixWord, tailWord_627255, baseEnd_627255] using wordTrace_append hprefix tailTrace_627255
  have hstable : (prefixWord ++ tailWord_627255).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_627255).length < 2 ^ (prefixWord ++ tailWord_627255).sum := by decide
  have hdescent : baseEnd_627255 < baseStart_627255 := by decide
  rcases family_descends (prefixWord ++ tailWord_627255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_627257 : List Nat := [1, 2, 1, 5, 1, 1, 2, 4, 1, 4]
def baseStart_627257 : Nat := 118140960795 + 627257 * 2 ^ 59
def prefixEnd_627257 : Nat := 4983230072969 + 3 ^ 40 * 627257 * 2
def baseEnd_627257 : Nat := 214722889931571725201869

theorem tailTrace_627257 : CollatzResearch.WordTrace tailWord_627257 prefixEnd_627257 214722889931571725201869 := by
  unfold tailWord_627257
  simp only [CollatzResearch.WordTrace]
  refine ⟨22877942288562490811896025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15251961525708327207930683 22877942288562490811896025)
  ·
    refine ⟨17158456716421868108922019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22877942288562490811896025 17158456716421868108922019)
    ·
      refine ⟨25737685074632802163383029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17158456716421868108922019 25737685074632802163383029)
      ·
        refine ⟨2412907975746825202817159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 25737685074632802163383029 2412907975746825202817159)
        ·
          refine ⟨3619361963620237804225739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2412907975746825202817159 3619361963620237804225739)
          ·
            refine ⟨5429042945430356706338609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3619361963620237804225739 5429042945430356706338609)
            ·
              refine ⟨4071782209072767529753957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5429042945430356706338609 4071782209072767529753957)
              ·
                refine ⟨763459164201143911828867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4071782209072767529753957 763459164201143911828867)
                ·
                  refine ⟨1145188746301715867743301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 763459164201143911828867 1145188746301715867743301)
                  ·
                    refine ⟨214722889931571725201869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1145188746301715867743301 214722889931571725201869)
                    ·
                      rfl

theorem cell22_627257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 2, 4, 1, 4].length) (baseStart_627257 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_627257 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_627257 prefixEnd_627257 := by exact prefixLift 627257
  have htrace : WordTrace (prefixWord ++ tailWord_627257) baseStart_627257 baseEnd_627257 := by
    simpa [prefixWord, tailWord_627257, baseEnd_627257] using wordTrace_append hprefix tailTrace_627257
  have hstable : (prefixWord ++ tailWord_627257).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_627257).length < 2 ^ (prefixWord ++ tailWord_627257).sum := by decide
  have hdescent : baseEnd_627257 < baseStart_627257 := by decide
  rcases family_descends (prefixWord ++ tailWord_627257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_627274 : List Nat := [3, 1, 2, 1, 1, 4, 4, 1, 1, 4]
def baseStart_627274 : Nat := 118140960795 + 627274 * 2 ^ 59
def prefixEnd_627274 : Nat := 4983230072969 + 3 ^ 40 * 627274 * 2
def baseEnd_627274 : Nat := 214728709378989347526817

theorem tailTrace_627274 : CollatzResearch.WordTrace tailWord_627274 prefixEnd_627274 214728709378989347526817 := by
  unfold tailWord_627274
  simp only [CollatzResearch.WordTrace]
  refine ⟨5719640582375225678816219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15252374886333935143509917 5719640582375225678816219)
  ·
    refine ⟨8579460873562838518224329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5719640582375225678816219 8579460873562838518224329)
    ·
      refine ⟨6434595655172128888668247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8579460873562838518224329 6434595655172128888668247)
      ·
        refine ⟨9651893482758193333002371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6434595655172128888668247 9651893482758193333002371)
        ·
          refine ⟨14477840224137289999503557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9651893482758193333002371 14477840224137289999503557)
          ·
            refine ⟨2714595042025741874906917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14477840224137289999503557 2714595042025741874906917)
            ·
              refine ⟨508986570379826601545047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2714595042025741874906917 508986570379826601545047)
              ·
                refine ⟨763479855569739902317571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 508986570379826601545047 763479855569739902317571)
                ·
                  refine ⟨1145219783354609853476357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 763479855569739902317571 1145219783354609853476357)
                  ·
                    refine ⟨214728709378989347526817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1145219783354609853476357 214728709378989347526817)
                    ·
                      rfl

theorem cell22_627274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 4, 1, 1, 4].length) (baseStart_627274 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_627274 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_627274 prefixEnd_627274 := by exact prefixLift 627274
  have htrace : WordTrace (prefixWord ++ tailWord_627274) baseStart_627274 baseEnd_627274 := by
    simpa [prefixWord, tailWord_627274, baseEnd_627274] using wordTrace_append hprefix tailTrace_627274
  have hstable : (prefixWord ++ tailWord_627274).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_627274).length < 2 ^ (prefixWord ++ tailWord_627274).sum := by decide
  have hdescent : baseEnd_627274 < baseStart_627274 := by decide
  rcases family_descends (prefixWord ++ tailWord_627274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_627287 : List Nat := [1, 1, 3, 2, 2, 2, 3, 1, 4, 3]
def baseStart_627287 : Nat := 118140960795 + 627287 * 2 ^ 59
def prefixEnd_627287 : Nat := 4983230072969 + 3 ^ 40 * 627287 * 2
def baseEnd_627287 : Nat := 214733159544661646951777

theorem tailTrace_627287 : CollatzResearch.WordTrace tailWord_627287 prefixEnd_627287 214733159544661646951777 := by
  unfold tailWord_627287
  simp only [CollatzResearch.WordTrace]
  refine ⟨22879036478453805935488115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15252690985635870623658743 22879036478453805935488115)
  ·
    refine ⟨34318554717680708903232173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22879036478453805935488115 34318554717680708903232173)
    ·
      refine ⟨12869458019130265838712065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34318554717680708903232173 12869458019130265838712065)
      ·
        refine ⟨9652093514347699379034049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12869458019130265838712065 9652093514347699379034049)
        ·
          refine ⟨7239070135760774534275537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9652093514347699379034049 7239070135760774534275537)
          ·
            refine ⟨5429302601820580900706653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7239070135760774534275537 5429302601820580900706653)
            ·
              refine ⟨2035988475682717837764995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5429302601820580900706653 2035988475682717837764995)
              ·
                refine ⟨3053982713524076756647493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2035988475682717837764995 3053982713524076756647493)
                ·
                  refine ⟨572621758785764391871405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3053982713524076756647493 572621758785764391871405)
                  ·
                    refine ⟨214733159544661646951777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 572621758785764391871405 214733159544661646951777)
                    ·
                      rfl

theorem cell22_627287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 3, 1, 4, 3].length) (baseStart_627287 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_627287 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_627287 prefixEnd_627287 := by exact prefixLift 627287
  have htrace : WordTrace (prefixWord ++ tailWord_627287) baseStart_627287 baseEnd_627287 := by
    simpa [prefixWord, tailWord_627287, baseEnd_627287] using wordTrace_append hprefix tailTrace_627287
  have hstable : (prefixWord ++ tailWord_627287).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_627287).length < 2 ^ (prefixWord ++ tailWord_627287).sum := by decide
  have hdescent : baseEnd_627287 < baseStart_627287 := by decide
  rcases family_descends (prefixWord ++ tailWord_627287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_627300 : List Nat := [2, 3, 1, 1, 2, 2, 2, 9]
def baseStart_627300 : Nat := 118140960795 + 627300 * 2 ^ 59
def prefixEnd_627300 : Nat := 4983230072969 + 3 ^ 40 * 627300 * 2
def baseEnd_627300 : Nat := 23859734412259327375193

theorem tailTrace_627300 : CollatzResearch.WordTrace tailWord_627300 prefixEnd_627300 23859734412259327375193 := by
  unfold tailWord_627300
  simp only [CollatzResearch.WordTrace]
  refine ⟨11439755313703354577855677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15253007084937806103807569 11439755313703354577855677)
  ·
    refine ⟨4289908242638757966695879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11439755313703354577855677 4289908242638757966695879)
    ·
      refine ⟨6434862363958136950043819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4289908242638757966695879 6434862363958136950043819)
      ·
        refine ⟨9652293545937205425065729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6434862363958136950043819 9652293545937205425065729)
        ·
          refine ⟨7239220159452904068799297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9652293545937205425065729 7239220159452904068799297)
          ·
            refine ⟨5429415119589678051599473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7239220159452904068799297 5429415119589678051599473)
            ·
              refine ⟨4072061339692258538699605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5429415119589678051599473 4072061339692258538699605)
              ·
                refine ⟨23859734412259327375193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 4072061339692258538699605 23859734412259327375193)
                ·
                  rfl

theorem cell22_627300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 2, 9].length) (baseStart_627300 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_627300 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_627300 prefixEnd_627300 := by exact prefixLift 627300
  have htrace : WordTrace (prefixWord ++ tailWord_627300) baseStart_627300 baseEnd_627300 := by
    simpa [prefixWord, tailWord_627300, baseEnd_627300] using wordTrace_append hprefix tailTrace_627300
  have hstable : (prefixWord ++ tailWord_627300).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_627300).length < 2 ^ (prefixWord ++ tailWord_627300).sum := by decide
  have hdescent : baseEnd_627300 < baseStart_627300 := by decide
  rcases family_descends (prefixWord ++ tailWord_627300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_627452 : List Nat := [2, 2, 2, 1, 3, 3, 9]
def baseStart_627452 : Nat := 118140960795 + 627452 * 2 ^ 59
def prefixEnd_627452 : Nat := 4983230072969 + 3 ^ 40 * 627452 * 2
def baseEnd_627452 : Nat := 7955171941357637650973

theorem tailTrace_627452 : CollatzResearch.WordTrace tailWord_627452 prefixEnd_627452 7955171941357637650973 := by
  unfold tailWord_627452
  simp only [CollatzResearch.WordTrace]
  refine ⟨11442527261428019557622305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15256703015237359410163073 11442527261428019557622305)
  ·
    refine ⟨8581895446071014668216729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11442527261428019557622305 8581895446071014668216729)
    ·
      refine ⟨6436421584553261001162547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8581895446071014668216729 6436421584553261001162547)
      ·
        refine ⟨9654632376829891501743821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6436421584553261001162547 9654632376829891501743821)
        ·
          refine ⟨3620487141311209313153933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9654632376829891501743821 3620487141311209313153933)
          ·
            refine ⟨1357682677991703492432725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3620487141311209313153933 1357682677991703492432725)
            ·
              refine ⟨7955171941357637650973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1357682677991703492432725 7955171941357637650973)
              ·
                rfl

theorem cell22_627452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 9].length) (baseStart_627452 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_627452 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_627452 prefixEnd_627452 := by exact prefixLift 627452
  have htrace : WordTrace (prefixWord ++ tailWord_627452) baseStart_627452 baseEnd_627452 := by
    simpa [prefixWord, tailWord_627452, baseEnd_627452] using wordTrace_append hprefix tailTrace_627452
  have hstable : (prefixWord ++ tailWord_627452).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_627452).length < 2 ^ (prefixWord ++ tailWord_627452).sum := by decide
  have hdescent : baseEnd_627452 < baseStart_627452 := by decide
  rcases family_descends (prefixWord ++ tailWord_627452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_627524 : List Nat := [2, 3, 4, 2, 2, 1, 2, 1, 2, 3]
def baseStart_627524 : Nat := 118140960795 + 627524 * 2 ^ 59
def prefixEnd_627524 : Nat := 4983230072969 + 3 ^ 40 * 627524 * 2
def baseEnd_627524 : Nat := 214814289488072028776051

theorem tailTrace_627524 : CollatzResearch.WordTrace tailWord_627524 prefixEnd_627524 214814289488072028776051 := by
  unfold tailWord_627524
  simp only [CollatzResearch.WordTrace]
  refine ⟨11443840289297597705932813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15258453719063463607910417 11443840289297597705932813)
  ·
    refine ⟨4291440108486599139724805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11443840289297597705932813 4291440108486599139724805)
    ·
      refine ⟨804645020341237338698401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4291440108486599139724805 804645020341237338698401)
      ·
        refine ⟨603483765255928004023801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 804645020341237338698401 603483765255928004023801)
        ·
          refine ⟨452612823941946003017851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 603483765255928004023801 452612823941946003017851)
          ·
            refine ⟨678919235912919004526777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 452612823941946003017851 678919235912919004526777)
            ·
              refine ⟨509189426934689253395083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 678919235912919004526777 509189426934689253395083)
              ·
                refine ⟨763784140402033880092625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 509189426934689253395083 763784140402033880092625)
                ·
                  refine ⟨572838105301525410069469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 763784140402033880092625 572838105301525410069469)
                  ·
                    refine ⟨214814289488072028776051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 572838105301525410069469 214814289488072028776051)
                    ·
                      rfl

theorem cell22_627524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 2, 1, 2, 1, 2, 3].length) (baseStart_627524 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_627524 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_627524 prefixEnd_627524 := by exact prefixLift 627524
  have htrace : WordTrace (prefixWord ++ tailWord_627524) baseStart_627524 baseEnd_627524 := by
    simpa [prefixWord, tailWord_627524, baseEnd_627524] using wordTrace_append hprefix tailTrace_627524
  have hstable : (prefixWord ++ tailWord_627524).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_627524).length < 2 ^ (prefixWord ++ tailWord_627524).sum := by decide
  have hdescent : baseEnd_627524 < baseStart_627524 := by decide
  rcases family_descends (prefixWord ++ tailWord_627524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_627527 : List Nat := [1, 1, 4, 1, 2, 1, 1, 1, 2, 8]
def baseStart_627527 : Nat := 118140960795 + 627527 * 2 ^ 59
def prefixEnd_627527 : Nat := 4983230072969 + 3 ^ 40 * 627527 * 2
def baseEnd_627527 : Nat := 214815316449381020951041

theorem tailTrace_627527 : CollatzResearch.WordTrace tailWord_627527 prefixEnd_627527 214815316449381020951041 := by
  unfold tailWord_627527
  simp only [CollatzResearch.WordTrace]
  refine ⟨22887789997584326924224835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15258526665056217949483223 22887789997584326924224835)
  ·
    refine ⟨34331684996376490386337253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22887789997584326924224835 34331684996376490386337253)
    ·
      refine ⟨6437190936820591947438235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 34331684996376490386337253 6437190936820591947438235)
      ·
        refine ⟨9655786405230887921157353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6437190936820591947438235 9655786405230887921157353)
        ·
          refine ⟨7241839803923165940868015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9655786405230887921157353 7241839803923165940868015)
          ·
            refine ⟨10862759705884748911302023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7241839803923165940868015 10862759705884748911302023)
            ·
              refine ⟨16294139558827123366953035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10862759705884748911302023 16294139558827123366953035)
              ·
                refine ⟨24441209338240685050429553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16294139558827123366953035 24441209338240685050429553)
                ·
                  refine ⟨18330907003680513787822165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24441209338240685050429553 18330907003680513787822165)
                  ·
                    refine ⟨214815316449381020951041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 18330907003680513787822165 214815316449381020951041)
                    ·
                      rfl

theorem cell22_627527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 1, 2, 8].length) (baseStart_627527 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_627527 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_627527 prefixEnd_627527 := by exact prefixLift 627527
  have htrace : WordTrace (prefixWord ++ tailWord_627527) baseStart_627527 baseEnd_627527 := by
    simpa [prefixWord, tailWord_627527, baseEnd_627527] using wordTrace_append hprefix tailTrace_627527
  have hstable : (prefixWord ++ tailWord_627527).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_627527).length < 2 ^ (prefixWord ++ tailWord_627527).sum := by decide
  have hdescent : baseEnd_627527 < baseStart_627527 := by decide
  rcases family_descends (prefixWord ++ tailWord_627527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_627591 : List Nat := [1, 1, 4, 2, 3, 2, 2, 1, 1, 5]
def baseStart_627591 : Nat := 118140960795 + 627591 * 2 ^ 59
def prefixEnd_627591 : Nat := 4983230072969 + 3 ^ 40 * 627591 * 2
def baseEnd_627591 : Nat := 214837224957306187350845

theorem tailTrace_627591 : CollatzResearch.WordTrace tailWord_627591 prefixEnd_627591 214837224957306187350845 := by
  unfold tailWord_627591
  simp only [CollatzResearch.WordTrace]
  refine ⟨22890124269352465854554627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15260082846234977236369751 22890124269352465854554627)
  ·
    refine ⟨34335186404028698781831941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22890124269352465854554627 34335186404028698781831941)
    ·
      refine ⟨6437847450755381021593489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 34335186404028698781831941 6437847450755381021593489)
      ·
        refine ⟨4828385588066535766195117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6437847450755381021593489 4828385588066535766195117)
        ·
          refine ⟨1810644595524950912323169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4828385588066535766195117 1810644595524950912323169)
          ·
            refine ⟨1357983446643713184242377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1810644595524950912323169 1357983446643713184242377)
            ·
              refine ⟨1018487584982784888181783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1357983446643713184242377 1018487584982784888181783)
              ·
                refine ⟨1527731377474177332272675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1018487584982784888181783 1527731377474177332272675)
                ·
                  refine ⟨2291597066211265998409013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1527731377474177332272675 2291597066211265998409013)
                  ·
                    refine ⟨214837224957306187350845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2291597066211265998409013 214837224957306187350845)
                    ·
                      rfl

theorem cell22_627591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 2, 1, 1, 5].length) (baseStart_627591 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_627591 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_627591 prefixEnd_627591 := by exact prefixLift 627591
  have htrace : WordTrace (prefixWord ++ tailWord_627591) baseStart_627591 baseEnd_627591 := by
    simpa [prefixWord, tailWord_627591, baseEnd_627591] using wordTrace_append hprefix tailTrace_627591
  have hstable : (prefixWord ++ tailWord_627591).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_627591).length < 2 ^ (prefixWord ++ tailWord_627591).sum := by decide
  have hdescent : baseEnd_627591 < baseStart_627591 := by decide
  rcases family_descends (prefixWord ++ tailWord_627591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_627612 : List Nat := [2, 2, 3, 3, 3, 1, 2, 1, 1, 4]
def baseStart_627612 : Nat := 118140960795 + 627612 * 2 ^ 59
def prefixEnd_627612 : Nat := 4983230072969 + 3 ^ 40 * 627612 * 2
def baseEnd_627612 : Nat := 214844413686469132575781

theorem tailTrace_627612 : CollatzResearch.WordTrace tailWord_627612 prefixEnd_627612 214844413686469132575781 := by
  unfold tailWord_627612
  simp only [CollatzResearch.WordTrace]
  refine ⟨11445445101138193220534545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15260593468184257627379393 11445445101138193220534545)
  ·
    refine ⟨8584083825853644915400909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11445445101138193220534545 8584083825853644915400909)
    ·
      refine ⟨3219031434695116843275341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8584083825853644915400909 3219031434695116843275341)
      ·
        refine ⟨1207136788010668816228253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3219031434695116843275341 1207136788010668816228253)
        ·
          refine ⟨452676295504000806085595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1207136788010668816228253 452676295504000806085595)
          ·
            refine ⟨679014443256001209128393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 452676295504000806085595 679014443256001209128393)
            ·
              refine ⟨509260832442000906846295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 679014443256001209128393 509260832442000906846295)
              ·
                refine ⟨763891248663001360269443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 509260832442000906846295 763891248663001360269443)
                ·
                  refine ⟨1145836872994502040404165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 763891248663001360269443 1145836872994502040404165)
                  ·
                    refine ⟨214844413686469132575781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1145836872994502040404165 214844413686469132575781)
                    ·
                      rfl

theorem cell22_627612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 3, 1, 2, 1, 1, 4].length) (baseStart_627612 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_627612 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_627612 prefixEnd_627612 := by exact prefixLift 627612
  have htrace : WordTrace (prefixWord ++ tailWord_627612) baseStart_627612 baseEnd_627612 := by
    simpa [prefixWord, tailWord_627612, baseEnd_627612] using wordTrace_append hprefix tailTrace_627612
  have hstable : (prefixWord ++ tailWord_627612).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_627612).length < 2 ^ (prefixWord ++ tailWord_627612).sum := by decide
  have hdescent : baseEnd_627612 < baseStart_627612 := by decide
  rcases family_descends (prefixWord ++ tailWord_627612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_627661 : List Nat := [1, 6, 3, 1, 2, 1, 1, 3, 4]
def baseStart_627661 : Nat := 118140960795 + 627661 * 2 ^ 59
def prefixEnd_627661 : Nat := 4983230072969 + 3 ^ 40 * 627661 * 2
def baseEnd_627661 : Nat := 71620395795949779366877

theorem tailTrace_627661 : CollatzResearch.WordTrace tailWord_627661 prefixEnd_627661 71620395795949779366877 := by
  unfold tailWord_627661
  simp only [CollatzResearch.WordTrace]
  refine ⟨22892677379098867809602837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15261784919399245206401891 22892677379098867809602837)
  ·
    refine ⟨1073094252145259428575133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 22892677379098867809602837 1073094252145259428575133)
    ·
      refine ⟨402410344554472285715675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1073094252145259428575133 402410344554472285715675)
      ·
        refine ⟨603615516831708428573513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 402410344554472285715675 603615516831708428573513)
        ·
          refine ⟨452711637623781321430135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 603615516831708428573513 452711637623781321430135)
          ·
            refine ⟨679067456435671982145203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 452711637623781321430135 679067456435671982145203)
            ·
              refine ⟨1018601184653507973217805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 679067456435671982145203 1018601184653507973217805)
              ·
                refine ⟨381975444245065489956677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1018601184653507973217805 381975444245065489956677)
                ·
                  refine ⟨71620395795949779366877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 381975444245065489956677 71620395795949779366877)
                  ·
                    rfl

theorem cell22_627661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 2, 1, 1, 3, 4].length) (baseStart_627661 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_627661 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_627661 prefixEnd_627661 := by exact prefixLift 627661
  have htrace : WordTrace (prefixWord ++ tailWord_627661) baseStart_627661 baseEnd_627661 := by
    simpa [prefixWord, tailWord_627661, baseEnd_627661] using wordTrace_append hprefix tailTrace_627661
  have hstable : (prefixWord ++ tailWord_627661).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_627661).length < 2 ^ (prefixWord ++ tailWord_627661).sum := by decide
  have hdescent : baseEnd_627661 < baseStart_627661 := by decide
  rcases family_descends (prefixWord ++ tailWord_627661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_627666 : List Nat := [3, 2, 2, 3, 1, 1, 1, 2, 7]
def baseStart_627666 : Nat := 118140960795 + 627666 * 2 ^ 59
def prefixEnd_627666 : Nat := 4983230072969 + 3 ^ 40 * 627666 * 2
def baseEnd_627666 : Nat := 71620966330010330575205

theorem tailTrace_627666 : CollatzResearch.WordTrace tailWord_627666 prefixEnd_627666 71620966330010330575205 := by
  unfold tailWord_627666
  simp only [CollatzResearch.WordTrace]
  refine ⟨5723214936020188415883713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15261906496053835775689901 5723214936020188415883713)
  ·
    refine ⟨4292411202015141311912785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5723214936020188415883713 4292411202015141311912785)
    ·
      refine ⟨3219308401511355983934589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4292411202015141311912785 3219308401511355983934589)
      ·
        refine ⟨1207240650566758493975471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3219308401511355983934589 1207240650566758493975471)
        ·
          refine ⟨1810860975850137740963207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1207240650566758493975471 1810860975850137740963207)
          ·
            refine ⟨2716291463775206611444811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1810860975850137740963207 2716291463775206611444811)
            ·
              refine ⟨4074437195662809917167217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2716291463775206611444811 4074437195662809917167217)
              ·
                refine ⟨3055827896747107437875413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4074437195662809917167217 3055827896747107437875413)
                ·
                  refine ⟨71620966330010330575205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3055827896747107437875413 71620966330010330575205)
                  ·
                    rfl

theorem cell22_627666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 1, 2, 7].length) (baseStart_627666 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_627666 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_627666 prefixEnd_627666 := by exact prefixLift 627666
  have htrace : WordTrace (prefixWord ++ tailWord_627666) baseStart_627666 baseEnd_627666 := by
    simpa [prefixWord, tailWord_627666, baseEnd_627666] using wordTrace_append hprefix tailTrace_627666
  have hstable : (prefixWord ++ tailWord_627666).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_627666).length < 2 ^ (prefixWord ++ tailWord_627666).sum := by decide
  have hdescent : baseEnd_627666 < baseStart_627666 := by decide
  rcases family_descends (prefixWord ++ tailWord_627666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_627687 : List Nat := [1, 1, 5, 2, 2, 2, 3, 2, 1, 3]
def baseStart_627687 : Nat := 118140960795 + 627687 * 2 ^ 59
def prefixEnd_627687 : Nat := 4983230072969 + 3 ^ 40 * 627687 * 2
def baseEnd_627687 : Nat := 214870087719193936950551

theorem tailTrace_627687 : CollatzResearch.WordTrace tailWord_627687 prefixEnd_627687 214870087719193936950551 := by
  unfold tailWord_627687
  simp only [CollatzResearch.WordTrace]
  refine ⟨22893625677004674250049315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15262417118003116166699543 22893625677004674250049315)
  ·
    refine ⟨34340438515507011375073973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22893625677004674250049315 34340438515507011375073973)
    ·
      refine ⟨3219416110828782316413185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 34340438515507011375073973 3219416110828782316413185)
      ·
        refine ⟨2414562083121586737309889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3219416110828782316413185 2414562083121586737309889)
        ·
          refine ⟨1810921562341190052982417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2414562083121586737309889 1810921562341190052982417)
          ·
            refine ⟨1358191171755892539736813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1810921562341190052982417 1358191171755892539736813)
            ·
              refine ⟨509321689408459702401305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1358191171755892539736813 509321689408459702401305)
              ·
                refine ⟨381991267056344776800979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 509321689408459702401305 381991267056344776800979)
                ·
                  refine ⟨572986900584517165201469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 381991267056344776800979 572986900584517165201469)
                  ·
                    refine ⟨214870087719193936950551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 572986900584517165201469 214870087719193936950551)
                    ·
                      rfl

theorem cell22_627687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 3, 2, 1, 3].length) (baseStart_627687 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_627687 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_627687 prefixEnd_627687 := by exact prefixLift 627687
  have htrace : WordTrace (prefixWord ++ tailWord_627687) baseStart_627687 baseEnd_627687 := by
    simpa [prefixWord, tailWord_627687, baseEnd_627687] using wordTrace_append hprefix tailTrace_627687
  have hstable : (prefixWord ++ tailWord_627687).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_627687).length < 2 ^ (prefixWord ++ tailWord_627687).sum := by decide
  have hdescent : baseEnd_627687 < baseStart_627687 := by decide
  rcases family_descends (prefixWord ++ tailWord_627687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_627713 : List Nat := [1, 2, 4, 1, 2, 2, 3, 2, 1, 4]
def baseStart_627713 : Nat := 118140960795 + 627713 * 2 ^ 59
def prefixEnd_627713 : Nat := 4983230072969 + 3 ^ 40 * 627713 * 2
def baseEnd_627713 : Nat := 214878988050538535800471

theorem tailTrace_627713 : CollatzResearch.WordTrace tailWord_627713 prefixEnd_627713 214878988050538535800471 := by
  unfold tailWord_627713
  simp only [CollatzResearch.WordTrace]
  refine ⟨22894573974910480690495793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15263049316606987126997195 22894573974910480690495793)
  ·
    refine ⟨17170930481182860517871845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22894573974910480690495793 17170930481182860517871845)
    ·
      refine ⟨3219549465221786347100971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17170930481182860517871845 3219549465221786347100971)
      ·
        refine ⟨4829324197832679520651457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3219549465221786347100971 4829324197832679520651457)
        ·
          refine ⟨3621993148374509640488593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4829324197832679520651457 3621993148374509640488593)
          ·
            refine ⟨2716494861280882230366445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3621993148374509640488593 2716494861280882230366445)
            ·
              refine ⟨1018685572980330836387417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2716494861280882230366445 1018685572980330836387417)
              ·
                refine ⟨764014179735248127290563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1018685572980330836387417 764014179735248127290563)
                ·
                  refine ⟨1146021269602872190935845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 764014179735248127290563 1146021269602872190935845)
                  ·
                    refine ⟨214878988050538535800471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1146021269602872190935845 214878988050538535800471)
                    ·
                      rfl

theorem cell22_627713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 3, 2, 1, 4].length) (baseStart_627713 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_627713 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_627713 prefixEnd_627713 := by exact prefixLift 627713
  have htrace : WordTrace (prefixWord ++ tailWord_627713) baseStart_627713 baseEnd_627713 := by
    simpa [prefixWord, tailWord_627713, baseEnd_627713] using wordTrace_append hprefix tailTrace_627713
  have hstable : (prefixWord ++ tailWord_627713).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_627713).length < 2 ^ (prefixWord ++ tailWord_627713).sum := by decide
  have hdescent : baseEnd_627713 < baseStart_627713 := by decide
  rcases family_descends (prefixWord ++ tailWord_627713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_627726 : List Nat := [4, 1, 1, 2, 2, 2, 1, 1, 3, 5]
def baseStart_627726 : Nat := 118140960795 + 627726 * 2 ^ 59
def prefixEnd_627726 : Nat := 4983230072969 + 3 ^ 40 * 627726 * 2
def baseEnd_627726 : Nat := 214883438216210835225431

theorem tailTrace_627726 : CollatzResearch.WordTrace tailWord_627726 prefixEnd_627726 214883438216210835225431 := by
  unfold tailWord_627726
  simp only [CollatzResearch.WordTrace]
  refine ⟨2861881015482922988839879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15263365415908922607146021 2861881015482922988839879)
  ·
    refine ⟨4292821523224384483259819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2861881015482922988839879 4292821523224384483259819)
    ·
      refine ⟨6439232284836576724889729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4292821523224384483259819 6439232284836576724889729)
      ·
        refine ⟨4829424213627432543667297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6439232284836576724889729 4829424213627432543667297)
        ·
          refine ⟨3622068160220574407750473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4829424213627432543667297 3622068160220574407750473)
          ·
            refine ⟨2716551120165430805812855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3622068160220574407750473 2716551120165430805812855)
            ·
              refine ⟨4074826680248146208719283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2716551120165430805812855 4074826680248146208719283)
              ·
                refine ⟨6112240020372219313078925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4074826680248146208719283 6112240020372219313078925)
                ·
                  refine ⟨2292090007639582242404597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6112240020372219313078925 2292090007639582242404597)
                  ·
                    refine ⟨214883438216210835225431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2292090007639582242404597 214883438216210835225431)
                    ·
                      rfl

theorem cell22_627726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 1, 1, 3, 5].length) (baseStart_627726 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_627726 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_627726 prefixEnd_627726 := by exact prefixLift 627726
  have htrace : WordTrace (prefixWord ++ tailWord_627726) baseStart_627726 baseEnd_627726 := by
    simpa [prefixWord, tailWord_627726, baseEnd_627726] using wordTrace_append hprefix tailTrace_627726
  have hstable : (prefixWord ++ tailWord_627726).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_627726).length < 2 ^ (prefixWord ++ tailWord_627726).sum := by decide
  have hdescent : baseEnd_627726 < baseStart_627726 := by decide
  rcases family_descends (prefixWord ++ tailWord_627726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_627743 : List Nat := [1, 1, 2, 4, 1, 3, 1, 4, 2, 3]
def baseStart_627743 : Nat := 118140960795 + 627743 * 2 ^ 59
def prefixEnd_627743 : Nat := 4983230072969 + 3 ^ 40 * 627743 * 2
def baseEnd_627743 : Nat := 214889257663628457550379

theorem tailTrace_627743 : CollatzResearch.WordTrace tailWord_627743 prefixEnd_627743 214889257663628457550379 := by
  unfold tailWord_627743
  simp only [CollatzResearch.WordTrace]
  refine ⟨22895668164801795814087883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15263778776534530542725255 22895668164801795814087883)
  ·
    refine ⟨34343502247202693721131825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22895668164801795814087883 34343502247202693721131825)
    ·
      refine ⟨25757626685402020290848869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34343502247202693721131825 25757626685402020290848869)
      ·
        refine ⟨4829555003512878804534163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25757626685402020290848869 4829555003512878804534163)
        ·
          refine ⟨7244332505269318206801245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4829555003512878804534163 7244332505269318206801245)
          ·
            refine ⟨2716624689475994327550467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7244332505269318206801245 2716624689475994327550467)
            ·
              refine ⟨4074937034213991491325701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2716624689475994327550467 4074937034213991491325701)
              ·
                refine ⟨764050693915123404623569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4074937034213991491325701 764050693915123404623569)
                ·
                  refine ⟨573038020436342553467677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 764050693915123404623569 573038020436342553467677)
                  ·
                    refine ⟨214889257663628457550379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 573038020436342553467677 214889257663628457550379)
                    ·
                      rfl

theorem cell22_627743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 1, 4, 2, 3].length) (baseStart_627743 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_627743 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_627743 prefixEnd_627743 := by exact prefixLift 627743
  have htrace : WordTrace (prefixWord ++ tailWord_627743) baseStart_627743 baseEnd_627743 := by
    simpa [prefixWord, tailWord_627743, baseEnd_627743] using wordTrace_append hprefix tailTrace_627743
  have hstable : (prefixWord ++ tailWord_627743).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_627743).length < 2 ^ (prefixWord ++ tailWord_627743).sum := by decide
  have hdescent : baseEnd_627743 < baseStart_627743 := by decide
  rcases family_descends (prefixWord ++ tailWord_627743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_627745 : List Nat := [1, 2, 3, 2, 3, 1, 4, 2, 4]
def baseStart_627745 : Nat := 118140960795 + 627745 * 2 ^ 59
def prefixEnd_627745 : Nat := 4983230072969 + 3 ^ 40 * 627745 * 2
def baseEnd_627745 : Nat := 71629980768167039666791

theorem tailTrace_627745 : CollatzResearch.WordTrace tailWord_627745 prefixEnd_627745 71629980768167039666791 := by
  unfold tailWord_627745
  simp only [CollatzResearch.WordTrace]
  refine ⟨22895741110794550155660689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15263827407196366770440459 22895741110794550155660689)
  ·
    refine ⟨17171805833095912616745517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22895741110794550155660689 17171805833095912616745517)
    ·
      refine ⟨6439427187410967231279569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17171805833095912616745517 6439427187410967231279569)
      ·
        refine ⟨4829570390558225423459677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6439427187410967231279569 4829570390558225423459677)
        ·
          refine ⟨1811088896459334533797379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4829570390558225423459677 1811088896459334533797379)
          ·
            refine ⟨2716633344689001800696069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1811088896459334533797379 2716633344689001800696069)
            ·
              refine ⟨509368752129187837630513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2716633344689001800696069 509368752129187837630513)
              ·
                refine ⟨382026564096890878222885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 509368752129187837630513 382026564096890878222885)
                ·
                  refine ⟨71629980768167039666791, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 382026564096890878222885 71629980768167039666791)
                  ·
                    rfl

theorem cell22_627745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 4, 2, 4].length) (baseStart_627745 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_627745 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_627745 prefixEnd_627745 := by exact prefixLift 627745
  have htrace : WordTrace (prefixWord ++ tailWord_627745) baseStart_627745 baseEnd_627745 := by
    simpa [prefixWord, tailWord_627745, baseEnd_627745] using wordTrace_append hprefix tailTrace_627745
  have hstable : (prefixWord ++ tailWord_627745).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_627745).length < 2 ^ (prefixWord ++ tailWord_627745).sum := by decide
  have hdescent : baseEnd_627745 < baseStart_627745 := by decide
  rcases family_descends (prefixWord ++ tailWord_627745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_627773 : List Nat := [1, 4, 1, 3, 1, 3, 3, 6]
def baseStart_627773 : Nat := 118140960795 + 627773 * 2 ^ 59
def prefixEnd_627773 : Nat := 4983230072969 + 3 ^ 40 * 627773 * 2
def baseEnd_627773 : Nat := 23877725252968708811143

theorem tailTrace_627773 : CollatzResearch.WordTrace tailWord_627773 prefixEnd_627773 23877725252968708811143 := by
  unfold tailWord_627773
  simp only [CollatzResearch.WordTrace]
  refine ⟨22896762354693110937679973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15264508236462073958453315 22896762354693110937679973)
  ·
    refine ⟨4293142941504958300814995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22896762354693110937679973 4293142941504958300814995)
    ·
      refine ⟨6439714412257437451222493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4293142941504958300814995 6439714412257437451222493)
      ·
        refine ⟨2414892904596539044208435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6439714412257437451222493 2414892904596539044208435)
        ·
          refine ⟨3622339356894808566312653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2414892904596539044208435 3622339356894808566312653)
          ·
            refine ⟨1358377258835553212367245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3622339356894808566312653 1358377258835553212367245)
            ·
              refine ⟨509391472063332454637717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1358377258835553212367245 509391472063332454637717)
              ·
                refine ⟨23877725252968708811143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 509391472063332454637717 23877725252968708811143)
                ·
                  rfl

theorem cell22_627773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 3, 6].length) (baseStart_627773 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_627773 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_627773 prefixEnd_627773 := by exact prefixLift 627773
  have htrace : WordTrace (prefixWord ++ tailWord_627773) baseStart_627773 baseEnd_627773 := by
    simpa [prefixWord, tailWord_627773, baseEnd_627773] using wordTrace_append hprefix tailTrace_627773
  have hstable : (prefixWord ++ tailWord_627773).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_627773).length < 2 ^ (prefixWord ++ tailWord_627773).sum := by decide
  have hdescent : baseEnd_627773 < baseStart_627773 := by decide
  rcases family_descends (prefixWord ++ tailWord_627773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_627801 : List Nat := [1, 2, 1, 2, 2, 1, 2, 6, 5]
def baseStart_627801 : Nat := 118140960795 + 627801 * 2 ^ 59
def prefixEnd_627801 : Nat := 4983230072969 + 3 ^ 40 * 627801 * 2
def baseEnd_627801 : Nat := 71636370749645213200067

theorem tailTrace_627801 : CollatzResearch.WordTrace tailWord_627801 prefixEnd_627801 71636370749645213200067 := by
  unfold tailWord_627801
  simp only [CollatzResearch.WordTrace]
  refine ⟨22897783598591671719699257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15265189065727781146466171 22897783598591671719699257)
  ·
    refine ⟨17173337698943753789774443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22897783598591671719699257 17173337698943753789774443)
    ·
      refine ⟨25760006548415630684661665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17173337698943753789774443 25760006548415630684661665)
      ·
        refine ⟨19320004911311723013496249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25760006548415630684661665 19320004911311723013496249)
        ·
          refine ⟨14490003683483792260122187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19320004911311723013496249 14490003683483792260122187)
          ·
            refine ⟨21735005525225688390183281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14490003683483792260122187 21735005525225688390183281)
            ·
              refine ⟨16301254143919266292637461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21735005525225688390183281 16301254143919266292637461)
              ·
                refine ⟨764121287996215607467381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 16301254143919266292637461 764121287996215607467381)
                ·
                  refine ⟨71636370749645213200067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 764121287996215607467381 71636370749645213200067)
                  ·
                    rfl

theorem cell22_627801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 6, 5].length) (baseStart_627801 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_627801 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_627801 prefixEnd_627801 := by exact prefixLift 627801
  have htrace : WordTrace (prefixWord ++ tailWord_627801) baseStart_627801 baseEnd_627801 := by
    simpa [prefixWord, tailWord_627801, baseEnd_627801] using wordTrace_append hprefix tailTrace_627801
  have hstable : (prefixWord ++ tailWord_627801).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_627801).length < 2 ^ (prefixWord ++ tailWord_627801).sum := by decide
  have hdescent : baseEnd_627801 < baseStart_627801 := by decide
  rcases family_descends (prefixWord ++ tailWord_627801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_627861 : List Nat := [1, 3, 2, 1, 1, 1, 2, 1, 5, 5]
def baseStart_627861 : Nat := 118140960795 + 627861 * 2 ^ 59
def prefixEnd_627861 : Nat := 4983230072969 + 3 ^ 40 * 627861 * 2
def baseEnd_627861 : Nat := 214929651475115483100017

theorem tailTrace_627861 : CollatzResearch.WordTrace tailWord_627861 prefixEnd_627861 214929651475115483100017 := by
  unfold tailWord_627861
  simp only [CollatzResearch.WordTrace]
  refine ⟨22899971978374301966883437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15266647985582867977922291 22899971978374301966883437)
  ·
    refine ⟨8587489491890363237581289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22899971978374301966883437 8587489491890363237581289)
    ·
      refine ⟨6440617118917772428185967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8587489491890363237581289 6440617118917772428185967)
      ·
        refine ⟨9660925678376658642278951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6440617118917772428185967 9660925678376658642278951)
        ·
          refine ⟨14491388517564987963418427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9660925678376658642278951 14491388517564987963418427)
          ·
            refine ⟨21737082776347481945127641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14491388517564987963418427 21737082776347481945127641)
            ·
              refine ⟨16302812082260611458845731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21737082776347481945127641 16302812082260611458845731)
              ·
                refine ⟨24454218123390917188268597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16302812082260611458845731 24454218123390917188268597)
                ·
                  refine ⟨2292582949067898486400181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 24454218123390917188268597 2292582949067898486400181)
                  ·
                    refine ⟨214929651475115483100017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2292582949067898486400181 214929651475115483100017)
                    ·
                      rfl

theorem cell22_627861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 1, 5, 5].length) (baseStart_627861 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_627861 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_627861 prefixEnd_627861 := by exact prefixLift 627861
  have htrace : WordTrace (prefixWord ++ tailWord_627861) baseStart_627861 baseEnd_627861 := by
    simpa [prefixWord, tailWord_627861, baseEnd_627861] using wordTrace_append hprefix tailTrace_627861
  have hstable : (prefixWord ++ tailWord_627861).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_627861).length < 2 ^ (prefixWord ++ tailWord_627861).sum := by decide
  have hdescent : baseEnd_627861 < baseStart_627861 := by decide
  rcases family_descends (prefixWord ++ tailWord_627861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_627863 : List Nat := [1, 1, 3, 3, 3, 1, 3, 1, 6]
def baseStart_627863 : Nat := 118140960795 + 627863 * 2 ^ 59
def prefixEnd_627863 : Nat := 4983230072969 + 3 ^ 40 * 627863 * 2
def baseEnd_627863 : Nat := 71643445371996048183337

theorem tailTrace_627863 : CollatzResearch.WordTrace tailWord_627863 prefixEnd_627863 71643445371996048183337 := by
  unfold tailWord_627863
  simp only [CollatzResearch.WordTrace]
  refine ⟨22900044924367056308456243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15266696616244704205637495 22900044924367056308456243)
  ·
    refine ⟨34350067386550584462684365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22900044924367056308456243 34350067386550584462684365)
    ·
      refine ⟨12881275269956469173506637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34350067386550584462684365 12881275269956469173506637)
      ·
        refine ⟨4830478226233675940064989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12881275269956469173506637 4830478226233675940064989)
        ·
          refine ⟨1811429334837628477524371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4830478226233675940064989 1811429334837628477524371)
          ·
            refine ⟨2717144002256442716286557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1811429334837628477524371 2717144002256442716286557)
            ·
              refine ⟨1018929000846166018607459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2717144002256442716286557 1018929000846166018607459)
              ·
                refine ⟨1528393501269249027911189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1018929000846166018607459 1528393501269249027911189)
                ·
                  refine ⟨71643445371996048183337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1528393501269249027911189 71643445371996048183337)
                  ·
                    rfl

theorem cell22_627863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 3, 1, 6].length) (baseStart_627863 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_627863 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_627863 prefixEnd_627863 := by exact prefixLift 627863
  have htrace : WordTrace (prefixWord ++ tailWord_627863) baseStart_627863 baseEnd_627863 := by
    simpa [prefixWord, tailWord_627863, baseEnd_627863] using wordTrace_append hprefix tailTrace_627863
  have hstable : (prefixWord ++ tailWord_627863).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_627863).length < 2 ^ (prefixWord ++ tailWord_627863).sum := by decide
  have hdescent : baseEnd_627863 < baseStart_627863 := by decide
  rcases family_descends (prefixWord ++ tailWord_627863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_627882 : List Nat := [3, 1, 5, 1, 1, 1, 3, 2, 1, 4]
def baseStart_627882 : Nat := 118140960795 + 627882 * 2 ^ 59
def prefixEnd_627882 : Nat := 4983230072969 + 3 ^ 40 * 627882 * 2
def baseEnd_627882 : Nat := 214936840204278428324953

theorem tailTrace_627882 : CollatzResearch.WordTrace tailWord_627882 prefixEnd_627882 214936840204278428324953 := by
  unfold tailWord_627882
  simp only [CollatzResearch.WordTrace]
  refine ⟨5725184477824555638349475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15267158607532148368931933 5725184477824555638349475)
  ·
    refine ⟨8587776716736833457524213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5725184477824555638349475 8587776716736833457524213)
    ·
      refine ⟨805104067194078136642895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 8587776716736833457524213 805104067194078136642895)
      ·
        refine ⟨1207656100791117204964343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 805104067194078136642895 1207656100791117204964343)
        ·
          refine ⟨1811484151186675807446515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1207656100791117204964343 1811484151186675807446515)
          ·
            refine ⟨2717226226780013711169773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1811484151186675807446515 2717226226780013711169773)
            ·
              refine ⟨1018959835042505141688665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2717226226780013711169773 1018959835042505141688665)
              ·
                refine ⟨764219876281878856266499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1018959835042505141688665 764219876281878856266499)
                ·
                  refine ⟨1146329814422818284399749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 764219876281878856266499 1146329814422818284399749)
                  ·
                    refine ⟨214936840204278428324953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1146329814422818284399749 214936840204278428324953)
                    ·
                      rfl

theorem cell22_627882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 3, 2, 1, 4].length) (baseStart_627882 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_627882 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_627882 prefixEnd_627882 := by exact prefixLift 627882
  have htrace : WordTrace (prefixWord ++ tailWord_627882) baseStart_627882 baseEnd_627882 := by
    simpa [prefixWord, tailWord_627882, baseEnd_627882] using wordTrace_append hprefix tailTrace_627882
  have hstable : (prefixWord ++ tailWord_627882).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_627882).length < 2 ^ (prefixWord ++ tailWord_627882).sum := by decide
  have hdescent : baseEnd_627882 < baseStart_627882 := by decide
  rcases family_descends (prefixWord ++ tailWord_627882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_627891 : List Nat := [1, 1, 1, 2, 3, 2, 4, 8]
def baseStart_627891 : Nat := 118140960795 + 627891 * 2 ^ 59
def prefixEnd_627891 : Nat := 4983230072969 + 3 ^ 40 * 627891 * 2
def baseEnd_627891 : Nat := 23882213454245044983325

theorem tailTrace_627891 : CollatzResearch.WordTrace tailWord_627891 prefixEnd_627891 23882213454245044983325 := by
  unfold tailWord_627891
  simp only [CollatzResearch.WordTrace]
  refine ⟨22901066168265617090475527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15267377445510411393650351 22901066168265617090475527)
  ·
    refine ⟨34351599252398425635713291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22901066168265617090475527 34351599252398425635713291)
    ·
      refine ⟨51527398878597638453569937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34351599252398425635713291 51527398878597638453569937)
      ·
        refine ⟨38645549158948228840177453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51527398878597638453569937 38645549158948228840177453)
        ·
          refine ⟨14492080934605585815066545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38645549158948228840177453 14492080934605585815066545)
          ·
            refine ⟨10869060700954189361299909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14492080934605585815066545 10869060700954189361299909)
            ·
              refine ⟨2037948881428910505243733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10869060700954189361299909 2037948881428910505243733)
              ·
                refine ⟨23882213454245044983325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2037948881428910505243733 23882213454245044983325)
                ·
                  rfl

theorem cell22_627891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 4, 8].length) (baseStart_627891 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_627891 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_627891 prefixEnd_627891 := by exact prefixLift 627891
  have htrace : WordTrace (prefixWord ++ tailWord_627891) baseStart_627891 baseEnd_627891 := by
    simpa [prefixWord, tailWord_627891, baseEnd_627891] using wordTrace_append hprefix tailTrace_627891
  have hstable : (prefixWord ++ tailWord_627891).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_627891).length < 2 ^ (prefixWord ++ tailWord_627891).sum := by decide
  have hdescent : baseEnd_627891 < baseStart_627891 := by decide
  rcases family_descends (prefixWord ++ tailWord_627891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_627908 : List Nat := [2, 3, 3, 1, 3, 10]
def baseStart_627908 : Nat := 118140960795 + 627908 * 2 ^ 59
def prefixEnd_627908 : Nat := 4983230072969 + 3 ^ 40 * 627908 * 2
def baseEnd_627908 : Nat := 2653651117723741076233

theorem tailTrace_627908 : CollatzResearch.WordTrace tailWord_627908 prefixEnd_627908 2653651117723741076233 := by
  unfold tailWord_627908
  simp only [CollatzResearch.WordTrace]
  refine ⟨11450843104602014496922189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15267790806136019329229585 11450843104602014496922189)
  ·
    refine ⟨4294066164225755436345821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11450843104602014496922189 4294066164225755436345821)
    ·
      refine ⟨1610274811584658288629683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4294066164225755436345821 1610274811584658288629683)
      ·
        refine ⟨2415412217376987432944525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1610274811584658288629683 2415412217376987432944525)
        ·
          refine ⟨905779581516370287354197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2415412217376987432944525 905779581516370287354197)
          ·
            refine ⟨2653651117723741076233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 905779581516370287354197 2653651117723741076233)
            ·
              rfl

theorem cell22_627908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 10].length) (baseStart_627908 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_627908 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_627908 prefixEnd_627908 := by exact prefixLift 627908
  have htrace : WordTrace (prefixWord ++ tailWord_627908) baseStart_627908 baseEnd_627908 := by
    simpa [prefixWord, tailWord_627908, baseEnd_627908] using wordTrace_append hprefix tailTrace_627908
  have hstable : (prefixWord ++ tailWord_627908).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_627908).length < 2 ^ (prefixWord ++ tailWord_627908).sum := by decide
  have hdescent : baseEnd_627908 < baseStart_627908 := by decide
  rcases family_descends (prefixWord ++ tailWord_627908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_627925 : List Nat := [1, 3, 2, 4, 1, 3, 1, 7]
def baseStart_627925 : Nat := 118140960795 + 627925 * 2 ^ 59
def prefixEnd_627925 : Nat := 4983230072969 + 3 ^ 40 * 627925 * 2
def baseEnd_627925 : Nat := 23883506664782294388869

theorem tailTrace_627925 : CollatzResearch.WordTrace tailWord_627925 prefixEnd_627925 23883506664782294388869 := by
  unfold tailWord_627925
  simp only [CollatzResearch.WordTrace]
  refine ⟨22902306250142440897213229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15268204166761627264808819 22902306250142440897213229)
  ·
    refine ⟨8588364843803415336454961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22902306250142440897213229 8588364843803415336454961)
    ·
      refine ⟨6441273632852561502341221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8588364843803415336454961 6441273632852561502341221)
      ·
        refine ⟨1207738806159855281688979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6441273632852561502341221 1207738806159855281688979)
        ·
          refine ⟨1811608209239782922533469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1207738806159855281688979 1811608209239782922533469)
          ·
            refine ⟨679353078464918595950051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1811608209239782922533469 679353078464918595950051)
            ·
              refine ⟨1019029617697377893925077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 679353078464918595950051 1019029617697377893925077)
              ·
                refine ⟨23883506664782294388869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1019029617697377893925077 23883506664782294388869)
                ·
                  rfl

theorem cell22_627925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 3, 1, 7].length) (baseStart_627925 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_627925 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_627925 prefixEnd_627925 := by exact prefixLift 627925
  have htrace : WordTrace (prefixWord ++ tailWord_627925) baseStart_627925 baseEnd_627925 := by
    simpa [prefixWord, tailWord_627925, baseEnd_627925] using wordTrace_append hprefix tailTrace_627925
  have hstable : (prefixWord ++ tailWord_627925).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_627925).length < 2 ^ (prefixWord ++ tailWord_627925).sum := by decide
  have hdescent : baseEnd_627925 < baseStart_627925 := by decide
  rcases family_descends (prefixWord ++ tailWord_627925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_628032 : List Nat := [2, 1, 1, 2, 2, 1, 7, 2, 4]
def baseStart_628032 : Nat := 118140960795 + 628032 * 2 ^ 59
def prefixEnd_628032 : Nat := 4983230072969 + 3 ^ 40 * 628032 * 2
def baseEnd_628032 : Nat := 71662729423242679024831

theorem tailTrace_628032 : CollatzResearch.WordTrace tailWord_628032 prefixEnd_628032 71662729423242679024831 := by
  unfold tailWord_628032
  simp only [CollatzResearch.WordTrace]
  refine ⟨11453104430377399085679175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15270805907169865447572233 11453104430377399085679175)
  ·
    refine ⟨17179656645566098628518763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11453104430377399085679175 17179656645566098628518763)
    ·
      refine ⟨25769484968349147942778145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17179656645566098628518763 25769484968349147942778145)
      ·
        refine ⟨19327113726261860957083609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25769484968349147942778145 19327113726261860957083609)
        ·
          refine ⟨14495335294696395717812707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19327113726261860957083609 14495335294696395717812707)
          ·
            refine ⟨21743002942044593576719061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14495335294696395717812707 21743002942044593576719061)
            ·
              refine ⟨509601631454170161954353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 21743002942044593576719061 509601631454170161954353)
              ·
                refine ⟨382201223590627621465765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 509601631454170161954353 382201223590627621465765)
                ·
                  refine ⟨71662729423242679024831, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 382201223590627621465765 71662729423242679024831)
                  ·
                    rfl

theorem cell22_628032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 7, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 7, 2, 4].length) (baseStart_628032 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_628032 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_628032 prefixEnd_628032 := by exact prefixLift 628032
  have htrace : WordTrace (prefixWord ++ tailWord_628032) baseStart_628032 baseEnd_628032 := by
    simpa [prefixWord, tailWord_628032, baseEnd_628032] using wordTrace_append hprefix tailTrace_628032
  have hstable : (prefixWord ++ tailWord_628032).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_628032).length < 2 ^ (prefixWord ++ tailWord_628032).sum := by decide
  have hdescent : baseEnd_628032 < baseStart_628032 := by decide
  rcases family_descends (prefixWord ++ tailWord_628032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_628038 : List Nat := [6, 1, 1, 3, 1, 2, 2, 1, 5]
def baseStart_628038 : Nat := 118140960795 + 628038 * 2 ^ 59
def prefixEnd_628038 : Nat := 4983230072969 + 3 ^ 40 * 628038 * 2
def baseEnd_628038 : Nat := 71663414064115340474825

theorem tailTrace_628038 : CollatzResearch.WordTrace tailWord_628038 prefixEnd_628038 71663414064115340474825 := by
  unfold tailWord_628038
  simp only [CollatzResearch.WordTrace]
  refine ⟨715825865585408162377399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 15270951799155374130717845 715825865585408162377399)
  ·
    refine ⟨1073738798378112243566099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 715825865585408162377399 1073738798378112243566099)
    ·
      refine ⟨1610608197567168365349149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1073738798378112243566099 1610608197567168365349149)
      ·
        refine ⟨603978074087688137005931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1610608197567168365349149 603978074087688137005931)
        ·
          refine ⟨905967111131532205508897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 603978074087688137005931 905967111131532205508897)
          ·
            refine ⟨679475333348649154131673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 905967111131532205508897 679475333348649154131673)
            ·
              refine ⟨509606500011486865598755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 679475333348649154131673 509606500011486865598755)
              ·
                refine ⟨764409750017230298398133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 509606500011486865598755 764409750017230298398133)
                ·
                  refine ⟨71663414064115340474825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 764409750017230298398133 71663414064115340474825)
                  ·
                    rfl

theorem cell22_628038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 2, 2, 1, 5].length) (baseStart_628038 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_628038 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_628038 prefixEnd_628038 := by exact prefixLift 628038
  have htrace : WordTrace (prefixWord ++ tailWord_628038) baseStart_628038 baseEnd_628038 := by
    simpa [prefixWord, tailWord_628038, baseEnd_628038] using wordTrace_append hprefix tailTrace_628038
  have hstable : (prefixWord ++ tailWord_628038).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_628038).length < 2 ^ (prefixWord ++ tailWord_628038).sum := by decide
  have hdescent : baseEnd_628038 < baseStart_628038 := by decide
  rcases family_descends (prefixWord ++ tailWord_628038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_628058 : List Nat := [3, 1, 1, 2, 1, 2, 2, 1, 2, 7]
def baseStart_628058 : Nat := 118140960795 + 628058 * 2 ^ 59
def prefixEnd_628058 : Nat := 4983230072969 + 3 ^ 40 * 628058 * 2
def baseEnd_628058 : Nat := 214997088601072635924413

theorem tailTrace_628058 : CollatzResearch.WordTrace tailWord_628058 prefixEnd_628058 214997088601072635924413 := by
  unfold tailWord_628058
  simp only [CollatzResearch.WordTrace]
  refine ⟨5726789289665151152951207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15271438105773736407869885 5726789289665151152951207)
  ·
    refine ⟨8590183934497726729426811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5726789289665151152951207 8590183934497726729426811)
    ·
      refine ⟨12885275901746590094140217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8590183934497726729426811 12885275901746590094140217)
      ·
        refine ⟨9663956926309942570605163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12885275901746590094140217 9663956926309942570605163)
        ·
          refine ⟨14495935389464913855907745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9663956926309942570605163 14495935389464913855907745)
          ·
            refine ⟨10871951542098685391930809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14495935389464913855907745 10871951542098685391930809)
            ·
              refine ⟨8153963656574014043948107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10871951542098685391930809 8153963656574014043948107)
              ·
                refine ⟨12230945484861021065922161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8153963656574014043948107 12230945484861021065922161)
                ·
                  refine ⟨9173209113645765799441621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12230945484861021065922161 9173209113645765799441621)
                  ·
                    refine ⟨214997088601072635924413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 9173209113645765799441621 214997088601072635924413)
                    ·
                      rfl

theorem cell22_628058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 1, 2, 7].length) (baseStart_628058 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_628058 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_628058 prefixEnd_628058 := by exact prefixLift 628058
  have htrace : WordTrace (prefixWord ++ tailWord_628058) baseStart_628058 baseEnd_628058 := by
    simpa [prefixWord, tailWord_628058, baseEnd_628058] using wordTrace_append hprefix tailTrace_628058
  have hstable : (prefixWord ++ tailWord_628058).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_628058).length < 2 ^ (prefixWord ++ tailWord_628058).sum := by decide
  have hdescent : baseEnd_628058 < baseStart_628058 := by decide
  rcases family_descends (prefixWord ++ tailWord_628058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_628195 : List Nat := [1, 1, 1, 6, 2, 1, 10]
def baseStart_628195 : Nat := 118140960795 + 628195 * 2 ^ 59
def prefixEnd_628195 : Nat := 4983230072969 + 3 ^ 40 * 628195 * 2
def baseEnd_628195 : Nat := 7964592092624072046259

theorem tailTrace_628195 : CollatzResearch.WordTrace tailWord_628195 prefixEnd_628195 7964592092624072046259 := by
  unfold tailWord_628195
  simp only [CollatzResearch.WordTrace]
  refine ⟨22912153959164277009542039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15274769306109518006361359 22912153959164277009542039)
  ·
    refine ⟨34368230938746415514313059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22912153959164277009542039 34368230938746415514313059)
    ·
      refine ⟨51552346408119623271469589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34368230938746415514313059 51552346408119623271469589)
      ·
        refine ⟨2416516237880607340850137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 51552346408119623271469589 2416516237880607340850137)
        ·
          refine ⟨1812387178410455505637603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2416516237880607340850137 1812387178410455505637603)
          ·
            refine ⟨2718580767615683258456405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1812387178410455505637603 2718580767615683258456405)
            ·
              refine ⟨7964592092624072046259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 2718580767615683258456405 7964592092624072046259)
              ·
                rfl

theorem cell22_628195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 10].length) (baseStart_628195 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_628195 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_628195 prefixEnd_628195 := by exact prefixLift 628195
  have htrace : WordTrace (prefixWord ++ tailWord_628195) baseStart_628195 baseEnd_628195 := by
    simpa [prefixWord, tailWord_628195, baseEnd_628195] using wordTrace_append hprefix tailTrace_628195
  have hstable : (prefixWord ++ tailWord_628195).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_628195).length < 2 ^ (prefixWord ++ tailWord_628195).sum := by decide
  have hdescent : baseEnd_628195 < baseStart_628195 := by decide
  rcases family_descends (prefixWord ++ tailWord_628195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_628197 : List Nat := [1, 3, 1, 5, 1, 1, 1, 1, 4, 4]
def baseStart_628197 : Nat := 118140960795 + 628197 * 2 ^ 59
def prefixEnd_628197 : Nat := 4983230072969 + 3 ^ 40 * 628197 * 2
def baseEnd_628197 : Nat := 215044671141722606698987

theorem tailTrace_628197 : CollatzResearch.WordTrace tailWord_628197 prefixEnd_628197 215044671141722606698987 := by
  unfold tailWord_628197
  simp only [CollatzResearch.WordTrace]
  refine ⟨22912226905157031351114845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15274817936771354234076563 22912226905157031351114845)
  ·
    refine ⟨8592085089433886756668067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22912226905157031351114845 8592085089433886756668067)
    ·
      refine ⟨12888127634150830135002101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8592085089433886756668067 12888127634150830135002101)
      ·
        refine ⟨1208261965701640325156447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 12888127634150830135002101 1208261965701640325156447)
        ·
          refine ⟨1812392948552460487734671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1208261965701640325156447 1812392948552460487734671)
          ·
            refine ⟨2718589422828690731602007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1812392948552460487734671 2718589422828690731602007)
            ·
              refine ⟨4077884134243036097403011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2718589422828690731602007 4077884134243036097403011)
              ·
                refine ⟨6116826201364554146104517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4077884134243036097403011 6116826201364554146104517)
                ·
                  refine ⟨1146904912755853902394597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6116826201364554146104517 1146904912755853902394597)
                  ·
                    refine ⟨215044671141722606698987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1146904912755853902394597 215044671141722606698987)
                    ·
                      rfl

theorem cell22_628197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 1, 1, 4, 4].length) (baseStart_628197 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_628197 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_628197 prefixEnd_628197 := by exact prefixLift 628197
  have htrace : WordTrace (prefixWord ++ tailWord_628197) baseStart_628197 baseEnd_628197 := by
    simpa [prefixWord, tailWord_628197, baseEnd_628197] using wordTrace_append hprefix tailTrace_628197
  have hstable : (prefixWord ++ tailWord_628197).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_628197).length < 2 ^ (prefixWord ++ tailWord_628197).sum := by decide
  have hdescent : baseEnd_628197 < baseStart_628197 := by decide
  rcases family_descends (prefixWord ++ tailWord_628197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_628216 : List Nat := [2, 1, 2, 1, 1, 7, 2, 1, 2, 3]
def baseStart_628216 : Nat := 118140960795 + 628216 * 2 ^ 59
def prefixEnd_628216 : Nat := 4983230072969 + 3 ^ 40 * 628216 * 2
def baseEnd_628216 : Nat := 215051175230012890473929

theorem tailTrace_628216 : CollatzResearch.WordTrace tailWord_628216 prefixEnd_628216 215051175230012890473929 := by
  unfold tailWord_628216
  simp only [CollatzResearch.WordTrace]
  refine ⟨11456459946044098798028251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15275279928058798397371001 11456459946044098798028251)
  ·
    refine ⟨17184689919066148197042377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11456459946044098798028251 17184689919066148197042377)
    ·
      refine ⟨12888517439299611147781783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17184689919066148197042377 12888517439299611147781783)
      ·
        refine ⟨19332776158949416721672675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12888517439299611147781783 19332776158949416721672675)
        ·
          refine ⟨28999164238424125082509013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19332776158949416721672675 28999164238424125082509013)
          ·
            refine ⟨679667911838065431621305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 28999164238424125082509013 679667911838065431621305)
            ·
              refine ⟨509750933878549073715979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 679667911838065431621305 509750933878549073715979)
              ·
                refine ⟨764626400817823610573969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 509750933878549073715979 764626400817823610573969)
                ·
                  refine ⟨573469800613367707930477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 764626400817823610573969 573469800613367707930477)
                  ·
                    refine ⟨215051175230012890473929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 573469800613367707930477 215051175230012890473929)
                    ·
                      rfl

theorem cell22_628216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 7, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 7, 2, 1, 2, 3].length) (baseStart_628216 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_628216 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_628216 prefixEnd_628216 := by exact prefixLift 628216
  have htrace : WordTrace (prefixWord ++ tailWord_628216) baseStart_628216 baseEnd_628216 := by
    simpa [prefixWord, tailWord_628216, baseEnd_628216] using wordTrace_append hprefix tailTrace_628216
  have hstable : (prefixWord ++ tailWord_628216).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_628216).length < 2 ^ (prefixWord ++ tailWord_628216).sum := by decide
  have hdescent : baseEnd_628216 < baseStart_628216 := by decide
  rcases family_descends (prefixWord ++ tailWord_628216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_628257 : List Nat := [1, 2, 3, 2, 2, 2, 1, 4, 5]
def baseStart_628257 : Nat := 118140960795 + 628257 * 2 ^ 59
def prefixEnd_628257 : Nat := 4983230072969 + 3 ^ 40 * 628257 * 2
def baseEnd_628257 : Nat := 71688403455967483399601

theorem tailTrace_628257 : CollatzResearch.WordTrace tailWord_628257 prefixEnd_628257 71688403455967483399601 := by
  unfold tailWord_628257
  simp only [CollatzResearch.WordTrace]
  refine ⟨22914415284939661598299025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15276276856626441065532683 22914415284939661598299025)
  ·
    refine ⟨17185811463704746198724269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22914415284939661598299025 17185811463704746198724269)
    ·
      refine ⟨6444679298889279824521601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17185811463704746198724269 6444679298889279824521601)
      ·
        refine ⟨4833509474166959868391201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6444679298889279824521601 4833509474166959868391201)
        ·
          refine ⟨3625132105625219901293401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4833509474166959868391201 3625132105625219901293401)
          ·
            refine ⟨2718849079218914925970051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3625132105625219901293401 2718849079218914925970051)
            ·
              refine ⟨4078273618828372388955077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2718849079218914925970051 4078273618828372388955077)
              ·
                refine ⟨764676303530319822929077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4078273618828372388955077 764676303530319822929077)
                ·
                  refine ⟨71688403455967483399601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 764676303530319822929077 71688403455967483399601)
                  ·
                    rfl

theorem cell22_628257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 1, 4, 5].length) (baseStart_628257 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_628257 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_628257 prefixEnd_628257 := by exact prefixLift 628257
  have htrace : WordTrace (prefixWord ++ tailWord_628257) baseStart_628257 baseEnd_628257 := by
    simpa [prefixWord, tailWord_628257, baseEnd_628257] using wordTrace_append hprefix tailTrace_628257
  have hstable : (prefixWord ++ tailWord_628257).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_628257).length < 2 ^ (prefixWord ++ tailWord_628257).sum := by decide
  have hdescent : baseEnd_628257 < baseStart_628257 := by decide
  rcases family_descends (prefixWord ++ tailWord_628257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_628287 : List Nat := [1, 1, 2, 2, 3, 3, 2, 1, 3, 4]
def baseStart_628287 : Nat := 118140960795 + 628287 * 2 ^ 59
def prefixEnd_628287 : Nat := 4983230072969 + 3 ^ 40 * 628287 * 2
def baseEnd_628287 : Nat := 215075479980992371948711

theorem tailTrace_628287 : CollatzResearch.WordTrace tailWord_628287 prefixEnd_628287 215075479980992371948711 := by
  unfold tailWord_628287
  simp only [CollatzResearch.WordTrace]
  refine ⟨22915509474830976721891115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15277006316553984481260743 22915509474830976721891115)
  ·
    refine ⟨34373264212246465082836673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22915509474830976721891115 34373264212246465082836673)
    ·
      refine ⟨25779948159184848812127505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34373264212246465082836673 25779948159184848812127505)
      ·
        refine ⟨19334961119388636609095629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25779948159184848812127505 19334961119388636609095629)
        ·
          refine ⟨7250610419770738728410861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19334961119388636609095629 7250610419770738728410861)
          ·
            refine ⟨2718978907414027023154073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7250610419770738728410861 2718978907414027023154073)
            ·
              refine ⟨2039234180560520267365555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2718978907414027023154073 2039234180560520267365555)
              ·
                refine ⟨3058851270840780401048333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2039234180560520267365555 3058851270840780401048333)
                ·
                  refine ⟨1147069226565292650393125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3058851270840780401048333 1147069226565292650393125)
                  ·
                    refine ⟨215075479980992371948711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1147069226565292650393125 215075479980992371948711)
                    ·
                      rfl

theorem cell22_628287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 2, 1, 3, 4].length) (baseStart_628287 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_628287 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_628287 prefixEnd_628287 := by exact prefixLift 628287
  have htrace : WordTrace (prefixWord ++ tailWord_628287) baseStart_628287 baseEnd_628287 := by
    simpa [prefixWord, tailWord_628287, baseEnd_628287] using wordTrace_append hprefix tailTrace_628287
  have hstable : (prefixWord ++ tailWord_628287).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_628287).length < 2 ^ (prefixWord ++ tailWord_628287).sum := by decide
  have hdescent : baseEnd_628287 < baseStart_628287 := by decide
  rcases family_descends (prefixWord ++ tailWord_628287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_628426 : List Nat := [3, 1, 2, 1, 5, 1, 2, 2, 5]
def baseStart_628426 : Nat := 118140960795 + 628426 * 2 ^ 59
def prefixEnd_628426 : Nat := 4983230072969 + 3 ^ 40 * 628426 * 2
def baseEnd_628426 : Nat := 71707687507214114241095

theorem tailTrace_628426 : CollatzResearch.WordTrace tailWord_628426 prefixEnd_628426 71707687507214114241095 := by
  unfold tailWord_628426
  simp only [CollatzResearch.WordTrace]
  refine ⟨5730144805331850865300283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15280386147551602307467421 5730144805331850865300283)
  ·
    refine ⟨8595217207997776297950425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5730144805331850865300283 8595217207997776297950425)
    ·
      refine ⟨6446412905998332223462819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8595217207997776297950425 6446412905998332223462819)
      ·
        refine ⟨9669619358997498335194229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6446412905998332223462819 9669619358997498335194229)
        ·
          refine ⟨906526814906015468924459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 9669619358997498335194229 906526814906015468924459)
          ·
            refine ⟨1359790222359023203386689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 906526814906015468924459 1359790222359023203386689)
            ·
              refine ⟨1019842666769267402540017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1359790222359023203386689 1019842666769267402540017)
              ·
                refine ⟨764882000076950551905013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1019842666769267402540017 764882000076950551905013)
                ·
                  refine ⟨71707687507214114241095, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 764882000076950551905013 71707687507214114241095)
                  ·
                    rfl

theorem cell22_628426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 2, 2, 5].length) (baseStart_628426 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_628426 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_628426 prefixEnd_628426 := by exact prefixLift 628426
  have htrace : WordTrace (prefixWord ++ tailWord_628426) baseStart_628426 baseEnd_628426 := by
    simpa [prefixWord, tailWord_628426, baseEnd_628426] using wordTrace_append hprefix tailTrace_628426
  have hstable : (prefixWord ++ tailWord_628426).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_628426).length < 2 ^ (prefixWord ++ tailWord_628426).sum := by decide
  have hdescent : baseEnd_628426 < baseStart_628426 := by decide
  rcases family_descends (prefixWord ++ tailWord_628426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_628514 : List Nat := [3, 3, 1, 1, 2, 1, 1, 1, 2, 7]
def baseStart_628514 : Nat := 118140960795 + 628514 * 2 ^ 59
def prefixEnd_628514 : Nat := 4983230072969 + 3 ^ 40 * 628514 * 2
def baseEnd_628514 : Nat := 215153186720039446523015

theorem tailTrace_628514 : CollatzResearch.WordTrace tailWord_628514 prefixEnd_628514 215153186720039446523015 := by
  unfold tailWord_628514
  simp only [CollatzResearch.WordTrace]
  refine ⟨5730947211252148622601149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15282525896672396326936397 5730947211252148622601149)
  ·
    refine ⟨2149105204219555733475431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5730947211252148622601149 2149105204219555733475431)
    ·
      refine ⟨3223657806329333600213147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2149105204219555733475431 3223657806329333600213147)
      ·
        refine ⟨4835486709494000400319721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3223657806329333600213147 4835486709494000400319721)
        ·
          refine ⟨3626615032120500300239791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4835486709494000400319721 3626615032120500300239791)
          ·
            refine ⟨5439922548180750450359687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3626615032120500300239791 5439922548180750450359687)
            ·
              refine ⟨8159883822271125675539531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5439922548180750450359687 8159883822271125675539531)
              ·
                refine ⟨12239825733406688513309297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8159883822271125675539531 12239825733406688513309297)
                ·
                  refine ⟨9179869300055016384981973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12239825733406688513309297 9179869300055016384981973)
                  ·
                    refine ⟨215153186720039446523015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 9179869300055016384981973 215153186720039446523015)
                    ·
                      rfl

theorem cell22_628514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 1, 2, 7].length) (baseStart_628514 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_628514 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_628514 prefixEnd_628514 := by exact prefixLift 628514
  have htrace : WordTrace (prefixWord ++ tailWord_628514) baseStart_628514 baseEnd_628514 := by
    simpa [prefixWord, tailWord_628514, baseEnd_628514] using wordTrace_append hprefix tailTrace_628514
  have hstable : (prefixWord ++ tailWord_628514).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_628514).length < 2 ^ (prefixWord ++ tailWord_628514).sum := by decide
  have hdescent : baseEnd_628514 < baseStart_628514 := by decide
  rcases family_descends (prefixWord ++ tailWord_628514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_628516 : List Nat := [2, 3, 1, 3, 2, 1, 4, 6]
def baseStart_628516 : Nat := 118140960795 + 628516 * 2 ^ 59
def prefixEnd_628516 : Nat := 4983230072969 + 3 ^ 40 * 628516 * 2
def baseEnd_628516 : Nat := 23905985706768011997001

theorem tailTrace_628516 : CollatzResearch.WordTrace tailWord_628516 prefixEnd_628516 23905985706768011997001 := by
  unfold tailWord_628516
  simp only [CollatzResearch.WordTrace]
  refine ⟨11461930895500674415988701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15282574527334232554651601 11461930895500674415988701)
  ·
    refine ⟨4298224085812752905995763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11461930895500674415988701 4298224085812752905995763)
    ·
      refine ⟨6447336128719129358993645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4298224085812752905995763 6447336128719129358993645)
      ·
        refine ⟨2417751048269673509622617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6447336128719129358993645 2417751048269673509622617)
        ·
          refine ⟨1813313286202255132216963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2417751048269673509622617 1813313286202255132216963)
          ·
            refine ⟨2719969929303382698325445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1813313286202255132216963 2719969929303382698325445)
            ·
              refine ⟨509994361744384255936021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2719969929303382698325445 509994361744384255936021)
              ·
                refine ⟨23905985706768011997001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 509994361744384255936021 23905985706768011997001)
                ·
                  rfl

theorem cell22_628516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 4, 6].length) (baseStart_628516 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_628516 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_628516 prefixEnd_628516 := by exact prefixLift 628516
  have htrace : WordTrace (prefixWord ++ tailWord_628516) baseStart_628516 baseEnd_628516 := by
    simpa [prefixWord, tailWord_628516, baseEnd_628516] using wordTrace_append hprefix tailTrace_628516
  have hstable : (prefixWord ++ tailWord_628516).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_628516).length < 2 ^ (prefixWord ++ tailWord_628516).sum := by decide
  have hdescent : baseEnd_628516 < baseStart_628516 := by decide
  rcases family_descends (prefixWord ++ tailWord_628516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_628561 : List Nat := [1, 2, 2, 1, 5, 2, 1, 3, 5]
def baseStart_628561 : Nat := 118140960795 + 628561 * 2 ^ 59
def prefixEnd_628561 : Nat := 4983230072969 + 3 ^ 40 * 628561 * 2
def baseEnd_628561 : Nat := 71723091926848996865957

theorem tailTrace_628561 : CollatzResearch.WordTrace tailWord_628561 prefixEnd_628561 71723091926848996865957 := by
  unfold tailWord_628561
  simp only [CollatzResearch.WordTrace]
  refine ⟨22925503075838321517365537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15283668717225547678243691 22925503075838321517365537)
  ·
    refine ⟨17194127306878741138024153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22925503075838321517365537 17194127306878741138024153)
    ·
      refine ⟨12895595480159055853518115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17194127306878741138024153 12895595480159055853518115)
      ·
        refine ⟨19343393220238583780277173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12895595480159055853518115 19343393220238583780277173)
        ·
          refine ⟨1813443114397367229400985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 19343393220238583780277173 1813443114397367229400985)
          ·
            refine ⟨1360082335798025422050739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1813443114397367229400985 1360082335798025422050739)
            ·
              refine ⟨2040123503697038133076109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1360082335798025422050739 2040123503697038133076109)
              ·
                refine ⟨765046313886389299903541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2040123503697038133076109 765046313886389299903541)
                ·
                  refine ⟨71723091926848996865957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 765046313886389299903541 71723091926848996865957)
                  ·
                    rfl

theorem cell22_628561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 1, 3, 5].length) (baseStart_628561 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_628561 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_628561 prefixEnd_628561 := by exact prefixLift 628561
  have htrace : WordTrace (prefixWord ++ tailWord_628561) baseStart_628561 baseEnd_628561 := by
    simpa [prefixWord, tailWord_628561, baseEnd_628561] using wordTrace_append hprefix tailTrace_628561
  have hstable : (prefixWord ++ tailWord_628561).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_628561).length < 2 ^ (prefixWord ++ tailWord_628561).sum := by decide
  have hdescent : baseEnd_628561 < baseStart_628561 := by decide
  rcases family_descends (prefixWord ++ tailWord_628561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_628619 : List Nat := [1, 1, 1, 1, 4, 2, 1, 4, 1, 6]
def baseStart_628619 : Nat := 118140960795 + 628619 * 2 ^ 59
def prefixEnd_628619 : Nat := 4983230072969 + 3 ^ 40 * 628619 * 2
def baseEnd_628619 : Nat := 215189130365854172647693

theorem tailTrace_628619 : CollatzResearch.WordTrace tailWord_628619 prefixEnd_628619 215189130365854172647693 := by
  unfold tailWord_628619
  simp only [CollatzResearch.WordTrace]
  refine ⟨22927618509628197422976911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15285079006418798281984607 22927618509628197422976911)
  ·
    refine ⟨34391427764442296134465367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22927618509628197422976911 34391427764442296134465367)
    ·
      refine ⟨51587141646663444201698051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34391427764442296134465367 51587141646663444201698051)
      ·
        refine ⟨77380712469995166302547077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51587141646663444201698051 77380712469995166302547077)
        ·
          refine ⟨14508883588124093681727577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 77380712469995166302547077 14508883588124093681727577)
          ·
            refine ⟨10881662691093070261295683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14508883588124093681727577 10881662691093070261295683)
            ·
              refine ⟨16322494036639605391943525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10881662691093070261295683 16322494036639605391943525)
              ·
                refine ⟨3060467631869926010989411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16322494036639605391943525 3060467631869926010989411)
                ·
                  refine ⟨4590701447804889016484117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3060467631869926010989411 4590701447804889016484117)
                  ·
                    refine ⟨215189130365854172647693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4590701447804889016484117 215189130365854172647693)
                    ·
                      rfl

theorem cell22_628619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 4, 1, 6].length) (baseStart_628619 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_628619 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_628619 prefixEnd_628619 := by exact prefixLift 628619
  have htrace : WordTrace (prefixWord ++ tailWord_628619) baseStart_628619 baseEnd_628619 := by
    simpa [prefixWord, tailWord_628619, baseEnd_628619] using wordTrace_append hprefix tailTrace_628619
  have hstable : (prefixWord ++ tailWord_628619).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_628619).length < 2 ^ (prefixWord ++ tailWord_628619).sum := by decide
  have hdescent : baseEnd_628619 < baseStart_628619 := by decide
  rcases family_descends (prefixWord ++ tailWord_628619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_628642 : List Nat := [3, 3, 1, 2, 3, 2, 2, 1, 1, 4]
def baseStart_628642 : Nat := 118140960795 + 628642 * 2 ^ 59
def prefixEnd_628642 : Nat := 4983230072969 + 3 ^ 40 * 628642 * 2
def baseEnd_628642 : Nat := 215197003735889779322623

theorem tailTrace_628642 : CollatzResearch.WordTrace tailWord_628642 prefixEnd_628642 215197003735889779322623 := by
  unfold tailWord_628642
  simp only [CollatzResearch.WordTrace]
  refine ⟨5732114347136218087766045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15285638259029914900709453 5732114347136218087766045)
  ·
    refine ⟨2149542880176081782912267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5732114347136218087766045 2149542880176081782912267)
    ·
      refine ⟨3224314320264122674368401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2149542880176081782912267 3224314320264122674368401)
      ·
        refine ⟨2418235740198092005776301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3224314320264122674368401 2418235740198092005776301)
        ·
          refine ⟨906838402574284502166113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2418235740198092005776301 906838402574284502166113)
          ·
            refine ⟨680128801930713376624585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 906838402574284502166113 680128801930713376624585)
            ·
              refine ⟨510096601448035032468439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 680128801930713376624585 510096601448035032468439)
              ·
                refine ⟨765144902172052548702659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 510096601448035032468439 765144902172052548702659)
                ·
                  refine ⟨1147717353258078823053989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 765144902172052548702659 1147717353258078823053989)
                  ·
                    refine ⟨215197003735889779322623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1147717353258078823053989 215197003735889779322623)
                    ·
                      rfl

theorem cell22_628642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 2, 2, 1, 1, 4].length) (baseStart_628642 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_628642 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_628642 prefixEnd_628642 := by exact prefixLift 628642
  have htrace : WordTrace (prefixWord ++ tailWord_628642) baseStart_628642 baseEnd_628642 := by
    simpa [prefixWord, tailWord_628642, baseEnd_628642] using wordTrace_append hprefix tailTrace_628642
  have hstable : (prefixWord ++ tailWord_628642).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_628642).length < 2 ^ (prefixWord ++ tailWord_628642).sum := by decide
  have hdescent : baseEnd_628642 < baseStart_628642 := by decide
  rcases family_descends (prefixWord ++ tailWord_628642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_628743 : List Nat := [1, 1, 4, 3, 1, 3, 1, 1, 3, 4]
def baseStart_628743 : Nat := 118140960795 + 628743 * 2 ^ 59
def prefixEnd_628743 : Nat := 4983230072969 + 3 ^ 40 * 628743 * 2
def baseEnd_628743 : Nat := 215231578099959182547313

theorem tailTrace_628743 : CollatzResearch.WordTrace tailWord_628743 prefixEnd_628743 215231578099959182547313 := by
  unfold tailWord_628743
  simp only [CollatzResearch.WordTrace]
  refine ⟨22932141161178966600490883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15288094107452644400327255 22932141161178966600490883)
  ·
    refine ⟨34398211741768449900736325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22932141161178966600490883 34398211741768449900736325)
    ·
      refine ⟨6449664701581584356388061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 34398211741768449900736325 6449664701581584356388061)
      ·
        refine ⟨2418624263093094133645523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6449664701581584356388061 2418624263093094133645523)
        ·
          refine ⟨3627936394639641200468285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2418624263093094133645523 3627936394639641200468285)
          ·
            refine ⟨1360476147989865450175607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3627936394639641200468285 1360476147989865450175607)
            ·
              refine ⟨2040714221984798175263411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1360476147989865450175607 2040714221984798175263411)
              ·
                refine ⟨3061071332977197262895117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2040714221984798175263411 3061071332977197262895117)
                ·
                  refine ⟨1147901749866448973585669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3061071332977197262895117 1147901749866448973585669)
                  ·
                    refine ⟨215231578099959182547313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1147901749866448973585669 215231578099959182547313)
                    ·
                      rfl

theorem cell22_628743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 1, 1, 3, 4].length) (baseStart_628743 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_628743 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_628743 prefixEnd_628743 := by exact prefixLift 628743
  have htrace : WordTrace (prefixWord ++ tailWord_628743) baseStart_628743 baseEnd_628743 := by
    simpa [prefixWord, tailWord_628743, baseEnd_628743] using wordTrace_append hprefix tailTrace_628743
  have hstable : (prefixWord ++ tailWord_628743).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_628743).length < 2 ^ (prefixWord ++ tailWord_628743).sum := by decide
  have hdescent : baseEnd_628743 < baseStart_628743 := by decide
  rcases family_descends (prefixWord ++ tailWord_628743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_628760 : List Nat := [2, 1, 2, 3, 2, 1, 5, 1, 1, 4]
def baseStart_628760 : Nat := 118140960795 + 628760 * 2 ^ 59
def prefixEnd_628760 : Nat := 4983230072969 + 3 ^ 40 * 628760 * 2
def baseEnd_628760 : Nat := 215237397547376804872261

theorem tailTrace_628760 : CollatzResearch.WordTrace tailWord_628760 prefixEnd_628760 215237397547376804872261 := by
  unfold tailWord_628760
  simp only [CollatzResearch.WordTrace]
  refine ⟨11466380601058689251929867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15288507468078252335906489 11466380601058689251929867)
  ·
    refine ⟨17199570901588033877894801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11466380601058689251929867 17199570901588033877894801)
    ·
      refine ⟨12899678176191025408421101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17199570901588033877894801 12899678176191025408421101)
      ·
        refine ⟨4837379316071634528157913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12899678176191025408421101 4837379316071634528157913)
        ·
          refine ⟨3628034487053725896118435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4837379316071634528157913 3628034487053725896118435)
          ·
            refine ⟨5442051730580588844177653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3628034487053725896118435 5442051730580588844177653)
            ·
              refine ⟨510192349741930204141655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5442051730580588844177653 510192349741930204141655)
              ·
                refine ⟨765288524612895306212483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 510192349741930204141655 765288524612895306212483)
                ·
                  refine ⟨1147932786919342959318725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 765288524612895306212483 1147932786919342959318725)
                  ·
                    refine ⟨215237397547376804872261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1147932786919342959318725 215237397547376804872261)
                    ·
                      rfl

theorem cell22_628760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 5, 1, 1, 4].length) (baseStart_628760 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_628760 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_628760 prefixEnd_628760 := by exact prefixLift 628760
  have htrace : WordTrace (prefixWord ++ tailWord_628760) baseStart_628760 baseEnd_628760 := by
    simpa [prefixWord, tailWord_628760, baseEnd_628760] using wordTrace_append hprefix tailTrace_628760
  have hstable : (prefixWord ++ tailWord_628760).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_628760).length < 2 ^ (prefixWord ++ tailWord_628760).sum := by decide
  have hdescent : baseEnd_628760 < baseStart_628760 := by decide
  rcases family_descends (prefixWord ++ tailWord_628760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_628790 : List Nat := [5, 1, 2, 1, 1, 1, 4, 1, 1, 5]
def baseStart_628790 : Nat := 118140960795 + 628790 * 2 ^ 59
def prefixEnd_628790 : Nat := 4983230072969 + 3 ^ 40 * 628790 * 2
def baseEnd_628790 : Nat := 215247667160466726622169

theorem tailTrace_628790 : CollatzResearch.WordTrace tailWord_628790 prefixEnd_628790 215247667160466726622169 := by
  unfold tailWord_628790
  simp only [CollatzResearch.WordTrace]
  refine ⟨1433365962000543351715739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 15289236928005795751634549 1433365962000543351715739)
  ·
    refine ⟨2150048943000815027573609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1433365962000543351715739 2150048943000815027573609)
    ·
      refine ⟨1612536707250611270680207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2150048943000815027573609 1612536707250611270680207)
      ·
        refine ⟨2418805060875916906020311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1612536707250611270680207 2418805060875916906020311)
        ·
          refine ⟨3628207591313875359030467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2418805060875916906020311 3628207591313875359030467)
          ·
            refine ⟨5442311386970813038545701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3628207591313875359030467 5442311386970813038545701)
            ·
              refine ⟨1020433385057027444727319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5442311386970813038545701 1020433385057027444727319)
              ·
                refine ⟨1530650077585541167090979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1020433385057027444727319 1530650077585541167090979)
                ·
                  refine ⟨2295975116378311750636469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1530650077585541167090979 2295975116378311750636469)
                  ·
                    refine ⟨215247667160466726622169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2295975116378311750636469 215247667160466726622169)
                    ·
                      rfl

theorem cell22_628790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 4, 1, 1, 5].length) (baseStart_628790 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_628790 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_628790 prefixEnd_628790 := by exact prefixLift 628790
  have htrace : WordTrace (prefixWord ++ tailWord_628790) baseStart_628790 baseEnd_628790 := by
    simpa [prefixWord, tailWord_628790, baseEnd_628790] using wordTrace_append hprefix tailTrace_628790
  have hstable : (prefixWord ++ tailWord_628790).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_628790).length < 2 ^ (prefixWord ++ tailWord_628790).sum := by decide
  have hdescent : baseEnd_628790 < baseStart_628790 := by decide
  rcases family_descends (prefixWord ++ tailWord_628790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_628869 : List Nat := [1, 3, 1, 1, 5, 3, 1, 3, 1, 3]
def baseStart_628869 : Nat := 118140960795 + 628869 * 2 ^ 59
def prefixEnd_628869 : Nat := 4983230072969 + 3 ^ 40 * 628869 * 2
def baseEnd_628869 : Nat := 215274710474936853896927

theorem tailTrace_628869 : CollatzResearch.WordTrace tailWord_628869 prefixEnd_628869 215274710474936853896927 := by
  unfold tailWord_628869
  simp only [CollatzResearch.WordTrace]
  refine ⟨22936736758722490119577661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15291157839148326746385107 22936736758722490119577661)
  ·
    refine ⟨8601276284520933794841623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22936736758722490119577661 8601276284520933794841623)
    ·
      refine ⟨12901914426781400692262435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8601276284520933794841623 12901914426781400692262435)
      ·
        refine ⟨19352871640172101038393653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12901914426781400692262435 19352871640172101038393653)
        ·
          refine ⟨1814331716266134472349405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 19352871640172101038393653 1814331716266134472349405)
          ·
            refine ⟨680374393599800427131027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1814331716266134472349405 680374393599800427131027)
            ·
              refine ⟨1020561590399700640696541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 680374393599800427131027 1020561590399700640696541)
              ·
                refine ⟨382710596399887740261203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1020561590399700640696541 382710596399887740261203)
                ·
                  refine ⟨574065894599831610391805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 382710596399887740261203 574065894599831610391805)
                  ·
                    refine ⟨215274710474936853896927, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 574065894599831610391805 215274710474936853896927)
                    ·
                      rfl

theorem cell22_628869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 3, 1, 3, 1, 3].length) (baseStart_628869 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_628869 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_628869 prefixEnd_628869 := by exact prefixLift 628869
  have htrace : WordTrace (prefixWord ++ tailWord_628869) baseStart_628869 baseEnd_628869 := by
    simpa [prefixWord, tailWord_628869, baseEnd_628869] using wordTrace_append hprefix tailTrace_628869
  have hstable : (prefixWord ++ tailWord_628869).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_628869).length < 2 ^ (prefixWord ++ tailWord_628869).sum := by decide
  have hdescent : baseEnd_628869 < baseStart_628869 := by decide
  rcases family_descends (prefixWord ++ tailWord_628869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_628942 : List Nat := [4, 1, 1, 1, 4, 1, 1, 4, 2, 3]
def baseStart_628942 : Nat := 118140960795 + 628942 * 2 ^ 59
def prefixEnd_628942 : Nat := 4983230072969 + 3 ^ 40 * 628942 * 2
def baseEnd_628942 : Nat := 215299699866788996821703

theorem tailTrace_628942 : CollatzResearch.WordTrace tailWord_628942 prefixEnd_628942 215299699866788996821703 := by
  unfold tailWord_628942
  simp only [CollatzResearch.WordTrace]
  refine ⟨2867424910932252948373135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15292932858305349057990053 2867424910932252948373135)
  ·
    refine ⟨4301137366398379422559703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2867424910932252948373135 4301137366398379422559703)
    ·
      refine ⟨6451706049597569133839555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4301137366398379422559703 6451706049597569133839555)
      ·
        refine ⟨9677559074396353700759333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6451706049597569133839555 9677559074396353700759333)
        ·
          refine ⟨1814542326449316318892375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9677559074396353700759333 1814542326449316318892375)
          ·
            refine ⟨2721813489673974478338563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1814542326449316318892375 2721813489673974478338563)
            ·
              refine ⟨4082720234510961717507845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2721813489673974478338563 4082720234510961717507845)
              ·
                refine ⟨765510043970805322032721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4082720234510961717507845 765510043970805322032721)
                ·
                  refine ⟨574132532978103991524541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 765510043970805322032721 574132532978103991524541)
                  ·
                    refine ⟨215299699866788996821703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 574132532978103991524541 215299699866788996821703)
                    ·
                      rfl

theorem cell22_628942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 1, 4, 2, 3].length) (baseStart_628942 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_628942 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_628942 prefixEnd_628942 := by exact prefixLift 628942
  have htrace : WordTrace (prefixWord ++ tailWord_628942) baseStart_628942 baseEnd_628942 := by
    simpa [prefixWord, tailWord_628942, baseEnd_628942] using wordTrace_append hprefix tailTrace_628942
  have hstable : (prefixWord ++ tailWord_628942).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_628942).length < 2 ^ (prefixWord ++ tailWord_628942).sum := by decide
  have hdescent : baseEnd_628942 < baseStart_628942 := by decide
  rcases family_descends (prefixWord ++ tailWord_628942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_629000 : List Nat := [2, 1, 3, 2, 3, 2, 1, 1, 7]
def baseStart_629000 : Nat := 118140960795 + 629000 * 2 ^ 59
def prefixEnd_629000 : Nat := 4983230072969 + 3 ^ 40 * 629000 * 2
def baseEnd_629000 : Nat := 71773184817365392957175

theorem tailTrace_629000 : CollatzResearch.WordTrace tailWord_629000 prefixEnd_629000 71773184817365392957175 := by
  unfold tailWord_629000
  simp only [CollatzResearch.WordTrace]
  refine ⟨11470757360623949746298227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15294343147498599661730969 11470757360623949746298227)
  ·
    refine ⟨17206136040935924619447341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11470757360623949746298227 17206136040935924619447341)
    ·
      refine ⟨6452301015350971732292753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17206136040935924619447341 6452301015350971732292753)
      ·
        refine ⟨4839225761513228799219565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6452301015350971732292753 4839225761513228799219565)
        ·
          refine ⟨1814709660567460799707337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4839225761513228799219565 1814709660567460799707337)
          ·
            refine ⟨1361032245425595599780503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1814709660567460799707337 1361032245425595599780503)
            ·
              refine ⟨2041548368138393399670755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1361032245425595599780503 2041548368138393399670755)
              ·
                refine ⟨3062322552207590099506133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2041548368138393399670755 3062322552207590099506133)
                ·
                  refine ⟨71773184817365392957175, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3062322552207590099506133 71773184817365392957175)
                  ·
                    rfl

theorem cell22_629000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 1, 1, 7].length) (baseStart_629000 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_629000 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_629000 prefixEnd_629000 := by exact prefixLift 629000
  have htrace : WordTrace (prefixWord ++ tailWord_629000) baseStart_629000 baseEnd_629000 := by
    simpa [prefixWord, tailWord_629000, baseEnd_629000] using wordTrace_append hprefix tailTrace_629000
  have hstable : (prefixWord ++ tailWord_629000).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_629000).length < 2 ^ (prefixWord ++ tailWord_629000).sum := by decide
  have hdescent : baseEnd_629000 < baseStart_629000 := by decide
  rcases family_descends (prefixWord ++ tailWord_629000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_629015 : List Nat := [1, 1, 3, 4, 1, 2, 2, 1, 2, 5]
def baseStart_629015 : Nat := 118140960795 + 629015 * 2 ^ 59
def prefixEnd_629015 : Nat := 4983230072969 + 3 ^ 40 * 629015 * 2
def baseEnd_629015 : Nat := 215324689258641139746479

theorem tailTrace_629015 : CollatzResearch.WordTrace tailWord_629015 prefixEnd_629015 215324689258641139746479 := by
  unfold tailWord_629015
  simp only [CollatzResearch.WordTrace]
  refine ⟨22942061816193557054392499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15294707877462371369594999 22942061816193557054392499)
  ·
    refine ⟨34413092724290335581588749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22942061816193557054392499 34413092724290335581588749)
    ·
      refine ⟨12904909771608875843095781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34413092724290335581588749 12904909771608875843095781)
      ·
        refine ⟨2419670582176664220580459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12904909771608875843095781 2419670582176664220580459)
        ·
          refine ⟨3629505873264996330870689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2419670582176664220580459 3629505873264996330870689)
          ·
            refine ⟨2722129404948747248153017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3629505873264996330870689 2722129404948747248153017)
            ·
              refine ⟨2041597053711560436114763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2722129404948747248153017 2041597053711560436114763)
              ·
                refine ⟨3062395580567340654172145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2041597053711560436114763 3062395580567340654172145)
                ·
                  refine ⟨2296796685425505490629109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3062395580567340654172145 2296796685425505490629109)
                  ·
                    refine ⟨215324689258641139746479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2296796685425505490629109 215324689258641139746479)
                    ·
                      rfl

theorem cell22_629015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 2, 1, 2, 5].length) (baseStart_629015 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_629015 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_629015 prefixEnd_629015 := by exact prefixLift 629015
  have htrace : WordTrace (prefixWord ++ tailWord_629015) baseStart_629015 baseEnd_629015 := by
    simpa [prefixWord, tailWord_629015, baseEnd_629015] using wordTrace_append hprefix tailTrace_629015
  have hstable : (prefixWord ++ tailWord_629015).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_629015).length < 2 ^ (prefixWord ++ tailWord_629015).sum := by decide
  have hdescent : baseEnd_629015 < baseStart_629015 := by decide
  rcases family_descends (prefixWord ++ tailWord_629015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_629092 : List Nat := [2, 3, 1, 1, 3, 1, 4, 1, 2, 4]
def baseStart_629092 : Nat := 118140960795 + 629092 * 2 ^ 59
def prefixEnd_629092 : Nat := 4983230072969 + 3 ^ 40 * 629092 * 2
def baseEnd_629092 : Nat := 215351047932238605571243

theorem tailTrace_629092 : CollatzResearch.WordTrace tailWord_629092 prefixEnd_629092 215351047932238605571243 := by
  unfold tailWord_629092
  simp only [CollatzResearch.WordTrace]
  refine ⟨11472435118457299602472765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15296580157943066136630353 11472435118457299602472765)
  ·
    refine ⟨4302163169421487350927287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11472435118457299602472765 4302163169421487350927287)
    ·
      refine ⟨6453244754132231026390931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4302163169421487350927287 6453244754132231026390931)
      ·
        refine ⟨9679867131198346539586397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6453244754132231026390931 9679867131198346539586397)
        ·
          refine ⟨3629950174199379952344899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9679867131198346539586397 3629950174199379952344899)
          ·
            refine ⟨5444925261299069928517349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3629950174199379952344899 5444925261299069928517349)
            ·
              refine ⟨1020923486493575611597003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5444925261299069928517349 1020923486493575611597003)
              ·
                refine ⟨1531385229740363417395505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1020923486493575611597003 1531385229740363417395505)
                ·
                  refine ⟨1148538922305272563046629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1531385229740363417395505 1148538922305272563046629)
                  ·
                    refine ⟨215351047932238605571243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1148538922305272563046629 215351047932238605571243)
                    ·
                      rfl

theorem cell22_629092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 4, 1, 2, 4].length) (baseStart_629092 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_629092 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_629092 prefixEnd_629092 := by exact prefixLift 629092
  have htrace : WordTrace (prefixWord ++ tailWord_629092) baseStart_629092 baseEnd_629092 := by
    simpa [prefixWord, tailWord_629092, baseEnd_629092] using wordTrace_append hprefix tailTrace_629092
  have hstable : (prefixWord ++ tailWord_629092).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_629092).length < 2 ^ (prefixWord ++ tailWord_629092).sum := by decide
  have hdescent : baseEnd_629092 < baseStart_629092 := by decide
  rcases family_descends (prefixWord ++ tailWord_629092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_629162 : List Nat := [3, 1, 6, 1, 2, 1, 1, 2, 2, 3]
def baseStart_629162 : Nat := 118140960795 + 629162 * 2 ^ 59
def prefixEnd_629162 : Nat := 4983230072969 + 3 ^ 40 * 629162 * 2
def baseEnd_629162 : Nat := 215375010362781756321029

theorem tailTrace_629162 : CollatzResearch.WordTrace tailWord_629162 prefixEnd_629162 215375010362781756321029 := by
  unfold tailWord_629162
  simp only [CollatzResearch.WordTrace]
  refine ⟨5736855836665250289998435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15298282231107334106662493 5736855836665250289998435)
  ·
    refine ⟨8605283754997875434997653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5736855836665250289998435 8605283754997875434997653)
    ·
      refine ⟨403372676015525411015515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 8605283754997875434997653 403372676015525411015515)
      ·
        refine ⟨605059014023288116523273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 403372676015525411015515 605059014023288116523273)
        ·
          refine ⟨453794260517466087392455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 605059014023288116523273 453794260517466087392455)
          ·
            refine ⟨680691390776199131088683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 453794260517466087392455 680691390776199131088683)
            ·
              refine ⟨1021037086164298696633025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 680691390776199131088683 1021037086164298696633025)
              ·
                refine ⟨765777814623224022474769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1021037086164298696633025 765777814623224022474769)
                ·
                  refine ⟨574333360967418016856077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 765777814623224022474769 574333360967418016856077)
                  ·
                    refine ⟨215375010362781756321029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 574333360967418016856077 215375010362781756321029)
                    ·
                      rfl

theorem cell22_629162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 2, 1, 1, 2, 2, 3].length) (baseStart_629162 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_629162 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_629162 prefixEnd_629162 := by exact prefixLift 629162
  have htrace : WordTrace (prefixWord ++ tailWord_629162) baseStart_629162 baseEnd_629162 := by
    simpa [prefixWord, tailWord_629162, baseEnd_629162] using wordTrace_append hprefix tailTrace_629162
  have hstable : (prefixWord ++ tailWord_629162).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_629162).length < 2 ^ (prefixWord ++ tailWord_629162).sum := by decide
  have hdescent : baseEnd_629162 < baseStart_629162 := by decide
  rcases family_descends (prefixWord ++ tailWord_629162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_629169 : List Nat := [1, 2, 2, 4, 1, 4, 1, 2, 5]
def baseStart_629169 : Nat := 118140960795 + 629169 * 2 ^ 59
def prefixEnd_629169 : Nat := 4983230072969 + 3 ^ 40 * 629169 * 2
def baseEnd_629169 : Nat := 71792468868612023798669

theorem tailTrace_629169 : CollatzResearch.WordTrace tailWord_629169 prefixEnd_629169 71792468868612023798669 := by
  unfold tailWord_629169
  simp only [CollatzResearch.WordTrace]
  refine ⟨22947678657635641355498561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15298452438423760903665707 22947678657635641355498561)
  ·
    refine ⟨17210758993226731016623921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22947678657635641355498561 17210758993226731016623921)
    ·
      refine ⟨12908069244920048262467941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17210758993226731016623921 12908069244920048262467941)
      ·
        refine ⟨2420262983422509049212739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12908069244920048262467941 2420262983422509049212739)
        ·
          refine ⟨3630394475133763573819109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2420262983422509049212739 3630394475133763573819109)
          ·
            refine ⟨680698964087580670091083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3630394475133763573819109 680698964087580670091083)
            ·
              refine ⟨1021048446131371005136625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 680698964087580670091083 1021048446131371005136625)
              ·
                refine ⟨765786334598528253852469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1021048446131371005136625 765786334598528253852469)
                ·
                  refine ⟨71792468868612023798669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 765786334598528253852469 71792468868612023798669)
                  ·
                    rfl

theorem cell22_629169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 4, 1, 2, 5].length) (baseStart_629169 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_629169 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_629169 prefixEnd_629169 := by exact prefixLift 629169
  have htrace : WordTrace (prefixWord ++ tailWord_629169) baseStart_629169 baseEnd_629169 := by
    simpa [prefixWord, tailWord_629169, baseEnd_629169] using wordTrace_append hprefix tailTrace_629169
  have hstable : (prefixWord ++ tailWord_629169).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_629169).length < 2 ^ (prefixWord ++ tailWord_629169).sum := by decide
  have hdescent : baseEnd_629169 < baseStart_629169 := by decide
  rcases family_descends (prefixWord ++ tailWord_629169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_629182 : List Nat := [4, 2, 1, 1, 1, 1, 2, 1, 5, 4]
def baseStart_629182 : Nat := 118140960795 + 629182 * 2 ^ 59
def prefixEnd_629182 : Nat := 4983230072969 + 3 ^ 40 * 629182 * 2
def baseEnd_629182 : Nat := 215381856771508370820967

theorem tailTrace_629182 : CollatzResearch.WordTrace tailWord_629182 prefixEnd_629182 215381856771508370820967 := by
  unfold tailWord_629182
  simp only [CollatzResearch.WordTrace]
  refine ⟨2868519100823568071965225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15298768537725696383814533 2868519100823568071965225)
  ·
    refine ⟨2151389325617676053973919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2868519100823568071965225 2151389325617676053973919)
    ·
      refine ⟨3227083988426514080960879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2151389325617676053973919 3227083988426514080960879)
      ·
        refine ⟨4840625982639771121441319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3227083988426514080960879 4840625982639771121441319)
        ·
          refine ⟨7260938973959656682161979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4840625982639771121441319 7260938973959656682161979)
          ·
            refine ⟨10891408460939485023242969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7260938973959656682161979 10891408460939485023242969)
            ·
              refine ⟨8168556345704613767432227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10891408460939485023242969 8168556345704613767432227)
              ·
                refine ⟨12252834518556920651148341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8168556345704613767432227 12252834518556920651148341)
                ·
                  refine ⟨1148703236114711311045157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 12252834518556920651148341 1148703236114711311045157)
                  ·
                    refine ⟨215381856771508370820967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1148703236114711311045157 215381856771508370820967)
                    ·
                      rfl

theorem cell22_629182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 1, 5, 4].length) (baseStart_629182 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_629182 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_629182 prefixEnd_629182 := by exact prefixLift 629182
  have htrace : WordTrace (prefixWord ++ tailWord_629182) baseStart_629182 baseEnd_629182 := by
    simpa [prefixWord, tailWord_629182, baseEnd_629182] using wordTrace_append hprefix tailTrace_629182
  have hstable : (prefixWord ++ tailWord_629182).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_629182).length < 2 ^ (prefixWord ++ tailWord_629182).sum := by decide
  have hdescent : baseEnd_629182 < baseStart_629182 := by decide
  rcases family_descends (prefixWord ++ tailWord_629182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_629227 : List Nat := [1, 1, 1, 1, 2, 3, 5, 2, 2, 4]
def baseStart_629227 : Nat := 118140960795 + 629227 * 2 ^ 59
def prefixEnd_629227 : Nat := 4983230072969 + 3 ^ 40 * 629227 * 2
def baseEnd_629227 : Nat := 215397261191143253445829

theorem tailTrace_629227 : CollatzResearch.WordTrace tailWord_629227 prefixEnd_629227 215397261191143253445829 := by
  unfold tailWord_629227
  simp only [CollatzResearch.WordTrace]
  refine ⟨22949794091425517261109935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15299862727617011507406623 22949794091425517261109935)
  ·
    refine ⟨34424691137138275891664903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22949794091425517261109935 34424691137138275891664903)
    ·
      refine ⟨51637036705707413837497355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34424691137138275891664903 51637036705707413837497355)
      ·
        refine ⟨77455555058561120756246033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51637036705707413837497355 77455555058561120756246033)
        ·
          refine ⟨58091666293920840567184525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77455555058561120756246033 58091666293920840567184525)
          ·
            refine ⟨21784374860220315212694197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 58091666293920840567184525 21784374860220315212694197)
            ·
              refine ⟨2042285143145654551190081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 21784374860220315212694197 2042285143145654551190081)
              ·
                refine ⟨1531713857359240913392561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2042285143145654551190081 1531713857359240913392561)
                ·
                  refine ⟨1148785393019430685044421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1531713857359240913392561 1148785393019430685044421)
                  ·
                    refine ⟨215397261191143253445829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1148785393019430685044421 215397261191143253445829)
                    ·
                      rfl

theorem cell22_629227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 5, 2, 2, 4].length) (baseStart_629227 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_629227 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_629227 prefixEnd_629227 := by exact prefixLift 629227
  have htrace : WordTrace (prefixWord ++ tailWord_629227) baseStart_629227 baseEnd_629227 := by
    simpa [prefixWord, tailWord_629227, baseEnd_629227] using wordTrace_append hprefix tailTrace_629227
  have hstable : (prefixWord ++ tailWord_629227).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_629227).length < 2 ^ (prefixWord ++ tailWord_629227).sum := by decide
  have hdescent : baseEnd_629227 < baseStart_629227 := by decide
  rcases family_descends (prefixWord ++ tailWord_629227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_629250 : List Nat := [3, 4, 1, 2, 3, 1, 1, 2, 1, 4]
def baseStart_629250 : Nat := 118140960795 + 629250 * 2 ^ 59
def prefixEnd_629250 : Nat := 4983230072969 + 3 ^ 40 * 629250 * 2
def baseEnd_629250 : Nat := 215405134561178860120759

theorem tailTrace_629250 : CollatzResearch.WordTrace tailWord_629250 prefixEnd_629250 215405134561178860120759 := by
  unfold tailWord_629250
  simp only [CollatzResearch.WordTrace]
  refine ⟨5737658242585548047299301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15300421980228128126131469 5737658242585548047299301)
  ·
    refine ⟨1075810920484790258868619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5737658242585548047299301 1075810920484790258868619)
    ·
      refine ⟨1613716380727185388302929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1075810920484790258868619 1613716380727185388302929)
      ·
        refine ⟨1210287285545389041227197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1613716380727185388302929 1210287285545389041227197)
        ·
          refine ⟨453857732079520890460199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1210287285545389041227197 453857732079520890460199)
          ·
            refine ⟨680786598119281335690299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 453857732079520890460199 680786598119281335690299)
            ·
              refine ⟨1021179897178922003535449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 680786598119281335690299 1021179897178922003535449)
              ·
                refine ⟨765884922884191502651587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1021179897178922003535449 765884922884191502651587)
                ·
                  refine ⟨1148827384326287253977381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 765884922884191502651587 1148827384326287253977381)
                  ·
                    refine ⟨215405134561178860120759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1148827384326287253977381 215405134561178860120759)
                    ·
                      rfl

theorem cell22_629250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 3, 1, 1, 2, 1, 4].length) (baseStart_629250 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_629250 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_629250 prefixEnd_629250 := by exact prefixLift 629250
  have htrace : WordTrace (prefixWord ++ tailWord_629250) baseStart_629250 baseEnd_629250 := by
    simpa [prefixWord, tailWord_629250, baseEnd_629250] using wordTrace_append hprefix tailTrace_629250
  have hstable : (prefixWord ++ tailWord_629250).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_629250).length < 2 ^ (prefixWord ++ tailWord_629250).sum := by decide
  have hdescent : baseEnd_629250 < baseStart_629250 := by decide
  rcases family_descends (prefixWord ++ tailWord_629250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_629325 : List Nat := [1, 6, 1, 1, 2, 2, 2, 3, 1, 3]
def baseStart_629325 : Nat := 118140960795 + 629325 * 2 ^ 59
def prefixEnd_629325 : Nat := 4983230072969 + 3 ^ 40 * 629325 * 2
def baseEnd_629325 : Nat := 215430808593903664495529

theorem tailTrace_629325 : CollatzResearch.WordTrace tailWord_629325 prefixEnd_629325 215430808593903664495529 := by
  unfold tailWord_629325
  simp only [CollatzResearch.WordTrace]
  refine ⟨22953368445070479998177429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15302245630046986665451619 22953368445070479998177429)
  ·
    refine ⟨1075939145862678749914567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 22953368445070479998177429 1075939145862678749914567)
    ·
      refine ⟨1613908718794018124871851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1075939145862678749914567 1613908718794018124871851)
      ·
        refine ⟨2420863078191027187307777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1613908718794018124871851 2420863078191027187307777)
        ·
          refine ⟨1815647308643270390480833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2420863078191027187307777 1815647308643270390480833)
          ·
            refine ⟨1361735481482452792860625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1815647308643270390480833 1361735481482452792860625)
            ·
              refine ⟨1021301611111839594645469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1361735481482452792860625 1021301611111839594645469)
              ·
                refine ⟨382988104166939847992051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1021301611111839594645469 382988104166939847992051)
                ·
                  refine ⟨574482156250409771988077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 382988104166939847992051 574482156250409771988077)
                  ·
                    refine ⟨215430808593903664495529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 574482156250409771988077 215430808593903664495529)
                    ·
                      rfl

theorem cell22_629325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 2, 3, 1, 3].length) (baseStart_629325 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_629325 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_629325 prefixEnd_629325 := by exact prefixLift 629325
  have htrace : WordTrace (prefixWord ++ tailWord_629325) baseStart_629325 baseEnd_629325 := by
    simpa [prefixWord, tailWord_629325, baseEnd_629325] using wordTrace_append hprefix tailTrace_629325
  have hstable : (prefixWord ++ tailWord_629325).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_629325).length < 2 ^ (prefixWord ++ tailWord_629325).sum := by decide
  have hdescent : baseEnd_629325 < baseStart_629325 := by decide
  rcases family_descends (prefixWord ++ tailWord_629325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_629342 : List Nat := [4, 4, 1, 2, 1, 1, 2, 1, 3, 3]
def baseStart_629342 : Nat := 118140960795 + 629342 * 2 ^ 59
def prefixEnd_629342 : Nat := 4983230072969 + 3 ^ 40 * 629342 * 2
def baseEnd_629342 : Nat := 215436628041321286820477

theorem tailTrace_629342 : CollatzResearch.WordTrace tailWord_629342 prefixEnd_629342 215436628041321286820477 := by
  unfold tailWord_629342
  simp only [CollatzResearch.WordTrace]
  refine ⟨2869248560751111487693285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15302658990672594601030853 2869248560751111487693285)
  ·
    refine ⟨537984105140833403942491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2869248560751111487693285 537984105140833403942491)
    ·
      refine ⟨806976157711250105913737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 537984105140833403942491 806976157711250105913737)
      ·
        refine ⟨605232118283437579435303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 806976157711250105913737 605232118283437579435303)
        ·
          refine ⟨907848177425156369152955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 605232118283437579435303 907848177425156369152955)
          ·
            refine ⟨1361772266137734553729433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 907848177425156369152955 1361772266137734553729433)
            ·
              refine ⟨1021329199603300915297075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1361772266137734553729433 1021329199603300915297075)
              ·
                refine ⟨1531993799404951372945613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1021329199603300915297075 1531993799404951372945613)
                ·
                  refine ⟨574497674776856764854605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1531993799404951372945613 574497674776856764854605)
                  ·
                    refine ⟨215436628041321286820477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 574497674776856764854605 215436628041321286820477)
                    ·
                      rfl

theorem cell22_629342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 2, 1, 3, 3].length) (baseStart_629342 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_629342 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_629342 prefixEnd_629342 := by exact prefixLift 629342
  have htrace : WordTrace (prefixWord ++ tailWord_629342) baseStart_629342 baseEnd_629342 := by
    simpa [prefixWord, tailWord_629342, baseEnd_629342] using wordTrace_append hprefix tailTrace_629342
  have hstable : (prefixWord ++ tailWord_629342).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_629342).length < 2 ^ (prefixWord ++ tailWord_629342).sum := by decide
  have hdescent : baseEnd_629342 < baseStart_629342 := by decide
  rcases family_descends (prefixWord ++ tailWord_629342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_629394 : List Nat := [3, 2, 3, 1, 2, 1, 10]
def baseStart_629394 : Nat := 118140960795 + 629394 * 2 ^ 59
def prefixEnd_629394 : Nat := 4983230072969 + 3 ^ 40 * 629394 * 2
def baseEnd_629394 : Nat := 7979793655704092019271

theorem tailTrace_629394 : CollatzResearch.WordTrace tailWord_629394 prefixEnd_629394 7979793655704092019271 := by
  unfold tailWord_629394
  simp only [CollatzResearch.WordTrace]
  refine ⟨5738971270455126195609809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15303923387880336521626157 5738971270455126195609809)
  ·
    refine ⟨4304228452841344646707357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5738971270455126195609809 4304228452841344646707357)
    ·
      refine ⟨1614085669815504242515259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4304228452841344646707357 1614085669815504242515259)
      ·
        refine ⟨2421128504723256363772889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1614085669815504242515259 2421128504723256363772889)
        ·
          refine ⟨1815846378542442272829667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2421128504723256363772889 1815846378542442272829667)
          ·
            refine ⟨2723769567813663409244501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1815846378542442272829667 2723769567813663409244501)
            ·
              refine ⟨7979793655704092019271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 2723769567813663409244501 7979793655704092019271)
              ·
                rfl

theorem cell22_629394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 10].length) (baseStart_629394 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_629394 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_629394 prefixEnd_629394 := by exact prefixLift 629394
  have htrace : WordTrace (prefixWord ++ tailWord_629394) baseStart_629394 baseEnd_629394 := by
    simpa [prefixWord, tailWord_629394, baseEnd_629394] using wordTrace_append hprefix tailTrace_629394
  have hstable : (prefixWord ++ tailWord_629394).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_629394).length < 2 ^ (prefixWord ++ tailWord_629394).sum := by decide
  have hdescent : baseEnd_629394 < baseStart_629394 := by decide
  rcases family_descends (prefixWord ++ tailWord_629394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_629396 : List Nat := [2, 4, 2, 2, 1, 1, 1, 1, 4, 4]
def baseStart_629396 : Nat := 118140960795 + 629396 * 2 ^ 59
def prefixEnd_629396 : Nat := 4983230072969 + 3 ^ 40 * 629396 * 2
def baseEnd_629396 : Nat := 215455113344883145970311

theorem tailTrace_629396 : CollatzResearch.WordTrace tailWord_629396 prefixEnd_629396 215455113344883145970311 := by
  unfold tailWord_629396
  simp only [CollatzResearch.WordTrace]
  refine ⟨11477979013906629562006021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15303972018542172749341361 11477979013906629562006021)
  ·
    refine ⟨2152121065107493042876129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11477979013906629562006021 2152121065107493042876129)
    ·
      refine ⟨1614090798830619782157097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2152121065107493042876129 1614090798830619782157097)
      ·
        refine ⟨1210568099122964836617823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1614090798830619782157097 1210568099122964836617823)
        ·
          refine ⟨1815852148684447254926735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1210568099122964836617823 1815852148684447254926735)
          ·
            refine ⟨2723778223026670882390103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1815852148684447254926735 2723778223026670882390103)
            ·
              refine ⟨4085667334540006323585155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2723778223026670882390103 4085667334540006323585155)
              ·
                refine ⟨6128501001810009485377733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4085667334540006323585155 6128501001810009485377733)
                ·
                  refine ⟨1149093937839376778508325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6128501001810009485377733 1149093937839376778508325)
                  ·
                    refine ⟨215455113344883145970311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1149093937839376778508325 215455113344883145970311)
                    ·
                      rfl

theorem cell22_629396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 1, 1, 4, 4].length) (baseStart_629396 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_629396 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_629396 prefixEnd_629396 := by exact prefixLift 629396
  have htrace : WordTrace (prefixWord ++ tailWord_629396) baseStart_629396 baseEnd_629396 := by
    simpa [prefixWord, tailWord_629396, baseEnd_629396] using wordTrace_append hprefix tailTrace_629396
  have hstable : (prefixWord ++ tailWord_629396).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_629396).length < 2 ^ (prefixWord ++ tailWord_629396).sum := by decide
  have hdescent : baseEnd_629396 < baseStart_629396 := by decide
  rcases family_descends (prefixWord ++ tailWord_629396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_629415 : List Nat := [1, 1, 6, 3, 1, 1, 1, 3, 2, 3]
def baseStart_629415 : Nat := 118140960795 + 629415 * 2 ^ 59
def prefixEnd_629415 : Nat := 4983230072969 + 3 ^ 40 * 629415 * 2
def baseEnd_629415 : Nat := 215461617433173429745253

theorem tailTrace_629415 : CollatzResearch.WordTrace tailWord_629415 prefixEnd_629415 215461617433173429745253 := by
  unfold tailWord_629415
  simp only [CollatzResearch.WordTrace]
  refine ⟨22956651014744425368953699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15304434009829616912635799 22956651014744425368953699)
  ·
    refine ⟨34434976522116638053430549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22956651014744425368953699 34434976522116638053430549)
    ·
      refine ⟨1614139524474217408754557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 34434976522116638053430549 1614139524474217408754557)
      ·
        refine ⟨605302321677831528282959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1614139524474217408754557 605302321677831528282959)
        ·
          refine ⟨907953482516747292424439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 605302321677831528282959 907953482516747292424439)
          ·
            refine ⟨1361930223775120938636659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 907953482516747292424439 1361930223775120938636659)
            ·
              refine ⟨2042895335662681407954989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1361930223775120938636659 2042895335662681407954989)
              ·
                refine ⟨766085750873505527983121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2042895335662681407954989 766085750873505527983121)
                ·
                  refine ⟨574564313155129145987341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 766085750873505527983121 574564313155129145987341)
                  ·
                    refine ⟨215461617433173429745253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 574564313155129145987341 215461617433173429745253)
                    ·
                      rfl

theorem cell22_629415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 1, 3, 2, 3].length) (baseStart_629415 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_629415 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_629415 prefixEnd_629415 := by exact prefixLift 629415
  have htrace : WordTrace (prefixWord ++ tailWord_629415) baseStart_629415 baseEnd_629415 := by
    simpa [prefixWord, tailWord_629415, baseEnd_629415] using wordTrace_append hprefix tailTrace_629415
  have hstable : (prefixWord ++ tailWord_629415).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_629415).length < 2 ^ (prefixWord ++ tailWord_629415).sum := by decide
  have hdescent : baseEnd_629415 < baseStart_629415 := by decide
  rcases family_descends (prefixWord ++ tailWord_629415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_629430 : List Nat := [5, 1, 3, 1, 2, 1, 2, 1, 2, 4]
def baseStart_629430 : Nat := 118140960795 + 629430 * 2 ^ 59
def prefixEnd_629430 : Nat := 4983230072969 + 3 ^ 40 * 629430 * 2
def baseEnd_629430 : Nat := 215466752239718390620207

theorem tailTrace_629430 : CollatzResearch.WordTrace tailWord_629430 prefixEnd_629430 215466752239718390620207 := by
  unfold tailWord_629430
  simp only [CollatzResearch.WordTrace]
  refine ⟨1434824881855630183171859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 15304798739793388620499829 1434824881855630183171859)
  ·
    refine ⟨2152237322783445274757789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1434824881855630183171859 2152237322783445274757789)
    ·
      refine ⟨807088996043791978034171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2152237322783445274757789 807088996043791978034171)
      ·
        refine ⟨1210633494065687967051257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 807088996043791978034171 1210633494065687967051257)
        ·
          refine ⟨907975120549265975288443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1210633494065687967051257 907975120549265975288443)
          ·
            refine ⟨1361962680823898962932665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 907975120549265975288443 1361962680823898962932665)
            ·
              refine ⟨1021472010617924222199499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1361962680823898962932665 1021472010617924222199499)
              ·
                refine ⟨1532208015926886333299249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1021472010617924222199499 1532208015926886333299249)
                ·
                  refine ⟨1149156011945164749974437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1532208015926886333299249 1149156011945164749974437)
                  ·
                    refine ⟨215466752239718390620207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1149156011945164749974437 215466752239718390620207)
                    ·
                      rfl

theorem cell22_629430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 2, 1, 2, 4].length) (baseStart_629430 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_629430 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_629430 prefixEnd_629430 := by exact prefixLift 629430
  have htrace : WordTrace (prefixWord ++ tailWord_629430) baseStart_629430 baseEnd_629430 := by
    simpa [prefixWord, tailWord_629430, baseEnd_629430] using wordTrace_append hprefix tailTrace_629430
  have hstable : (prefixWord ++ tailWord_629430).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_629430).length < 2 ^ (prefixWord ++ tailWord_629430).sum := by decide
  have hdescent : baseEnd_629430 < baseStart_629430 := by decide
  rcases family_descends (prefixWord ++ tailWord_629430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_629486 : List Nat := [4, 1, 2, 1, 1, 3, 2, 1, 3, 4]
def baseStart_629486 : Nat := 118140960795 + 629486 * 2 ^ 59
def prefixEnd_629486 : Nat := 4983230072969 + 3 ^ 40 * 629486 * 2
def baseEnd_629486 : Nat := 215485922184152911220035

theorem tailTrace_629486 : CollatzResearch.WordTrace tailWord_629486 prefixEnd_629486 215485922184152911220035 := by
  unfold tailWord_629486
  simp only [CollatzResearch.WordTrace]
  refine ⟨2869905074685900561848539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15306160398324802996525541 2869905074685900561848539)
  ·
    refine ⟨4304857612028850842772809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2869905074685900561848539 4304857612028850842772809)
    ·
      refine ⟨3228643209021638132079607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4304857612028850842772809 3228643209021638132079607)
      ·
        refine ⟨4842964813532457198119411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3228643209021638132079607 4842964813532457198119411)
        ·
          refine ⟨7264447220298685797179117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4842964813532457198119411 7264447220298685797179117)
          ·
            refine ⟨2724167707612007173942169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7264447220298685797179117 2724167707612007173942169)
            ·
              refine ⟨2043125780709005380456627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2724167707612007173942169 2043125780709005380456627)
              ·
                refine ⟨3064688671063508070684941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2043125780709005380456627 3064688671063508070684941)
                ·
                  refine ⟨1149258251648815526506853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3064688671063508070684941 1149258251648815526506853)
                  ·
                    refine ⟨215485922184152911220035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1149258251648815526506853 215485922184152911220035)
                    ·
                      rfl

theorem cell22_629486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 2, 1, 3, 4].length) (baseStart_629486 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_629486 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_629486 prefixEnd_629486 := by exact prefixLift 629486
  have htrace : WordTrace (prefixWord ++ tailWord_629486) baseStart_629486 baseEnd_629486 := by
    simpa [prefixWord, tailWord_629486, baseEnd_629486] using wordTrace_append hprefix tailTrace_629486
  have hstable : (prefixWord ++ tailWord_629486).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_629486).length < 2 ^ (prefixWord ++ tailWord_629486).sum := by decide
  have hdescent : baseEnd_629486 < baseStart_629486 := by decide
  rcases family_descends (prefixWord ++ tailWord_629486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_629636 : List Nat := [2, 3, 2, 1, 1, 1, 1, 5, 6]
def baseStart_629636 : Nat := 118140960795 + 629636 * 2 ^ 59
def prefixEnd_629636 : Nat := 4983230072969 + 3 ^ 40 * 629636 * 2
def baseEnd_629636 : Nat := 71845756749867506656525

theorem tailTrace_629636 : CollatzResearch.WordTrace tailWord_629636 prefixEnd_629636 71845756749867506656525 := by
  unfold tailWord_629636
  simp only [CollatzResearch.WordTrace]
  refine ⟨11482355773471890056374381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15309807697962520075165841 11482355773471890056374381)
  ·
    refine ⟨4305883415051958771140393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11482355773471890056374381 4305883415051958771140393)
    ·
      refine ⟨3229412561288969078355295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4305883415051958771140393 3229412561288969078355295)
      ·
        refine ⟨4844118841933453617532943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3229412561288969078355295 4844118841933453617532943)
        ·
          refine ⟨7266178262900180426299415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4844118841933453617532943 7266178262900180426299415)
          ·
            refine ⟨10899267394350270639449123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7266178262900180426299415 10899267394350270639449123)
            ·
              refine ⟨16348901091525405959173685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10899267394350270639449123 16348901091525405959173685)
              ·
                refine ⟨1532709477330506808672533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 16348901091525405959173685 1532709477330506808672533)
                ·
                  refine ⟨71845756749867506656525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1532709477330506808672533 71845756749867506656525)
                  ·
                    rfl

theorem cell22_629636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 5, 6].length) (baseStart_629636 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_629636 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_629636 prefixEnd_629636 := by exact prefixLift 629636
  have htrace : WordTrace (prefixWord ++ tailWord_629636) baseStart_629636 baseEnd_629636 := by
    simpa [prefixWord, tailWord_629636, baseEnd_629636] using wordTrace_append hprefix tailTrace_629636
  have hstable : (prefixWord ++ tailWord_629636).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_629636).length < 2 ^ (prefixWord ++ tailWord_629636).sum := by decide
  have hdescent : baseEnd_629636 < baseStart_629636 := by decide
  rcases family_descends (prefixWord ++ tailWord_629636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_629668 : List Nat := [2, 3, 1, 2, 1, 2, 2, 2, 4, 3]
def baseStart_629668 : Nat := 118140960795 + 629668 * 2 ^ 59
def prefixEnd_629668 : Nat := 4983230072969 + 3 ^ 40 * 629668 * 2
def baseEnd_629668 : Nat := 215548224503565103169477

theorem tailTrace_629668 : CollatzResearch.WordTrace tailWord_629668 prefixEnd_629668 215548224503565103169477 := by
  unfold tailWord_629668
  simp only [CollatzResearch.WordTrace]
  refine ⟨11482939341413924788956829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15310585788551899718609105 11482939341413924788956829)
  ·
    refine ⟨4306102253030221795858811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11482939341413924788956829 4306102253030221795858811)
    ·
      refine ⟨6459153379545332693788217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4306102253030221795858811 6459153379545332693788217)
      ·
        refine ⟨4844365034658999520341163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6459153379545332693788217 4844365034658999520341163)
        ·
          refine ⟨7266547551988499280511745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4844365034658999520341163 7266547551988499280511745)
          ·
            refine ⟨5449910663991374460383809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7266547551988499280511745 5449910663991374460383809)
            ·
              refine ⟨4087432997993530845287857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5449910663991374460383809 4087432997993530845287857)
              ·
                refine ⟨3065574748495148133965893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4087432997993530845287857 3065574748495148133965893)
                ·
                  refine ⟨574795265342840275118605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3065574748495148133965893 574795265342840275118605)
                  ·
                    refine ⟨215548224503565103169477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 574795265342840275118605 215548224503565103169477)
                    ·
                      rfl

theorem cell22_629668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 2, 2, 4, 3].length) (baseStart_629668 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_629668 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_629668 prefixEnd_629668 := by exact prefixLift 629668
  have htrace : WordTrace (prefixWord ++ tailWord_629668) baseStart_629668 baseEnd_629668 := by
    simpa [prefixWord, tailWord_629668, baseEnd_629668] using wordTrace_append hprefix tailTrace_629668
  have hstable : (prefixWord ++ tailWord_629668).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_629668).length < 2 ^ (prefixWord ++ tailWord_629668).sum := by decide
  have hdescent : baseEnd_629668 < baseStart_629668 := by decide
  rcases family_descends (prefixWord ++ tailWord_629668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_629713 : List Nat := [1, 2, 2, 1, 2, 1, 3, 4, 3, 3]
def baseStart_629713 : Nat := 118140960795 + 629713 * 2 ^ 59
def prefixEnd_629713 : Nat := 4983230072969 + 3 ^ 40 * 629713 * 2
def baseEnd_629713 : Nat := 215563628923199985794339

theorem tailTrace_629713 : CollatzResearch.WordTrace tailWord_629713 prefixEnd_629713 215563628923199985794339 := by
  unfold tailWord_629713
  simp only [CollatzResearch.WordTrace]
  refine ⟨22967519967664822263301793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15311679978443214842201195 22967519967664822263301793)
  ·
    refine ⟨17225639975748616697476345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22967519967664822263301793 17225639975748616697476345)
    ·
      refine ⟨12919229981811462523107259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17225639975748616697476345 12919229981811462523107259)
      ·
        refine ⟨19378844972717193784660889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12919229981811462523107259 19378844972717193784660889)
        ·
          refine ⟨14534133729537895338495667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19378844972717193784660889 14534133729537895338495667)
          ·
            refine ⟨21801200594306843007743501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14534133729537895338495667 21801200594306843007743501)
            ·
              refine ⟨8175450222865066127903813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21801200594306843007743501 8175450222865066127903813)
              ·
                refine ⟨1532896916787199898981965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8175450222865066127903813 1532896916787199898981965)
                ·
                  refine ⟨574836343795199962118237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1532896916787199898981965 574836343795199962118237)
                  ·
                    refine ⟨215563628923199985794339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 574836343795199962118237 215563628923199985794339)
                    ·
                      rfl

theorem cell22_629713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 4, 3, 3].length) (baseStart_629713 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_629713 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_629713 prefixEnd_629713 := by exact prefixLift 629713
  have htrace : WordTrace (prefixWord ++ tailWord_629713) baseStart_629713 baseEnd_629713 := by
    simpa [prefixWord, tailWord_629713, baseEnd_629713] using wordTrace_append hprefix tailTrace_629713
  have hstable : (prefixWord ++ tailWord_629713).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_629713).length < 2 ^ (prefixWord ++ tailWord_629713).sum := by decide
  have hdescent : baseEnd_629713 < baseStart_629713 := by decide
  rcases family_descends (prefixWord ++ tailWord_629713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_629818 : List Nat := [3, 1, 1, 1, 3, 1, 2, 2, 4, 4]
def baseStart_629818 : Nat := 118140960795 + 629818 * 2 ^ 59
def prefixEnd_629818 : Nat := 4983230072969 + 3 ^ 40 * 629818 * 2
def baseEnd_629818 : Nat := 215599572569014711919017

theorem tailTrace_629818 : CollatzResearch.WordTrace tailWord_629818 prefixEnd_629818 215599572569014711919017 := by
  unfold tailWord_629818
  simp only [CollatzResearch.WordTrace]
  refine ⟨5742837408071106298968527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15314233088189616797249405 5742837408071106298968527)
  ·
    refine ⟨8614256112106659448452791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5742837408071106298968527 8614256112106659448452791)
    ·
      refine ⟨12921384168159989172679187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8614256112106659448452791 12921384168159989172679187)
      ·
        refine ⟨19382076252239983759018781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12921384168159989172679187 19382076252239983759018781)
        ·
          refine ⟨7268278594589993909632043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19382076252239983759018781 7268278594589993909632043)
          ·
            refine ⟨10902417891884990864448065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7268278594589993909632043 10902417891884990864448065)
            ·
              refine ⟨8176813418913743148336049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10902417891884990864448065 8176813418913743148336049)
              ·
                refine ⟨6132610064185307361252037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8176813418913743148336049 6132610064185307361252037)
                ·
                  refine ⟨1149864387034745130234757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6132610064185307361252037 1149864387034745130234757)
                  ·
                    refine ⟨215599572569014711919017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1149864387034745130234757 215599572569014711919017)
                    ·
                      rfl

theorem cell22_629818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 2, 4, 4].length) (baseStart_629818 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_629818 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_629818 prefixEnd_629818 := by exact prefixLift 629818
  have htrace : WordTrace (prefixWord ++ tailWord_629818) baseStart_629818 baseEnd_629818 := by
    simpa [prefixWord, tailWord_629818, baseEnd_629818] using wordTrace_append hprefix tailTrace_629818
  have hstable : (prefixWord ++ tailWord_629818).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_629818).length < 2 ^ (prefixWord ++ tailWord_629818).sum := by decide
  have hdescent : baseEnd_629818 < baseStart_629818 := by decide
  rcases family_descends (prefixWord ++ tailWord_629818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_629820 : List Nat := [2, 2, 2, 2, 2, 3, 2, 1, 1, 5]
def baseStart_629820 : Nat := 118140960795 + 629820 * 2 ^ 59
def prefixEnd_629820 : Nat := 4983230072969 + 3 ^ 40 * 629820 * 2
def baseEnd_629820 : Nat := 215600257209887373369011

theorem tailTrace_629820 : CollatzResearch.WordTrace tailWord_629820 prefixEnd_629820 215600257209887373369011 := by
  unfold tailWord_629820
  simp only [CollatzResearch.WordTrace]
  refine ⟨11485711289138589768723457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15314281718851453024964609 11485711289138589768723457)
  ·
    refine ⟨8614283466853942326542593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11485711289138589768723457 8614283466853942326542593)
    ·
      refine ⟨6460712600140456744906945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8614283466853942326542593 6460712600140456744906945)
      ·
        refine ⟨4845534450105342558680209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6460712600140456744906945 4845534450105342558680209)
        ·
          refine ⟨3634150837579006919010157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4845534450105342558680209 3634150837579006919010157)
          ·
            refine ⟨1362806564092127594628809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3634150837579006919010157 1362806564092127594628809)
            ·
              refine ⟨1022104923069095695971607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1362806564092127594628809 1022104923069095695971607)
              ·
                refine ⟨1533157384603643543957411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1022104923069095695971607 1533157384603643543957411)
                ·
                  refine ⟨2299736076905465315936117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1533157384603643543957411 2299736076905465315936117)
                  ·
                    refine ⟨215600257209887373369011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2299736076905465315936117 215600257209887373369011)
                    ·
                      rfl

theorem cell22_629820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 2, 1, 1, 5].length) (baseStart_629820 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_629820 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_629820 prefixEnd_629820 := by exact prefixLift 629820
  have htrace : WordTrace (prefixWord ++ tailWord_629820) baseStart_629820 baseEnd_629820 := by
    simpa [prefixWord, tailWord_629820, baseEnd_629820] using wordTrace_append hprefix tailTrace_629820
  have hstable : (prefixWord ++ tailWord_629820).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_629820).length < 2 ^ (prefixWord ++ tailWord_629820).sum := by decide
  have hdescent : baseEnd_629820 < baseStart_629820 := by decide
  rcases family_descends (prefixWord ++ tailWord_629820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_629865 : List Nat := [1, 2, 1, 1, 1, 6, 1, 3, 3, 3]
def baseStart_629865 : Nat := 118140960795 + 629865 * 2 ^ 59
def prefixEnd_629865 : Nat := 4983230072969 + 3 ^ 40 * 629865 * 2
def baseEnd_629865 : Nat := 215615661629522255993873

theorem tailTrace_629865 : CollatzResearch.WordTrace tailWord_629865 prefixEnd_629865 215615661629522255993873 := by
  unfold tailWord_629865
  simp only [CollatzResearch.WordTrace]
  refine ⟨22973063863114152222835049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15315375908742768148556699 22973063863114152222835049)
  ·
    refine ⟨17229797897335614167126287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22973063863114152222835049 17229797897335614167126287)
    ·
      refine ⟨25844696846003421250689431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17229797897335614167126287 25844696846003421250689431)
      ·
        refine ⟨38767045269005131876034147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25844696846003421250689431 38767045269005131876034147)
        ·
          refine ⟨58150567903507697814051221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38767045269005131876034147 58150567903507697814051221)
          ·
            refine ⟨2725807870476923335033651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 58150567903507697814051221 2725807870476923335033651)
            ·
              refine ⟨4088711805715385002550477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2725807870476923335033651 4088711805715385002550477)
              ·
                refine ⟨1533266927143269375956429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4088711805715385002550477 1533266927143269375956429)
                ·
                  refine ⟨574975097678726015983661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1533266927143269375956429 574975097678726015983661)
                  ·
                    refine ⟨215615661629522255993873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 574975097678726015983661 215615661629522255993873)
                    ·
                      rfl

theorem cell22_629865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 1, 3, 3, 3].length) (baseStart_629865 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_629865 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_629865 prefixEnd_629865 := by exact prefixLift 629865
  have htrace : WordTrace (prefixWord ++ tailWord_629865) baseStart_629865 baseEnd_629865 := by
    simpa [prefixWord, tailWord_629865, baseEnd_629865] using wordTrace_append hprefix tailTrace_629865
  have hstable : (prefixWord ++ tailWord_629865).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_629865).length < 2 ^ (prefixWord ++ tailWord_629865).sum := by decide
  have hdescent : baseEnd_629865 < baseStart_629865 := by decide
  rcases family_descends (prefixWord ++ tailWord_629865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_629916 : List Nat := [2, 2, 3, 2, 1, 3, 3, 2, 1, 3]
def baseStart_629916 : Nat := 118140960795 + 629916 * 2 ^ 59
def prefixEnd_629916 : Nat := 4983230072969 + 3 ^ 40 * 629916 * 2
def baseEnd_629916 : Nat := 215633119971775122968717

theorem tailTrace_629916 : CollatzResearch.WordTrace tailWord_629916 prefixEnd_629916 215633119971775122968717 := by
  unfold tailWord_629916
  simp only [CollatzResearch.WordTrace]
  refine ⟨11487461992964693966470801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15316615990619591955294401 11487461992964693966470801)
  ·
    refine ⟨8615596494723520474853101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11487461992964693966470801 8615596494723520474853101)
    ·
      refine ⟨3230848685521320178069913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8615596494723520474853101 3230848685521320178069913)
      ·
        refine ⟨2423136514140990133552435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3230848685521320178069913 2423136514140990133552435)
        ·
          refine ⟨3634704771211485200328653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2423136514140990133552435 3634704771211485200328653)
          ·
            refine ⟨1363014289204306950123245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3634704771211485200328653 1363014289204306950123245)
            ·
              refine ⟨511130358451615106296217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1363014289204306950123245 511130358451615106296217)
              ·
                refine ⟨383347768838711329722163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 511130358451615106296217 383347768838711329722163)
                ·
                  refine ⟨575021653258066994583245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 383347768838711329722163 575021653258066994583245)
                  ·
                    refine ⟨215633119971775122968717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 575021653258066994583245 215633119971775122968717)
                    ·
                      rfl

theorem cell22_629916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 3, 2, 1, 3].length) (baseStart_629916 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_629916 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_629916 prefixEnd_629916 := by exact prefixLift 629916
  have htrace : WordTrace (prefixWord ++ tailWord_629916) baseStart_629916 baseEnd_629916 := by
    simpa [prefixWord, tailWord_629916, baseEnd_629916] using wordTrace_append hprefix tailTrace_629916
  have hstable : (prefixWord ++ tailWord_629916).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_629916).length < 2 ^ (prefixWord ++ tailWord_629916).sum := by decide
  have hdescent : baseEnd_629916 < baseStart_629916 := by decide
  rcases family_descends (prefixWord ++ tailWord_629916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_629955 : List Nat := [1, 1, 1, 3, 1, 1, 1, 6, 4, 3]
def baseStart_629955 : Nat := 118140960795 + 629955 * 2 ^ 59
def prefixEnd_629955 : Nat := 4983230072969 + 3 ^ 40 * 629955 * 2
def baseEnd_629955 : Nat := 215646470468792021243597

theorem tailTrace_629955 : CollatzResearch.WordTrace tailWord_629955 prefixEnd_629955 215646470468792021243597 := by
  unfold tailWord_629955
  simp only [CollatzResearch.WordTrace]
  refine ⟨22976346432788097593611319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15317564288525398395740879 22976346432788097593611319)
  ·
    refine ⟨34464519649182146390416979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22976346432788097593611319 34464519649182146390416979)
    ·
      refine ⟨51696779473773219585625469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34464519649182146390416979 51696779473773219585625469)
      ·
        refine ⟨19386292302664957344609551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51696779473773219585625469 19386292302664957344609551)
        ·
          refine ⟨29079438453997436016914327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19386292302664957344609551 29079438453997436016914327)
          ·
            refine ⟨43619157680996154025371491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29079438453997436016914327 43619157680996154025371491)
            ·
              refine ⟨65428736521494231038057237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43619157680996154025371491 65428736521494231038057237)
              ·
                refine ⟨3066972024445042079908933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 65428736521494231038057237 3066972024445042079908933)
                ·
                  refine ⟨575057254583445389982925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3066972024445042079908933 575057254583445389982925)
                  ·
                    refine ⟨215646470468792021243597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 575057254583445389982925 215646470468792021243597)
                    ·
                      rfl

theorem cell22_629955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 6, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 6, 4, 3].length) (baseStart_629955 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_629955 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_629955 prefixEnd_629955 := by exact prefixLift 629955
  have htrace : WordTrace (prefixWord ++ tailWord_629955) baseStart_629955 baseEnd_629955 := by
    simpa [prefixWord, tailWord_629955, baseEnd_629955] using wordTrace_append hprefix tailTrace_629955
  have hstable : (prefixWord ++ tailWord_629955).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_629955).length < 2 ^ (prefixWord ++ tailWord_629955).sum := by decide
  have hdescent : baseEnd_629955 < baseStart_629955 := by decide
  rcases family_descends (prefixWord ++ tailWord_629955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_629985 : List Nat := [1, 2, 3, 1, 3, 2, 3, 7]
def baseStart_629985 : Nat := 118140960795 + 629985 * 2 ^ 59
def prefixEnd_629985 : Nat := 4983230072969 + 3 ^ 40 * 629985 * 2
def baseEnd_629985 : Nat := 23961860009097993665945

theorem tailTrace_629985 : CollatzResearch.WordTrace tailWord_629985 prefixEnd_629985 23961860009097993665945 := by
  unfold tailWord_629985
  simp only [CollatzResearch.WordTrace]
  refine ⟨22977440622679412717203409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15318293748452941811468939 22977440622679412717203409)
  ·
    refine ⟨17233080467009559537902557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22977440622679412717203409 17233080467009559537902557)
    ·
      refine ⟨6462405175128584826713459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17233080467009559537902557 6462405175128584826713459)
      ·
        refine ⟨9693607762692877240070189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6462405175128584826713459 9693607762692877240070189)
        ·
          refine ⟨3635102911009828965026321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9693607762692877240070189 3635102911009828965026321)
          ·
            refine ⟨2726327183257371723769741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3635102911009828965026321 2726327183257371723769741)
            ·
              refine ⟨1022372693721514396413653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2726327183257371723769741 1022372693721514396413653)
              ·
                refine ⟨23961860009097993665945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1022372693721514396413653 23961860009097993665945)
                ·
                  rfl

theorem cell22_629985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 3, 7].length) (baseStart_629985 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_629985 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_629985 prefixEnd_629985 := by exact prefixLift 629985
  have htrace : WordTrace (prefixWord ++ tailWord_629985) baseStart_629985 baseEnd_629985 := by
    simpa [prefixWord, tailWord_629985, baseEnd_629985] using wordTrace_append hprefix tailTrace_629985
  have hstable : (prefixWord ++ tailWord_629985).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_629985).length < 2 ^ (prefixWord ++ tailWord_629985).sum := by decide
  have hdescent : baseEnd_629985 < baseStart_629985 := by decide
  rcases family_descends (prefixWord ++ tailWord_629985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_630092 : List Nat := [2, 2, 1, 3, 2, 2, 3, 1, 6]
def baseStart_630092 : Nat := 118140960795 + 630092 * 2 ^ 59
def prefixEnd_630092 : Nat := 4983230072969 + 3 ^ 40 * 630092 * 2
def baseEnd_630092 : Nat := 71897789456189776856059

theorem tailTrace_630092 : CollatzResearch.WordTrace tailWord_630092 prefixEnd_630092 71897789456189776856059 := by
  unfold tailWord_630092
  simp only [CollatzResearch.WordTrace]
  refine ⟨11490671616645884995674265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15320895488861179994232353 11490671616645884995674265)
  ·
    refine ⟨8618003712484413746755699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11490671616645884995674265 8618003712484413746755699)
    ·
      refine ⟨12927005568726620620133549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8618003712484413746755699 12927005568726620620133549)
      ·
        refine ⟨4847627088272482732550081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12927005568726620620133549 4847627088272482732550081)
        ·
          refine ⟨3635720316204362049412561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4847627088272482732550081 3635720316204362049412561)
          ·
            refine ⟨2726790237153271537059421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3635720316204362049412561 2726790237153271537059421)
            ·
              refine ⟨1022546338932476826397283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2726790237153271537059421 1022546338932476826397283)
              ·
                refine ⟨1533819508398715239595925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1022546338932476826397283 1533819508398715239595925)
                ·
                  refine ⟨71897789456189776856059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1533819508398715239595925 71897789456189776856059)
                  ·
                    rfl

theorem cell22_630092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 3, 1, 6].length) (baseStart_630092 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_630092 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_630092 prefixEnd_630092 := by exact prefixLift 630092
  have htrace : WordTrace (prefixWord ++ tailWord_630092) baseStart_630092 baseEnd_630092 := by
    simpa [prefixWord, tailWord_630092, baseEnd_630092] using wordTrace_append hprefix tailTrace_630092
  have hstable : (prefixWord ++ tailWord_630092).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_630092).length < 2 ^ (prefixWord ++ tailWord_630092).sum := by decide
  have hdescent : baseEnd_630092 < baseStart_630092 := by decide
  rcases family_descends (prefixWord ++ tailWord_630092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_630105 : List Nat := [1, 2, 1, 2, 2, 2, 2, 1, 3, 6]
def baseStart_630105 : Nat := 118140960795 + 630105 * 2 ^ 59
def prefixEnd_630105 : Nat := 4983230072969 + 3 ^ 40 * 630105 * 2
def baseEnd_630105 : Nat := 215697818534241629993137

theorem tailTrace_630105 : CollatzResearch.WordTrace tailWord_630105 prefixEnd_630105 215697818534241629993137 := by
  unfold tailWord_630105
  simp only [CollatzResearch.WordTrace]
  refine ⟨22981817382244673211571769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15321211588163115474381179 22981817382244673211571769)
  ·
    refine ⟨17236363036683504908678827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22981817382244673211571769 17236363036683504908678827)
    ·
      refine ⟨25854544555025257363018241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17236363036683504908678827 25854544555025257363018241)
      ·
        refine ⟨19390908416268943022263681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25854544555025257363018241 19390908416268943022263681)
        ·
          refine ⟨14543181312201707266697761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19390908416268943022263681 14543181312201707266697761)
          ·
            refine ⟨10907385984151280450023321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14543181312201707266697761 10907385984151280450023321)
            ·
              refine ⟨8180539488113460337517491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10907385984151280450023321 8180539488113460337517491)
              ·
                refine ⟨12270809232170190506276237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8180539488113460337517491 12270809232170190506276237)
                ·
                  refine ⟨4601553462063821439853589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12270809232170190506276237 4601553462063821439853589)
                  ·
                    refine ⟨215697818534241629993137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4601553462063821439853589 215697818534241629993137)
                    ·
                      rfl

theorem cell22_630105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 1, 3, 6].length) (baseStart_630105 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_630105 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_630105 prefixEnd_630105 := by exact prefixLift 630105
  have htrace : WordTrace (prefixWord ++ tailWord_630105) baseStart_630105 baseEnd_630105 := by
    simpa [prefixWord, tailWord_630105, baseEnd_630105] using wordTrace_append hprefix tailTrace_630105
  have hstable : (prefixWord ++ tailWord_630105).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_630105).length < 2 ^ (prefixWord ++ tailWord_630105).sum := by decide
  have hdescent : baseEnd_630105 < baseStart_630105 := by decide
  rcases family_descends (prefixWord ++ tailWord_630105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_630169 : List Nat := [1, 2, 1, 2, 1, 6, 1, 2, 3, 3]
def baseStart_630169 : Nat := 118140960795 + 630169 * 2 ^ 59
def prefixEnd_630169 : Nat := 4983230072969 + 3 ^ 40 * 630169 * 2
def baseEnd_630169 : Nat := 215719727042166796392941

theorem tailTrace_630169 : CollatzResearch.WordTrace tailWord_630169 prefixEnd_630169 215719727042166796392941 := by
  unfold tailWord_630169
  simp only [CollatzResearch.WordTrace]
  refine ⟨22984151654012812141901561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15322767769341874761267707 22984151654012812141901561)
  ·
    refine ⟨17238113740509609106426171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22984151654012812141901561 17238113740509609106426171)
    ·
      refine ⟨25857170610764413659639257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17238113740509609106426171 25857170610764413659639257)
      ·
        refine ⟨19392877958073310244729443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25857170610764413659639257 19392877958073310244729443)
        ·
          refine ⟨29089316937109965367094165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19392877958073310244729443 29089316937109965367094165)
          ·
            refine ⟨1363561731427029626582539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 29089316937109965367094165 1363561731427029626582539)
            ·
              refine ⟨2045342597140544439873809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1363561731427029626582539 2045342597140544439873809)
              ·
                refine ⟨1534006947855408329905357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2045342597140544439873809 1534006947855408329905357)
                ·
                  refine ⟨575252605445778123714509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1534006947855408329905357 575252605445778123714509)
                  ·
                    refine ⟨215719727042166796392941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 575252605445778123714509 215719727042166796392941)
                    ·
                      rfl

theorem cell22_630169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 1, 2, 3, 3].length) (baseStart_630169 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_630169 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_630169 prefixEnd_630169 := by exact prefixLift 630169
  have htrace : WordTrace (prefixWord ++ tailWord_630169) baseStart_630169 baseEnd_630169 := by
    simpa [prefixWord, tailWord_630169, baseEnd_630169] using wordTrace_append hprefix tailTrace_630169
  have hstable : (prefixWord ++ tailWord_630169).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_630169).length < 2 ^ (prefixWord ++ tailWord_630169).sum := by decide
  have hdescent : baseEnd_630169 < baseStart_630169 := by decide
  rcases family_descends (prefixWord ++ tailWord_630169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_630261 : List Nat := [1, 3, 5, 1, 1, 1, 3, 1, 6]
def baseStart_630261 : Nat := 118140960795 + 630261 * 2 ^ 59
def prefixEnd_630261 : Nat := 4983230072969 + 3 ^ 40 * 630261 * 2
def baseEnd_630261 : Nat := 71917073507436407697553

theorem tailTrace_630261 : CollatzResearch.WordTrace tailWord_630261 prefixEnd_630261 71917073507436407697553 := by
  unfold tailWord_630261
  simp only [CollatzResearch.WordTrace]
  refine ⟨22987507169679511854250637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15325004779786341236167091 22987507169679511854250637)
  ·
    refine ⟨8620315188629816945343989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22987507169679511854250637 8620315188629816945343989)
    ·
      refine ⟨808154548934045338625999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 8620315188629816945343989 808154548934045338625999)
      ·
        refine ⟨1212231823401068007938999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 808154548934045338625999 1212231823401068007938999)
        ·
          refine ⟨1818347735101602011908499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1212231823401068007938999 1818347735101602011908499)
          ·
            refine ⟨2727521602652403017862749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1818347735101602011908499 2727521602652403017862749)
            ·
              refine ⟨1022820600994651131698531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2727521602652403017862749 1022820600994651131698531)
              ·
                refine ⟨1534230901491976697547797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1022820600994651131698531 1534230901491976697547797)
                ·
                  refine ⟨71917073507436407697553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1534230901491976697547797 71917073507436407697553)
                  ·
                    rfl

theorem cell22_630261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 3, 1, 6].length) (baseStart_630261 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_630261 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_630261 prefixEnd_630261 := by exact prefixLift 630261
  have htrace : WordTrace (prefixWord ++ tailWord_630261) baseStart_630261 baseEnd_630261 := by
    simpa [prefixWord, tailWord_630261, baseEnd_630261] using wordTrace_append hprefix tailTrace_630261
  have hstable : (prefixWord ++ tailWord_630261).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_630261).length < 2 ^ (prefixWord ++ tailWord_630261).sum := by decide
  have hdescent : baseEnd_630261 < baseStart_630261 := by decide
  rcases family_descends (prefixWord ++ tailWord_630261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_630312 : List Nat := [2, 1, 5, 2, 3, 1, 2, 2, 4]
def baseStart_630312 : Nat := 118140960795 + 630312 * 2 ^ 59
def prefixEnd_630312 : Nat := 4983230072969 + 3 ^ 40 * 630312 * 2
def baseEnd_630312 : Nat := 71922892954854030022501

theorem tailTrace_630312 : CollatzResearch.WordTrace tailWord_630312 prefixEnd_630312 71922892954854030022501 := by
  unfold tailWord_630312
  simp only [CollatzResearch.WordTrace]
  refine ⟨11494683646247373782178595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15326244861663165042904793 11494683646247373782178595)
  ·
    refine ⟨17242025469371060673267893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11494683646247373782178595 17242025469371060673267893)
    ·
      refine ⟨1616439887753536938118865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 17242025469371060673267893 1616439887753536938118865)
      ·
        refine ⟨1212329915815152703589149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1616439887753536938118865 1212329915815152703589149)
        ·
          refine ⟨454623718430682263845931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1212329915815152703589149 454623718430682263845931)
          ·
            refine ⟨681935577646023395768897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 454623718430682263845931 681935577646023395768897)
            ·
              refine ⟨511451683234517546826673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 681935577646023395768897 511451683234517546826673)
              ·
                refine ⟨383588762425888160120005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 511451683234517546826673 383588762425888160120005)
                ·
                  refine ⟨71922892954854030022501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 383588762425888160120005 71922892954854030022501)
                  ·
                    rfl

theorem cell22_630312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 3, 1, 2, 2, 4].length) (baseStart_630312 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_630312 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_630312 prefixEnd_630312 := by exact prefixLift 630312
  have htrace : WordTrace (prefixWord ++ tailWord_630312) baseStart_630312 baseEnd_630312 := by
    simpa [prefixWord, tailWord_630312, baseEnd_630312] using wordTrace_append hprefix tailTrace_630312
  have hstable : (prefixWord ++ tailWord_630312).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_630312).length < 2 ^ (prefixWord ++ tailWord_630312).sum := by decide
  have hdescent : baseEnd_630312 < baseStart_630312 := by decide
  rcases family_descends (prefixWord ++ tailWord_630312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_630342 : List Nat := [6, 1, 1, 1, 4, 1, 1, 1, 2, 4]
def baseStart_630342 : Nat := 118140960795 + 630342 * 2 ^ 59
def prefixEnd_630342 : Nat := 4983230072969 + 3 ^ 40 * 630342 * 2
def baseEnd_630342 : Nat := 215778948477652011817411

theorem tailTrace_630342 : CollatzResearch.WordTrace tailWord_630342 prefixEnd_630342 215778948477652011817411 := by
  unfold tailWord_630342
  simp only [CollatzResearch.WordTrace]
  refine ⟨718451921324564458998415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 15326974321590708458632853 718451921324564458998415)
  ·
    refine ⟨1077677881986846688497623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 718451921324564458998415 1077677881986846688497623)
    ·
      refine ⟨1616516822980270032746435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1077677881986846688497623 1616516822980270032746435)
      ·
        refine ⟨2424775234470405049119653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1616516822980270032746435 2424775234470405049119653)
        ·
          refine ⟨454645356463200946709935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2424775234470405049119653 454645356463200946709935)
          ·
            refine ⟨681968034694801420064903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 454645356463200946709935 681968034694801420064903)
            ·
              refine ⟨1022952052042202130097355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 681968034694801420064903 1022952052042202130097355)
              ·
                refine ⟨1534428078063303195146033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1022952052042202130097355 1534428078063303195146033)
                ·
                  refine ⟨1150821058547477396359525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1534428078063303195146033 1150821058547477396359525)
                  ·
                    refine ⟨215778948477652011817411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1150821058547477396359525 215778948477652011817411)
                    ·
                      rfl

theorem cell22_630342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 4, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 4, 1, 1, 1, 2, 4].length) (baseStart_630342 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_630342 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_630342 prefixEnd_630342 := by exact prefixLift 630342
  have htrace : WordTrace (prefixWord ++ tailWord_630342) baseStart_630342 baseEnd_630342 := by
    simpa [prefixWord, tailWord_630342, baseEnd_630342] using wordTrace_append hprefix tailTrace_630342
  have hstable : (prefixWord ++ tailWord_630342).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_630342).length < 2 ^ (prefixWord ++ tailWord_630342).sum := by decide
  have hdescent : baseEnd_630342 < baseStart_630342 := by decide
  rcases family_descends (prefixWord ++ tailWord_630342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_630394 : List Nat := [3, 1, 1, 1, 1, 1, 1, 7, 1, 5]
def baseStart_630394 : Nat := 118140960795 + 630394 * 2 ^ 59
def prefixEnd_630394 : Nat := 4983230072969 + 3 ^ 40 * 630394 * 2
def baseEnd_630394 : Nat := 215796749140341209517251

theorem tailTrace_630394 : CollatzResearch.WordTrace tailWord_630394 prefixEnd_630394 215796749140341209517251 := by
  unfold tailWord_630394
  simp only [CollatzResearch.WordTrace]
  refine ⟨5748089519549418892210559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15328238718798450379228157 5748089519549418892210559)
  ·
    refine ⟨8622134279324128338315839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5748089519549418892210559 8622134279324128338315839)
    ·
      refine ⟨12933201418986192507473759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8622134279324128338315839 12933201418986192507473759)
      ·
        refine ⟨19399802128479288761210639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12933201418986192507473759 19399802128479288761210639)
        ·
          refine ⟨29099703192718933141815959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19399802128479288761210639 29099703192718933141815959)
          ·
            refine ⟨43649554789078399712723939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29099703192718933141815959 43649554789078399712723939)
            ·
              refine ⟨65474332183617599569085909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43649554789078399712723939 65474332183617599569085909)
              ·
                refine ⟨1534554660553537489900451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 65474332183617599569085909 1534554660553537489900451)
                ·
                  refine ⟨2301831990830306234850677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1534554660553537489900451 2301831990830306234850677)
                  ·
                    refine ⟨215796749140341209517251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2301831990830306234850677 215796749140341209517251)
                    ·
                      rfl

theorem cell22_630394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 7, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 7, 1, 5].length) (baseStart_630394 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_630394 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_630394 prefixEnd_630394 := by exact prefixLift 630394
  have htrace : WordTrace (prefixWord ++ tailWord_630394) baseStart_630394 baseEnd_630394 := by
    simpa [prefixWord, tailWord_630394, baseEnd_630394] using wordTrace_append hprefix tailTrace_630394
  have hstable : (prefixWord ++ tailWord_630394).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_630394).length < 2 ^ (prefixWord ++ tailWord_630394).sum := by decide
  have hdescent : baseEnd_630394 < baseStart_630394 := by decide
  rcases family_descends (prefixWord ++ tailWord_630394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
