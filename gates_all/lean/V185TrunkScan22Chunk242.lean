import V185TrunkScan22Chunk241

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_2157579 : List Nat := [1, 1, 1, 1, 6, 2, 1, 1, 2, 6]
def baseStart_2157579 : Nat := 118140960795 + 2157579 * 2 ^ 59
def prefixEnd_2157579 : Nat := 4983230072969 + 3 ^ 40 * 2157579 * 2
def baseEnd_2157579 : Nat := 738583384698079463959987

theorem tailTrace_2157579 : CollatzResearch.WordTrace tailWord_2157579 prefixEnd_2157579 738583384698079463959987 := by
  unfold tailWord_2157579
  simp only [CollatzResearch.WordTrace]
  refine ⟨78693371050467243001707791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52462247366978162001138527 78693371050467243001707791)
  ·
    refine ⟨118040056575700864502561687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78693371050467243001707791 118040056575700864502561687)
    ·
      refine ⟨177060084863551296753842531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118040056575700864502561687 177060084863551296753842531)
      ·
        refine ⟨265590127295326945130763797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 177060084863551296753842531 265590127295326945130763797)
        ·
          refine ⟨12449537216968450553004553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 265590127295326945130763797 12449537216968450553004553)
          ·
            refine ⟨9337152912726337914753415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12449537216968450553004553 9337152912726337914753415)
            ·
              refine ⟨14005729369089506872130123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9337152912726337914753415 14005729369089506872130123)
              ·
                refine ⟨21008594053634260308195185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14005729369089506872130123 21008594053634260308195185)
                ·
                  refine ⟨15756445540225695231146389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21008594053634260308195185 15756445540225695231146389)
                  ·
                    refine ⟨738583384698079463959987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15756445540225695231146389 738583384698079463959987)
                    ·
                      rfl

theorem cell22_2157579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 1, 1, 2, 6].length) (baseStart_2157579 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2157579 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2157579 prefixEnd_2157579 := by exact prefixLift 2157579
  have htrace : WordTrace (prefixWord ++ tailWord_2157579) baseStart_2157579 baseEnd_2157579 := by
    simpa [prefixWord, tailWord_2157579, baseEnd_2157579] using wordTrace_append hprefix tailTrace_2157579
  have hstable : (prefixWord ++ tailWord_2157579).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2157579).length < 2 ^ (prefixWord ++ tailWord_2157579).sum := by decide
  have hdescent : baseEnd_2157579 < baseStart_2157579 := by decide
  rcases family_descends (prefixWord ++ tailWord_2157579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2157628 : List Nat := [2, 2, 2, 2, 2, 4, 1, 2, 5]
def baseStart_2157628 : Nat := 118140960795 + 2157628 * 2 ^ 59
def prefixEnd_2157628 : Nat := 4983230072969 + 3 ^ 40 * 2157628 * 2
def baseEnd_2157628 : Nat := 246200052799819889828279

theorem tailTrace_2157628 : CollatzResearch.WordTrace tailWord_2157628 prefixEnd_2157628 246200052799819889828279 := by
  unfold tailWord_2157628
  simp only [CollatzResearch.WordTrace]
  refine ⟨39347579113644862185120769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52463438818193149580161025 39347579113644862185120769)
  ·
    refine ⟨29510684335233646638840577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39347579113644862185120769 29510684335233646638840577)
    ·
      refine ⟨22133013251425234979130433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29510684335233646638840577 22133013251425234979130433)
      ·
        refine ⟨16599759938568926234347825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22133013251425234979130433 16599759938568926234347825)
        ·
          refine ⟨12449819953926694675760869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16599759938568926234347825 12449819953926694675760869)
          ·
            refine ⟨2334341241361255251705163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12449819953926694675760869 2334341241361255251705163)
            ·
              refine ⟨3501511862041882877557745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2334341241361255251705163 3501511862041882877557745)
              ·
                refine ⟨2626133896531412158168309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3501511862041882877557745 2626133896531412158168309)
                ·
                  refine ⟨246200052799819889828279, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2626133896531412158168309 246200052799819889828279)
                  ·
                    rfl

theorem cell22_2157628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 4, 1, 2, 5].length) (baseStart_2157628 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2157628 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2157628 prefixEnd_2157628 := by exact prefixLift 2157628
  have htrace : WordTrace (prefixWord ++ tailWord_2157628) baseStart_2157628 baseEnd_2157628 := by
    simpa [prefixWord, tailWord_2157628, baseEnd_2157628] using wordTrace_append hprefix tailTrace_2157628
  have hstable : (prefixWord ++ tailWord_2157628).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2157628).length < 2 ^ (prefixWord ++ tailWord_2157628).sum := by decide
  have hdescent : baseEnd_2157628 < baseStart_2157628 := by decide
  rcases family_descends (prefixWord ++ tailWord_2157628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2157645 : List Nat := [1, 6, 1, 1, 1, 3, 3, 1, 5]
def baseStart_2157645 : Nat := 118140960795 + 2157645 * 2 ^ 59
def prefixEnd_2157645 : Nat := 4983230072969 + 3 ^ 40 * 2157645 * 2
def baseEnd_2157645 : Nat := 246201992615625763936595

theorem tailTrace_2157645 : CollatzResearch.WordTrace tailWord_2157645 prefixEnd_2157645 246201992615625763936595 := by
  unfold tailWord_2157645
  simp only [CollatzResearch.WordTrace]
  refine ⟨78695778268228136273610389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52463852178818757515740259 78695778268228136273610389)
  ·
    refine ⟨3688864606323193887825487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 78695778268228136273610389 3688864606323193887825487)
    ·
      refine ⟨5533296909484790831738231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3688864606323193887825487 5533296909484790831738231)
      ·
        refine ⟨8299945364227186247607347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5533296909484790831738231 8299945364227186247607347)
        ·
          refine ⟨12449918046340779371411021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8299945364227186247607347 12449918046340779371411021)
          ·
            refine ⟨4668719267377792264279133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12449918046340779371411021 4668719267377792264279133)
            ·
              refine ⟨1750769725266672099104675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4668719267377792264279133 1750769725266672099104675)
              ·
                refine ⟨2626154587900008148657013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1750769725266672099104675 2626154587900008148657013)
                ·
                  refine ⟨246201992615625763936595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2626154587900008148657013 246201992615625763936595)
                  ·
                    rfl

theorem cell22_2157645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 3, 1, 5].length) (baseStart_2157645 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2157645 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2157645 prefixEnd_2157645 := by exact prefixLift 2157645
  have htrace : WordTrace (prefixWord ++ tailWord_2157645) baseStart_2157645 baseEnd_2157645 := by
    simpa [prefixWord, tailWord_2157645, baseEnd_2157645] using wordTrace_append hprefix tailTrace_2157645
  have hstable : (prefixWord ++ tailWord_2157645).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2157645).length < 2 ^ (prefixWord ++ tailWord_2157645).sum := by decide
  have hdescent : baseEnd_2157645 < baseStart_2157645 := by decide
  rcases family_descends (prefixWord ++ tailWord_2157645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2157673 : List Nat := [1, 2, 1, 1, 1, 6, 3, 3, 4]
def baseStart_2157673 : Nat := 118140960795 + 2157673 * 2 ^ 59
def prefixEnd_2157673 : Nat := 4983230072969 + 3 ^ 40 * 2157673 * 2
def baseEnd_2157673 : Nat := 246205187606364850703233

theorem tailTrace_2157673 : CollatzResearch.WordTrace tailWord_2157673 prefixEnd_2157673 246205187606364850703233 := by
  unfold tailWord_2157673
  simp only [CollatzResearch.WordTrace]
  refine ⟨78696799512126697055629673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52464533008084464703753115 78696799512126697055629673)
  ·
    refine ⟨59022599634095022791722255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78696799512126697055629673 59022599634095022791722255)
    ·
      refine ⟨88533899451142534187583383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59022599634095022791722255 88533899451142534187583383)
      ·
        refine ⟨132800849176713801281375075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88533899451142534187583383 132800849176713801281375075)
        ·
          refine ⟨199201273765070701922062613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 132800849176713801281375075 199201273765070701922062613)
          ·
            refine ⟨9337559707737689152596685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 199201273765070701922062613 9337559707737689152596685)
            ·
              refine ⟨3501584890401633432223757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9337559707737689152596685 3501584890401633432223757)
              ·
                refine ⟨1313094333900612537083909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3501584890401633432223757 1313094333900612537083909)
                ·
                  refine ⟨246205187606364850703233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1313094333900612537083909 246205187606364850703233)
                  ·
                    rfl

theorem cell22_2157673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 3, 3, 4].length) (baseStart_2157673 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2157673 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2157673 prefixEnd_2157673 := by exact prefixLift 2157673
  have htrace : WordTrace (prefixWord ++ tailWord_2157673) baseStart_2157673 baseEnd_2157673 := by
    simpa [prefixWord, tailWord_2157673, baseEnd_2157673] using wordTrace_append hprefix tailTrace_2157673
  have hstable : (prefixWord ++ tailWord_2157673).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2157673).length < 2 ^ (prefixWord ++ tailWord_2157673).sum := by decide
  have hdescent : baseEnd_2157673 < baseStart_2157673 := by decide
  rcases family_descends (prefixWord ++ tailWord_2157673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2157705 : List Nat := [1, 2, 1, 1, 4, 3, 4, 1, 2, 3]
def baseStart_2157705 : Nat := 118140960795 + 2157705 * 2 ^ 59
def prefixEnd_2157705 : Nat := 4983230072969 + 3 ^ 40 * 2157705 * 2
def baseEnd_2157705 : Nat := 738626517073057135309601

theorem tailTrace_2157705 : CollatzResearch.WordTrace tailWord_2157705 prefixEnd_2157705 738626517073057135309601 := by
  unfold tailWord_2157705
  simp only [CollatzResearch.WordTrace]
  refine ⟨78697966648010766520794569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52465311098673844347196379 78697966648010766520794569)
  ·
    refine ⟨59023474986008074890595927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78697966648010766520794569 59023474986008074890595927)
    ·
      refine ⟨88535212479012112335893891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59023474986008074890595927 88535212479012112335893891)
      ·
        refine ⟨132802818718518168503840837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88535212479012112335893891 132802818718518168503840837)
        ·
          refine ⟨24900528509722156594470157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 132802818718518168503840837 24900528509722156594470157)
          ·
            refine ⟨9337698191145808722926309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24900528509722156594470157 9337698191145808722926309)
            ·
              refine ⟨1750818410839839135548683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9337698191145808722926309 1750818410839839135548683)
              ·
                refine ⟨2626227616259758703323025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1750818410839839135548683 2626227616259758703323025)
                ·
                  refine ⟨1969670712194819027492269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2626227616259758703323025 1969670712194819027492269)
                  ·
                    refine ⟨738626517073057135309601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1969670712194819027492269 738626517073057135309601)
                    ·
                      rfl

theorem cell22_2157705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 4, 1, 2, 3].length) (baseStart_2157705 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2157705 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2157705 prefixEnd_2157705 := by exact prefixLift 2157705
  have htrace : WordTrace (prefixWord ++ tailWord_2157705) baseStart_2157705 baseEnd_2157705 := by
    simpa [prefixWord, tailWord_2157705, baseEnd_2157705] using wordTrace_append hprefix tailTrace_2157705
  have hstable : (prefixWord ++ tailWord_2157705).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2157705).length < 2 ^ (prefixWord ++ tailWord_2157705).sum := by decide
  have hdescent : baseEnd_2157705 < baseStart_2157705 := by decide
  rcases family_descends (prefixWord ++ tailWord_2157705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2157797 : List Nat := [1, 3, 1, 4, 4, 1, 1, 2, 5]
def baseStart_2157797 : Nat := 118140960795 + 2157797 * 2 ^ 59
def prefixEnd_2157797 : Nat := 4983230072969 + 3 ^ 40 * 2157797 * 2
def baseEnd_2157797 : Nat := 246219336851066520669773

theorem tailTrace_2157797 : CollatzResearch.WordTrace tailWord_2157797 prefixEnd_2157797 246219336851066520669773 := by
  unfold tailWord_2157797
  simp only [CollatzResearch.WordTrace]
  refine ⟨78701322163677466233143645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52467548109118310822095763 78701322163677466233143645)
  ·
    refine ⟨29512995811379049837428867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 78701322163677466233143645 29512995811379049837428867)
    ·
      refine ⟨44269493717068574756143301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29512995811379049837428867 44269493717068574756143301)
      ·
        refine ⟨8300530071950357766776869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 44269493717068574756143301 8300530071950357766776869)
        ·
          refine ⟨1556349388490692081270663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8300530071950357766776869 1556349388490692081270663)
          ·
            refine ⟨2334524082736038121905995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1556349388490692081270663 2334524082736038121905995)
            ·
              refine ⟨3501786124104057182858993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2334524082736038121905995 3501786124104057182858993)
              ·
                refine ⟨2626339593078042887144245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3501786124104057182858993 2626339593078042887144245)
                ·
                  refine ⟨246219336851066520669773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2626339593078042887144245 246219336851066520669773)
                  ·
                    rfl

theorem cell22_2157797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 4, 1, 1, 2, 5].length) (baseStart_2157797 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2157797 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2157797 prefixEnd_2157797 := by exact prefixLift 2157797
  have htrace : WordTrace (prefixWord ++ tailWord_2157797) baseStart_2157797 baseEnd_2157797 := by
    simpa [prefixWord, tailWord_2157797, baseEnd_2157797] using wordTrace_append hprefix tailTrace_2157797
  have hstable : (prefixWord ++ tailWord_2157797).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2157797).length < 2 ^ (prefixWord ++ tailWord_2157797).sum := by decide
  have hdescent : baseEnd_2157797 < baseStart_2157797 := by decide
  rcases family_descends (prefixWord ++ tailWord_2157797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2157823 : List Nat := [1, 1, 2, 2, 1, 5, 3, 1, 1, 5]
def baseStart_2157823 : Nat := 118140960795 + 2157823 * 2 ^ 59
def prefixEnd_2157823 : Nat := 4983230072969 + 3 ^ 40 * 2157823 * 2
def baseEnd_2157823 : Nat := 738666910884544160859239

theorem tailTrace_2157823 : CollatzResearch.WordTrace tailWord_2157823 prefixEnd_2157823 738666910884544160859239 := by
  unfold tailWord_2157823
  simp only [CollatzResearch.WordTrace]
  refine ⟨78702270461583272673590123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52468180307722181782393415 78702270461583272673590123)
  ·
    refine ⟨118053405692374909010385185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78702270461583272673590123 118053405692374909010385185)
    ·
      refine ⟨88540054269281181757788889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 118053405692374909010385185 88540054269281181757788889)
      ·
        refine ⟨66405040701960886318341667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 88540054269281181757788889 66405040701960886318341667)
        ·
          refine ⟨99607561052941329477512501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66405040701960886318341667 99607561052941329477512501)
          ·
            refine ⟨9338208848713249638516797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 99607561052941329477512501 9338208848713249638516797)
            ·
              refine ⟨3501828318267468614443799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9338208848713249638516797 3501828318267468614443799)
              ·
                refine ⟨5252742477401202921665699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3501828318267468614443799 5252742477401202921665699)
                ·
                  refine ⟨7879113716101804382498549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5252742477401202921665699 7879113716101804382498549)
                  ·
                    refine ⟨738666910884544160859239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7879113716101804382498549 738666910884544160859239)
                    ·
                      rfl

theorem cell22_2157823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 3, 1, 1, 5].length) (baseStart_2157823 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2157823 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2157823 prefixEnd_2157823 := by exact prefixLift 2157823
  have htrace : WordTrace (prefixWord ++ tailWord_2157823) baseStart_2157823 baseEnd_2157823 := by
    simpa [prefixWord, tailWord_2157823, baseEnd_2157823] using wordTrace_append hprefix tailTrace_2157823
  have hstable : (prefixWord ++ tailWord_2157823).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2157823).length < 2 ^ (prefixWord ++ tailWord_2157823).sum := by decide
  have hdescent : baseEnd_2157823 < baseStart_2157823 := by decide
  rcases family_descends (prefixWord ++ tailWord_2157823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2157838 : List Nat := [4, 1, 1, 2, 1, 3, 2, 1, 1, 6]
def baseStart_2157838 : Nat := 118140960795 + 2157838 * 2 ^ 59
def prefixEnd_2157838 : Nat := 4983230072969 + 3 ^ 40 * 2157838 * 2
def baseEnd_2157838 : Nat := 738672045691089121734193

theorem tailTrace_2157838 : CollatzResearch.WordTrace tailWord_2157838 prefixEnd_2157838 738672045691089121734193 := by
  unfold tailWord_2157838
  simp only [CollatzResearch.WordTrace]
  refine ⟨9837852194566116279423271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 52468545037685953490257445 9837852194566116279423271)
  ·
    refine ⟨14756778291849174419134907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9837852194566116279423271 14756778291849174419134907)
    ·
      refine ⟨22135167437773761628702361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14756778291849174419134907 22135167437773761628702361)
      ·
        refine ⟨16601375578330321221526771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22135167437773761628702361 16601375578330321221526771)
        ·
          refine ⟨24902063367495481832290157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16601375578330321221526771 24902063367495481832290157)
          ·
            refine ⟨9338273762810805687108809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24902063367495481832290157 9338273762810805687108809)
            ·
              refine ⟨7003705322108104265331607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9338273762810805687108809 7003705322108104265331607)
              ·
                refine ⟨10505557983162156397997411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7003705322108104265331607 10505557983162156397997411)
                ·
                  refine ⟨15758336974743234596996117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10505557983162156397997411 15758336974743234596996117)
                  ·
                    refine ⟨738672045691089121734193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15758336974743234596996117 738672045691089121734193)
                    ·
                      rfl

theorem cell22_2157838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 2, 1, 1, 6].length) (baseStart_2157838 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2157838 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2157838 prefixEnd_2157838 := by exact prefixLift 2157838
  have htrace : WordTrace (prefixWord ++ tailWord_2157838) baseStart_2157838 baseEnd_2157838 := by
    simpa [prefixWord, tailWord_2157838, baseEnd_2157838] using wordTrace_append hprefix tailTrace_2157838
  have hstable : (prefixWord ++ tailWord_2157838).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2157838).length < 2 ^ (prefixWord ++ tailWord_2157838).sum := by decide
  have hdescent : baseEnd_2157838 < baseStart_2157838 := by decide
  rcases family_descends (prefixWord ++ tailWord_2157838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2157853 : List Nat := [1, 4, 2, 3, 1, 1, 10]
def baseStart_2157853 : Nat := 118140960795 + 2157853 * 2 ^ 59
def prefixEnd_2157853 : Nat := 4983230072969 + 3 ^ 40 * 2157853 * 2
def baseEnd_2157853 : Nat := 27358414092504966022561

theorem tailTrace_2157853 : CollatzResearch.WordTrace tailWord_2157853 prefixEnd_2157853 27358414092504966022561 := by
  unfold tailWord_2157853
  simp only [CollatzResearch.WordTrace]
  refine ⟨78703364651474587797182213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52468909767649725198121475 78703364651474587797182213)
  ·
    refine ⟨14756880872151485211971665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 78703364651474587797182213 14756880872151485211971665)
    ·
      refine ⟨11067660654113613908978749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14756880872151485211971665 11067660654113613908978749)
      ·
        refine ⟨4150372745292605215867031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11067660654113613908978749 4150372745292605215867031)
        ·
          refine ⟨6225559117938907823800547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4150372745292605215867031 6225559117938907823800547)
          ·
            refine ⟨9338338676908361735700821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6225559117938907823800547 9338338676908361735700821)
            ·
              refine ⟨27358414092504966022561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 9338338676908361735700821 27358414092504966022561)
              ·
                rfl

theorem cell22_2157853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 10].length) (baseStart_2157853 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2157853 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2157853 prefixEnd_2157853 := by exact prefixLift 2157853
  have htrace : WordTrace (prefixWord ++ tailWord_2157853) baseStart_2157853 baseEnd_2157853 := by
    simpa [prefixWord, tailWord_2157853, baseEnd_2157853] using wordTrace_append hprefix tailTrace_2157853
  have hstable : (prefixWord ++ tailWord_2157853).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2157853).length < 2 ^ (prefixWord ++ tailWord_2157853).sum := by decide
  have hdescent : baseEnd_2157853 < baseStart_2157853 := by decide
  rcases family_descends (prefixWord ++ tailWord_2157853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2157855 : List Nat := [1, 1, 2, 4, 4, 1, 1, 2, 2, 4]
def baseStart_2157855 : Nat := 118140960795 + 2157855 * 2 ^ 59
def prefixEnd_2157855 : Nat := 4983230072969 + 3 ^ 40 * 2157855 * 2
def baseEnd_2157855 : Nat := 738677865138506744059141

theorem tailTrace_2157855 : CollatzResearch.WordTrace tailWord_2157855 prefixEnd_2157855 738677865138506744059141 := by
  unfold tailWord_2157855
  simp only [CollatzResearch.WordTrace]
  refine ⟨78703437597467342138755019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52468958398311561425836679 78703437597467342138755019)
  ·
    refine ⟨118055156396201013208132529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78703437597467342138755019 118055156396201013208132529)
    ·
      refine ⟨88541367297150759906099397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 118055156396201013208132529 88541367297150759906099397)
      ·
        refine ⟨16601506368215767482393637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 88541367297150759906099397 16601506368215767482393637)
        ·
          refine ⟨3112782444040456402948807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16601506368215767482393637 3112782444040456402948807)
          ·
            refine ⟨4669173666060684604423211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3112782444040456402948807 4669173666060684604423211)
            ·
              refine ⟨7003760499091026906634817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4669173666060684604423211 7003760499091026906634817)
              ·
                refine ⟨5252820374318270179976113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7003760499091026906634817 5252820374318270179976113)
                ·
                  refine ⟨3939615280738702634982085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5252820374318270179976113 3939615280738702634982085)
                  ·
                    refine ⟨738677865138506744059141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3939615280738702634982085 738677865138506744059141)
                    ·
                      rfl

theorem cell22_2157855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 1, 2, 2, 4].length) (baseStart_2157855 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2157855 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2157855 prefixEnd_2157855 := by exact prefixLift 2157855
  have htrace : WordTrace (prefixWord ++ tailWord_2157855) baseStart_2157855 baseEnd_2157855 := by
    simpa [prefixWord, tailWord_2157855, baseEnd_2157855] using wordTrace_append hprefix tailTrace_2157855
  have hstable : (prefixWord ++ tailWord_2157855).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2157855).length < 2 ^ (prefixWord ++ tailWord_2157855).sum := by decide
  have hdescent : baseEnd_2157855 < baseStart_2157855 := by decide
  rcases family_descends (prefixWord ++ tailWord_2157855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2157874 : List Nat := [3, 2, 1, 1, 4, 3, 2, 1, 2, 3]
def baseStart_2157874 : Nat := 118140960795 + 2157874 * 2 ^ 59
def prefixEnd_2157874 : Nat := 4983230072969 + 3 ^ 40 * 2157874 * 2
def baseEnd_2157874 : Nat := 738684369226797027834083

theorem tailTrace_2157874 : CollatzResearch.WordTrace tailWord_2157874 prefixEnd_2157874 738684369226797027834083 := by
  unfold tailWord_2157874
  simp only [CollatzResearch.WordTrace]
  refine ⟨19676032646099627095924169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52469420389599005589131117 19676032646099627095924169)
  ·
    refine ⟨14757024484574720321943127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19676032646099627095924169 14757024484574720321943127)
    ·
      refine ⟨22135536726862080482914691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14757024484574720321943127 22135536726862080482914691)
      ·
        refine ⟨33203305090293120724372037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22135536726862080482914691 33203305090293120724372037)
        ·
          refine ⟨6225619704429960135819757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 33203305090293120724372037 6225619704429960135819757)
          ·
            refine ⟨2334607389161235050932409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6225619704429960135819757 2334607389161235050932409)
            ·
              refine ⟨1750955541870926288199307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2334607389161235050932409 1750955541870926288199307)
              ·
                refine ⟨2626433312806389432298961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1750955541870926288199307 2626433312806389432298961)
                ·
                  refine ⟨1969824984604792074224221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2626433312806389432298961 1969824984604792074224221)
                  ·
                    refine ⟨738684369226797027834083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1969824984604792074224221 738684369226797027834083)
                    ·
                      rfl

theorem cell22_2157874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 3, 2, 1, 2, 3].length) (baseStart_2157874 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2157874 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2157874 prefixEnd_2157874 := by exact prefixLift 2157874
  have htrace : WordTrace (prefixWord ++ tailWord_2157874) baseStart_2157874 baseEnd_2157874 := by
    simpa [prefixWord, tailWord_2157874, baseEnd_2157874] using wordTrace_append hprefix tailTrace_2157874
  have hstable : (prefixWord ++ tailWord_2157874).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2157874).length < 2 ^ (prefixWord ++ tailWord_2157874).sum := by decide
  have hdescent : baseEnd_2157874 < baseStart_2157874 := by decide
  rcases family_descends (prefixWord ++ tailWord_2157874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2157902 : List Nat := [4, 1, 1, 1, 1, 1, 4, 5, 1, 3]
def baseStart_2157902 : Nat := 118140960795 + 2157902 * 2 ^ 59
def prefixEnd_2157902 : Nat := 4983230072969 + 3 ^ 40 * 2157902 * 2
def baseEnd_2157902 : Nat := 738693954199014288133997

theorem tailTrace_2157902 : CollatzResearch.WordTrace tailWord_2157902 prefixEnd_2157902 738693954199014288133997 := by
  unfold tailWord_2157902
  simp only [CollatzResearch.WordTrace]
  refine ⟨9838143978537133645714495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 52470101218864712777143973 9838143978537133645714495)
  ·
    refine ⟨14757215967805700468571743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9838143978537133645714495 14757215967805700468571743)
    ·
      refine ⟨22135823951708550702857615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14757215967805700468571743 22135823951708550702857615)
      ·
        refine ⟨33203735927562826054286423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22135823951708550702857615 33203735927562826054286423)
        ·
          refine ⟨49805603891344239081429635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33203735927562826054286423 49805603891344239081429635)
          ·
            refine ⟨74708405837016358622144453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49805603891344239081429635 74708405837016358622144453)
            ·
              refine ⟨14007826094440567241652085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 74708405837016358622144453 14007826094440567241652085)
              ·
                refine ⟨1313233696353803178904883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 14007826094440567241652085 1313233696353803178904883)
                ·
                  refine ⟨1969850544530704768357325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1313233696353803178904883 1969850544530704768357325)
                  ·
                    refine ⟨738693954199014288133997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1969850544530704768357325 738693954199014288133997)
                    ·
                      rfl

theorem cell22_2157902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 4, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 4, 5, 1, 3].length) (baseStart_2157902 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2157902 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2157902 prefixEnd_2157902 := by exact prefixLift 2157902
  have htrace : WordTrace (prefixWord ++ tailWord_2157902) baseStart_2157902 baseEnd_2157902 := by
    simpa [prefixWord, tailWord_2157902, baseEnd_2157902] using wordTrace_append hprefix tailTrace_2157902
  have hstable : (prefixWord ++ tailWord_2157902).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2157902).length < 2 ^ (prefixWord ++ tailWord_2157902).sum := by decide
  have hdescent : baseEnd_2157902 < baseStart_2157902 := by decide
  rcases family_descends (prefixWord ++ tailWord_2157902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2157910 : List Nat := [5, 2, 3, 1, 1, 2, 2, 2, 4]
def baseStart_2157910 : Nat := 118140960795 + 2157910 * 2 ^ 59
def prefixEnd_2157910 : Nat := 4983230072969 + 3 ^ 40 * 2157910 * 2
def baseEnd_2157910 : Nat := 246232230920834977977991

theorem tailTrace_2157910 : CollatzResearch.WordTrace tailWord_2157910 prefixEnd_2157910 246232230920834977977991 := by
  unfold tailWord_2157910
  simp only [CollatzResearch.WordTrace]
  refine ⟨4919090225766755408250449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 52470295741512057688004789 4919090225766755408250449)
  ·
    refine ⟨3689317669325066556187837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4919090225766755408250449 3689317669325066556187837)
    ·
      refine ⟨1383494125996899958570439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3689317669325066556187837 1383494125996899958570439)
      ·
        refine ⟨2075241188995349937855659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1383494125996899958570439 2075241188995349937855659)
        ·
          refine ⟨3112861783493024906783489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2075241188995349937855659 3112861783493024906783489)
          ·
            refine ⟨2334646337619768680087617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3112861783493024906783489 2334646337619768680087617)
            ·
              refine ⟨1750984753214826510065713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2334646337619768680087617 1750984753214826510065713)
              ·
                refine ⟨1313238564911119882549285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1750984753214826510065713 1313238564911119882549285)
                ·
                  refine ⟨246232230920834977977991, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1313238564911119882549285 246232230920834977977991)
                  ·
                    rfl

theorem cell22_2157910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 2, 2, 2, 4].length) (baseStart_2157910 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2157910 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2157910 prefixEnd_2157910 := by exact prefixLift 2157910
  have htrace : WordTrace (prefixWord ++ tailWord_2157910) baseStart_2157910 baseEnd_2157910 := by
    simpa [prefixWord, tailWord_2157910, baseEnd_2157910] using wordTrace_append hprefix tailTrace_2157910
  have hstable : (prefixWord ++ tailWord_2157910).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2157910).length < 2 ^ (prefixWord ++ tailWord_2157910).sum := by decide
  have hdescent : baseEnd_2157910 < baseStart_2157910 := by decide
  rcases family_descends (prefixWord ++ tailWord_2157910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2157943 : List Nat := [1, 1, 3, 1, 1, 2, 5, 2, 6]
def baseStart_2157943 : Nat := 118140960795 + 2157943 * 2 ^ 59
def prefixEnd_2157943 : Nat := 4983230072969 + 3 ^ 40 * 2157943 * 2
def baseEnd_2157943 : Nat := 246235996445634615952957

theorem tailTrace_2157943 : CollatzResearch.WordTrace tailWord_2157943 prefixEnd_2157943 246235996445634615952957 := by
  unfold tailWord_2157943
  simp only [CollatzResearch.WordTrace]
  refine ⟨78706647221148533167958483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52471098147432355445305655 78706647221148533167958483)
  ·
    refine ⟨118059970831722799751937725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78706647221148533167958483 118059970831722799751937725)
    ·
      refine ⟨44272489061896049906976647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 118059970831722799751937725 44272489061896049906976647)
      ·
        refine ⟨66408733592844074860464971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44272489061896049906976647 66408733592844074860464971)
        ·
          refine ⟨99613100389266112290697457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66408733592844074860464971 99613100389266112290697457)
          ·
            refine ⟨74709825291949584218023093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 99613100389266112290697457 74709825291949584218023093)
            ·
              refine ⟨7004046121120273520439665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 74709825291949584218023093 7004046121120273520439665)
              ·
                refine ⟨5253034590840205140329749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7004046121120273520439665 5253034590840205140329749)
                ·
                  refine ⟨246235996445634615952957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5253034590840205140329749 246235996445634615952957)
                  ·
                    rfl

theorem cell22_2157943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 5, 2, 6].length) (baseStart_2157943 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2157943 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2157943 prefixEnd_2157943 := by exact prefixLift 2157943
  have htrace : WordTrace (prefixWord ++ tailWord_2157943) baseStart_2157943 baseEnd_2157943 := by
    simpa [prefixWord, tailWord_2157943, baseEnd_2157943] using wordTrace_append hprefix tailTrace_2157943
  have hstable : (prefixWord ++ tailWord_2157943).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2157943).length < 2 ^ (prefixWord ++ tailWord_2157943).sum := by decide
  have hdescent : baseEnd_2157943 < baseStart_2157943 := by decide
  rcases family_descends (prefixWord ++ tailWord_2157943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2157988 : List Nat := [2, 3, 1, 2, 1, 1, 1, 11]
def baseStart_2157988 : Nat := 118140960795 + 2157988 * 2 ^ 59
def prefixEnd_2157988 : Nat := 4983230072969 + 3 ^ 40 * 2157988 * 2
def baseEnd_2157988 : Nat := 82080377084059858942637

theorem tailTrace_2157988 : CollatzResearch.WordTrace tailWord_2157988 prefixEnd_2157988 82080377084059858942637 := by
  unfold tailWord_2157988
  simp only [CollatzResearch.WordTrace]
  refine ⟨39354144252992752926673309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52472192337323670568897745 39354144252992752926673309)
  ·
    refine ⟨14757804094872282347502491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39354144252992752926673309 14757804094872282347502491)
    ·
      refine ⟨22136706142308423521253737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14757804094872282347502491 22136706142308423521253737)
      ·
        refine ⟨16602529606731317640940303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22136706142308423521253737 16602529606731317640940303)
        ·
          refine ⟨24903794410096976461410455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16602529606731317640940303 24903794410096976461410455)
          ·
            refine ⟨37355691615145464692115683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24903794410096976461410455 37355691615145464692115683)
            ·
              refine ⟨56033537422718197038173525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37355691615145464692115683 56033537422718197038173525)
              ·
                refine ⟨82080377084059858942637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 56033537422718197038173525 82080377084059858942637)
                ·
                  rfl

theorem cell22_2157988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 11].length) (baseStart_2157988 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2157988 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2157988 prefixEnd_2157988 := by exact prefixLift 2157988
  have htrace : WordTrace (prefixWord ++ tailWord_2157988) baseStart_2157988 baseEnd_2157988 := by
    simpa [prefixWord, tailWord_2157988, baseEnd_2157988] using wordTrace_append hprefix tailTrace_2157988
  have hstable : (prefixWord ++ tailWord_2157988).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2157988).length < 2 ^ (prefixWord ++ tailWord_2157988).sum := by decide
  have hdescent : baseEnd_2157988 < baseStart_2157988 := by decide
  rcases family_descends (prefixWord ++ tailWord_2157988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2158005 : List Nat := [1, 3, 3, 2, 2, 2, 1, 8]
def baseStart_2158005 : Nat := 118140960795 + 2158005 * 2 ^ 59
def prefixEnd_2158005 : Nat := 4983230072969 + 3 ^ 40 * 2158005 * 2
def baseEnd_2158005 : Nat := 82081023689328483645409

theorem tailTrace_2158005 : CollatzResearch.WordTrace tailWord_2158005 prefixEnd_2158005 82081023689328483645409 := by
  unfold tailWord_2158005
  simp only [CollatzResearch.WordTrace]
  refine ⟨78708908546923917756715469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52472605697949278504476979 78708908546923917756715469)
  ·
    refine ⟨29515840705096469158768301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 78708908546923917756715469 29515840705096469158768301)
    ·
      refine ⟨11068440264411175934538113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29515840705096469158768301 11068440264411175934538113)
      ·
        refine ⟨8301330198308381950903585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11068440264411175934538113 8301330198308381950903585)
        ·
          refine ⟨6225997648731286463177689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8301330198308381950903585 6225997648731286463177689)
          ·
            refine ⟨4669498236548464847383267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6225997648731286463177689 4669498236548464847383267)
            ·
              refine ⟨7004247354822697271074901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4669498236548464847383267 7004247354822697271074901)
              ·
                refine ⟨82081023689328483645409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7004247354822697271074901 82081023689328483645409)
                ·
                  rfl

theorem cell22_2158005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 1, 8].length) (baseStart_2158005 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2158005 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2158005 prefixEnd_2158005 := by exact prefixLift 2158005
  have htrace : WordTrace (prefixWord ++ tailWord_2158005) baseStart_2158005 baseEnd_2158005 := by
    simpa [prefixWord, tailWord_2158005, baseEnd_2158005] using wordTrace_append hprefix tailTrace_2158005
  have hstable : (prefixWord ++ tailWord_2158005).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2158005).length < 2 ^ (prefixWord ++ tailWord_2158005).sum := by decide
  have hdescent : baseEnd_2158005 < baseStart_2158005 := by decide
  rcases family_descends (prefixWord ++ tailWord_2158005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2158084 : List Nat := [2, 3, 2, 3, 2, 1, 2, 2, 5]
def baseStart_2158084 : Nat := 118140960795 + 2158084 * 2 ^ 59
def prefixEnd_2158084 : Nat := 4983230072969 + 3 ^ 40 * 2158084 * 2
def baseEnd_2158084 : Nat := 246252085506142160027813

theorem tailTrace_2158084 : CollatzResearch.WordTrace tailWord_2158084 prefixEnd_2158084 246252085506142160027813 := by
  unfold tailWord_2158084
  simp only [CollatzResearch.WordTrace]
  refine ⟨39355894956818857124420653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52474526609091809499227537 39355894956818857124420653)
  ·
    refine ⟨14758460608807071421657745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39355894956818857124420653 14758460608807071421657745)
    ·
      refine ⟨11068845456605303566243309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14758460608807071421657745 11068845456605303566243309)
      ·
        refine ⟨4150817046226988837341241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11068845456605303566243309 4150817046226988837341241)
        ·
          refine ⟨3113112784670241628005931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4150817046226988837341241 3113112784670241628005931)
          ·
            refine ⟨4669669177005362442008897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3113112784670241628005931 4669669177005362442008897)
            ·
              refine ⟨3502251882754021831506673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4669669177005362442008897 3502251882754021831506673)
              ·
                refine ⟨2626688912065516373630005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3502251882754021831506673 2626688912065516373630005)
                ·
                  refine ⟨246252085506142160027813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2626688912065516373630005 246252085506142160027813)
                  ·
                    rfl

theorem cell22_2158084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 2, 2, 5].length) (baseStart_2158084 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2158084 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2158084 prefixEnd_2158084 := by exact prefixLift 2158084
  have htrace : WordTrace (prefixWord ++ tailWord_2158084) baseStart_2158084 baseEnd_2158084 := by
    simpa [prefixWord, tailWord_2158084, baseEnd_2158084] using wordTrace_append hprefix tailTrace_2158084
  have hstable : (prefixWord ++ tailWord_2158084).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2158084).length < 2 ^ (prefixWord ++ tailWord_2158084).sum := by decide
  have hdescent : baseEnd_2158084 < baseStart_2158084 := by decide
  rcases family_descends (prefixWord ++ tailWord_2158084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2158112 : List Nat := [2, 1, 1, 6, 1, 2, 1, 2, 6]
def baseStart_2158112 : Nat := 118140960795 + 2158112 * 2 ^ 59
def prefixEnd_2158112 : Nat := 4983230072969 + 3 ^ 40 * 2158112 * 2
def baseEnd_2158112 : Nat := 246255280496881246794451

theorem tailTrace_2158112 : CollatzResearch.WordTrace tailWord_2158112 prefixEnd_2158112 246255280496881246794451 := by
  unfold tailWord_2158112
  simp only [CollatzResearch.WordTrace]
  refine ⟨39356405578768137515430295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52475207438357516687240393 39356405578768137515430295)
  ·
    refine ⟨59034608368152206273145443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39356405578768137515430295 59034608368152206273145443)
    ·
      refine ⟨88551912552228309409718165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59034608368152206273145443 88551912552228309409718165)
      ·
        refine ⟨4150870900885702003580539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 88551912552228309409718165 4150870900885702003580539)
        ·
          refine ⟨6226306351328553005370809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4150870900885702003580539 6226306351328553005370809)
          ·
            refine ⟨4669729763496414754028107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6226306351328553005370809 4669729763496414754028107)
            ·
              refine ⟨7004594645244622131042161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4669729763496414754028107 7004594645244622131042161)
              ·
                refine ⟨5253445983933466598281621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7004594645244622131042161 5253445983933466598281621)
                ·
                  refine ⟨246255280496881246794451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5253445983933466598281621 246255280496881246794451)
                  ·
                    rfl

theorem cell22_2158112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 1, 2, 6].length) (baseStart_2158112 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2158112 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2158112 prefixEnd_2158112 := by exact prefixLift 2158112
  have htrace : WordTrace (prefixWord ++ tailWord_2158112) baseStart_2158112 baseEnd_2158112 := by
    simpa [prefixWord, tailWord_2158112, baseEnd_2158112] using wordTrace_append hprefix tailTrace_2158112
  have hstable : (prefixWord ++ tailWord_2158112).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2158112).length < 2 ^ (prefixWord ++ tailWord_2158112).sum := by decide
  have hdescent : baseEnd_2158112 < baseStart_2158112 := by decide
  rcases family_descends (prefixWord ++ tailWord_2158112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2158170 : List Nat := [3, 1, 1, 2, 1, 1, 1, 4, 2, 6]
def baseStart_2158170 : Nat := 118140960795 + 2158170 * 2 ^ 59
def prefixEnd_2158170 : Nat := 4983230072969 + 3 ^ 40 * 2158170 * 2
def baseEnd_2158170 : Nat := 738785696075950922433175

theorem tailTrace_2158170 : CollatzResearch.WordTrace tailWord_2158170 prefixEnd_2158170 738785696075950922433175 := by
  unfold tailWord_2158170
  simp only [CollatzResearch.WordTrace]
  refine ⟨19678731647831537734117991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52476617727550767290981309 19678731647831537734117991)
  ·
    refine ⟨29518097471747306601176987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19678731647831537734117991 29518097471747306601176987)
    ·
      refine ⟨44277146207620959901765481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29518097471747306601176987 44277146207620959901765481)
      ·
        refine ⟨33207859655715719926324111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44277146207620959901765481 33207859655715719926324111)
        ·
          refine ⟨49811789483573579889486167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33207859655715719926324111 49811789483573579889486167)
          ·
            refine ⟨74717684225360369834229251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49811789483573579889486167 74717684225360369834229251)
            ·
              refine ⟨112076526338040554751343877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 74717684225360369834229251 112076526338040554751343877)
              ·
                refine ⟨21014348688382604015876977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 112076526338040554751343877 21014348688382604015876977)
                ·
                  refine ⟨15760761516286953011907733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21014348688382604015876977 15760761516286953011907733)
                  ·
                    refine ⟨738785696075950922433175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15760761516286953011907733 738785696075950922433175)
                    ·
                      rfl

theorem cell22_2158170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 4, 2, 6].length) (baseStart_2158170 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2158170 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2158170 prefixEnd_2158170 := by exact prefixLift 2158170
  have htrace : WordTrace (prefixWord ++ tailWord_2158170) baseStart_2158170 baseEnd_2158170 := by
    simpa [prefixWord, tailWord_2158170, baseEnd_2158170] using wordTrace_append hprefix tailTrace_2158170
  have hstable : (prefixWord ++ tailWord_2158170).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2158170).length < 2 ^ (prefixWord ++ tailWord_2158170).sum := by decide
  have hdescent : baseEnd_2158170 < baseStart_2158170 := by decide
  rcases family_descends (prefixWord ++ tailWord_2158170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2158185 : List Nat := [1, 2, 1, 1, 1, 4, 3, 2, 7]
def baseStart_2158185 : Nat := 118140960795 + 2158185 * 2 ^ 59
def prefixEnd_2158185 : Nat := 4983230072969 + 3 ^ 40 * 2158185 * 2
def baseEnd_2158185 : Nat := 246263610294165294436043

theorem tailTrace_2158185 : CollatzResearch.WordTrace tailWord_2158185 prefixEnd_2158185 246263610294165294436043 := by
  unfold tailWord_2158185
  simp only [CollatzResearch.WordTrace]
  refine ⟨78715473686271808498268009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52476982457514538998845339 78715473686271808498268009)
  ·
    refine ⟨59036605264703856373701007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78715473686271808498268009 59036605264703856373701007)
    ·
      refine ⟨88554907897055784560551511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59036605264703856373701007 88554907897055784560551511)
      ·
        refine ⟨132832361845583676840827267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88554907897055784560551511 132832361845583676840827267)
        ·
          refine ⟨199248542768375515261240901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 132832361845583676840827267 199248542768375515261240901)
          ·
            refine ⟨37359101769070409111482669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 199248542768375515261240901 37359101769070409111482669)
            ·
              refine ⟨14009663163401403416806001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37359101769070409111482669 14009663163401403416806001)
              ·
                refine ⟨10507247372551052562604501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14009663163401403416806001 10507247372551052562604501)
                ·
                  refine ⟨246263610294165294436043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10507247372551052562604501 246263610294165294436043)
                  ·
                    rfl

theorem cell22_2158185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 3, 2, 7].length) (baseStart_2158185 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2158185 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2158185 prefixEnd_2158185 := by exact prefixLift 2158185
  have htrace : WordTrace (prefixWord ++ tailWord_2158185) baseStart_2158185 baseEnd_2158185 := by
    simpa [prefixWord, tailWord_2158185, baseEnd_2158185] using wordTrace_append hprefix tailTrace_2158185
  have hstable : (prefixWord ++ tailWord_2158185).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2158185).length < 2 ^ (prefixWord ++ tailWord_2158185).sum := by decide
  have hdescent : baseEnd_2158185 < baseStart_2158185 := by decide
  rcases family_descends (prefixWord ++ tailWord_2158185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2158279 : List Nat := [1, 1, 4, 1, 1, 1, 3, 5, 2, 3]
def baseStart_2158279 : Nat := 118140960795 + 2158279 * 2 ^ 59
def prefixEnd_2158279 : Nat := 4983230072969 + 3 ^ 40 * 2158279 * 2
def baseEnd_2158279 : Nat := 738823009003510971457841

theorem tailTrace_2158279 : CollatzResearch.WordTrace tailWord_2158279 prefixEnd_2158279 738823009003510971457841 := by
  unfold tailWord_2158279
  simp only [CollatzResearch.WordTrace]
  refine ⟨78718902147931262552189891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52479268098620841701459927 78718902147931262552189891)
  ·
    refine ⟨118078353221896893828284837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78718902147931262552189891 118078353221896893828284837)
    ·
      refine ⟨22139691229105667592803407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 118078353221896893828284837 22139691229105667592803407)
      ·
        refine ⟨33209536843658501389205111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22139691229105667592803407 33209536843658501389205111)
        ·
          refine ⟨49814305265487752083807667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33209536843658501389205111 49814305265487752083807667)
          ·
            refine ⟨74721457898231628125711501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49814305265487752083807667 74721457898231628125711501)
            ·
              refine ⟨28020546711836860547141813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 74721457898231628125711501 28020546711836860547141813)
              ·
                refine ⟨2626926254234705676294545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 28020546711836860547141813 2626926254234705676294545)
                ·
                  refine ⟨1970194690676029257220909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2626926254234705676294545 1970194690676029257220909)
                  ·
                    refine ⟨738823009003510971457841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1970194690676029257220909 738823009003510971457841)
                    ·
                      rfl

theorem cell22_2158279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 5, 2, 3].length) (baseStart_2158279 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2158279 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2158279 prefixEnd_2158279 := by exact prefixLift 2158279
  have htrace : WordTrace (prefixWord ++ tailWord_2158279) baseStart_2158279 baseEnd_2158279 := by
    simpa [prefixWord, tailWord_2158279, baseEnd_2158279] using wordTrace_append hprefix tailTrace_2158279
  have hstable : (prefixWord ++ tailWord_2158279).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2158279).length < 2 ^ (prefixWord ++ tailWord_2158279).sum := by decide
  have hdescent : baseEnd_2158279 < baseStart_2158279 := by decide
  rcases family_descends (prefixWord ++ tailWord_2158279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2158300 : List Nat := [2, 2, 5, 1, 2, 2, 2, 1, 1, 4]
def baseStart_2158300 : Nat := 118140960795 + 2158300 * 2 ^ 59
def prefixEnd_2158300 : Nat := 4983230072969 + 3 ^ 40 * 2158300 * 2
def baseEnd_2158300 : Nat := 738830197732673916682777

theorem tailTrace_2158300 : CollatzResearch.WordTrace tailWord_2158300 prefixEnd_2158300 738830197732673916682777 := by
  unfold tailWord_2158300
  simp only [CollatzResearch.WordTrace]
  refine ⟨39359834040427591569352177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52479778720570122092469569 39359834040427591569352177)
  ·
    refine ⟨29519875530320693677014133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39359834040427591569352177 29519875530320693677014133)
    ·
      refine ⟨2767488330967565032220075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 29519875530320693677014133 2767488330967565032220075)
      ·
        refine ⟨4151232496451347548330113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2767488330967565032220075 4151232496451347548330113)
        ·
          refine ⟨3113424372338510661247585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4151232496451347548330113 3113424372338510661247585)
          ·
            refine ⟨2335068279253882995935689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3113424372338510661247585 2335068279253882995935689)
            ·
              refine ⟨1751301209440412246951767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2335068279253882995935689 1751301209440412246951767)
              ·
                refine ⟨2626951814160618370427651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1751301209440412246951767 2626951814160618370427651)
                ·
                  refine ⟨3940427721240927555641477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2626951814160618370427651 3940427721240927555641477)
                  ·
                    refine ⟨738830197732673916682777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3940427721240927555641477 738830197732673916682777)
                    ·
                      rfl

theorem cell22_2158300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 2, 2, 1, 1, 4].length) (baseStart_2158300 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2158300 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2158300 prefixEnd_2158300 := by exact prefixLift 2158300
  have htrace : WordTrace (prefixWord ++ tailWord_2158300) baseStart_2158300 baseEnd_2158300 := by
    simpa [prefixWord, tailWord_2158300, baseEnd_2158300] using wordTrace_append hprefix tailTrace_2158300
  have hstable : (prefixWord ++ tailWord_2158300).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2158300).length < 2 ^ (prefixWord ++ tailWord_2158300).sum := by decide
  have hdescent : baseEnd_2158300 < baseStart_2158300 := by decide
  rcases family_descends (prefixWord ++ tailWord_2158300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2158343 : List Nat := [1, 1, 4, 4, 3, 1, 2, 6]
def baseStart_2158343 : Nat := 118140960795 + 2158343 * 2 ^ 59
def prefixEnd_2158343 : Nat := 4983230072969 + 3 ^ 40 * 2158343 * 2
def baseEnd_2158343 : Nat := 82093879723492904206405

theorem tailTrace_2158343 : CollatzResearch.WordTrace tailWord_2158343 prefixEnd_2158343 82093879723492904206405 := by
  unfold tailWord_2158343
  simp only [CollatzResearch.WordTrace]
  refine ⟨78721236419699401482519683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52480824279799600988346455 78721236419699401482519683)
  ·
    refine ⟨118081854629549102223779525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78721236419699401482519683 118081854629549102223779525)
    ·
      refine ⟨22140347743040456666958661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 118081854629549102223779525 22140347743040456666958661)
      ·
        refine ⟨4151315201820085625054749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22140347743040456666958661 4151315201820085625054749)
        ·
          refine ⟨1556743200682532109395531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4151315201820085625054749 1556743200682532109395531)
          ·
            refine ⟨2335114801023798164093297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1556743200682532109395531 2335114801023798164093297)
            ·
              refine ⟨1751336100767848623069973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2335114801023798164093297 1751336100767848623069973)
              ·
                refine ⟨82093879723492904206405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1751336100767848623069973 82093879723492904206405)
                ·
                  rfl

theorem cell22_2158343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 3, 1, 2, 6].length) (baseStart_2158343 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2158343 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2158343 prefixEnd_2158343 := by exact prefixLift 2158343
  have htrace : WordTrace (prefixWord ++ tailWord_2158343) baseStart_2158343 baseEnd_2158343 := by
    simpa [prefixWord, tailWord_2158343, baseEnd_2158343] using wordTrace_append hprefix tailTrace_2158343
  have hstable : (prefixWord ++ tailWord_2158343).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2158343).length < 2 ^ (prefixWord ++ tailWord_2158343).sum := by decide
  have hdescent : baseEnd_2158343 < baseStart_2158343 := by decide
  rcases family_descends (prefixWord ++ tailWord_2158343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2158349 : List Nat := [1, 7, 2, 1, 1, 2, 1, 3, 4]
def baseStart_2158349 : Nat := 118140960795 + 2158349 * 2 ^ 59
def prefixEnd_2158349 : Nat := 4983230072969 + 3 ^ 40 * 2158349 * 2
def baseEnd_2158349 : Nat := 246282323811351374069209

theorem tailTrace_2158349 : CollatzResearch.WordTrace tailWord_2158349 prefixEnd_2158349 246282323811351374069209 := by
  unfold tailWord_2158349
  simp only [CollatzResearch.WordTrace]
  refine ⟨78721455257677664507238101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52480970171785109671492067 78721455257677664507238101)
  ·
    refine ⟨1845034107601820261888393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 78721455257677664507238101 1845034107601820261888393)
    ·
      refine ⟨1383775580701365196416295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1845034107601820261888393 1383775580701365196416295)
      ·
        refine ⟨2075663371052047794624443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1383775580701365196416295 2075663371052047794624443)
        ·
          refine ⟨3113495056578071691936665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2075663371052047794624443 3113495056578071691936665)
          ·
            refine ⟨2335121292433553768952499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3113495056578071691936665 2335121292433553768952499)
            ·
              refine ⟨3502681938650330653428749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2335121292433553768952499 3502681938650330653428749)
              ·
                refine ⟨1313505726993873995035781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3502681938650330653428749 1313505726993873995035781)
                ·
                  refine ⟨246282323811351374069209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1313505726993873995035781 246282323811351374069209)
                  ·
                    rfl

theorem cell22_2158349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 2, 1, 3, 4].length) (baseStart_2158349 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2158349 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2158349 prefixEnd_2158349 := by exact prefixLift 2158349
  have htrace : WordTrace (prefixWord ++ tailWord_2158349) baseStart_2158349 baseEnd_2158349 := by
    simpa [prefixWord, tailWord_2158349, baseEnd_2158349] using wordTrace_append hprefix tailTrace_2158349
  have hstable : (prefixWord ++ tailWord_2158349).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2158349).length < 2 ^ (prefixWord ++ tailWord_2158349).sum := by decide
  have hdescent : baseEnd_2158349 < baseStart_2158349 := by decide
  rcases family_descends (prefixWord ++ tailWord_2158349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2158388 : List Nat := [2, 5, 1, 1, 2, 1, 4, 1, 5]
def baseStart_2158388 : Nat := 118140960795 + 2158388 * 2 ^ 59
def prefixEnd_2158388 : Nat := 4983230072969 + 3 ^ 40 * 2158388 * 2
def baseEnd_2158388 : Nat := 246286773977023673494169

theorem tailTrace_2158388 : CollatzResearch.WordTrace tailWord_2158388 prefixEnd_2158388 246286773977023673494169 := by
  unfold tailWord_2158388
  simp only [CollatzResearch.WordTrace]
  refine ⟨39361438852268187083953909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52481918469690916111938545 39361438852268187083953909)
  ·
    refine ⟨3690134892400142539120679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 39361438852268187083953909 3690134892400142539120679)
    ·
      refine ⟨5535202338600213808681019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3690134892400142539120679 5535202338600213808681019)
      ·
        refine ⟨8302803507900320713021529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5535202338600213808681019 8302803507900320713021529)
        ·
          refine ⟨6227102630925240534766147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8302803507900320713021529 6227102630925240534766147)
          ·
            refine ⟨9340653946387860802149221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6227102630925240534766147 9340653946387860802149221)
            ·
              refine ⟨1751372614947723900402979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9340653946387860802149221 1751372614947723900402979)
              ·
                refine ⟨2627058922421585850604469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1751372614947723900402979 2627058922421585850604469)
                ·
                  refine ⟨246286773977023673494169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2627058922421585850604469 246286773977023673494169)
                  ·
                    rfl

theorem cell22_2158388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 4, 1, 5].length) (baseStart_2158388 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2158388 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2158388 prefixEnd_2158388 := by exact prefixLift 2158388
  have htrace : WordTrace (prefixWord ++ tailWord_2158388) baseStart_2158388 baseEnd_2158388 := by
    simpa [prefixWord, tailWord_2158388, baseEnd_2158388] using wordTrace_append hprefix tailTrace_2158388
  have hstable : (prefixWord ++ tailWord_2158388).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2158388).length < 2 ^ (prefixWord ++ tailWord_2158388).sum := by decide
  have hdescent : baseEnd_2158388 < baseStart_2158388 := by decide
  rcases family_descends (prefixWord ++ tailWord_2158388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2158418 : List Nat := [3, 2, 2, 1, 1, 4, 3, 1, 1, 4]
def baseStart_2158418 : Nat := 118140960795 + 2158418 * 2 ^ 59
def prefixEnd_2158418 : Nat := 4983230072969 + 3 ^ 40 * 2158418 * 2
def baseEnd_2158418 : Nat := 738870591544160942232415

theorem tailTrace_2158418 : CollatzResearch.WordTrace tailWord_2158418 prefixEnd_2158418 738870591544160942232415 := by
  unfold tailWord_2158418
  simp only [CollatzResearch.WordTrace]
  refine ⟨19680992973606922322874977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52482647929618459527666605 19680992973606922322874977)
  ·
    refine ⟨14760744730205191742156233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19680992973606922322874977 14760744730205191742156233)
    ·
      refine ⟨11070558547653893806617175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14760744730205191742156233 11070558547653893806617175)
      ·
        refine ⟨16605837821480840709925763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11070558547653893806617175 16605837821480840709925763)
        ·
          refine ⟨24908756732221261064888645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16605837821480840709925763 24908756732221261064888645)
          ·
            refine ⟨4670391887291486449666621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24908756732221261064888645 4670391887291486449666621)
            ·
              refine ⟨1751396957734307418624983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4670391887291486449666621 1751396957734307418624983)
              ·
                refine ⟨2627095436601461127937475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1751396957734307418624983 2627095436601461127937475)
                ·
                  refine ⟨3940643154902191691906213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2627095436601461127937475 3940643154902191691906213)
                  ·
                    refine ⟨738870591544160942232415, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3940643154902191691906213 738870591544160942232415)
                    ·
                      rfl

theorem cell22_2158418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 3, 1, 1, 4].length) (baseStart_2158418 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2158418 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2158418 prefixEnd_2158418 := by exact prefixLift 2158418
  have htrace : WordTrace (prefixWord ++ tailWord_2158418) baseStart_2158418 baseEnd_2158418 := by
    simpa [prefixWord, tailWord_2158418, baseEnd_2158418] using wordTrace_append hprefix tailTrace_2158418
  have hstable : (prefixWord ++ tailWord_2158418).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2158418).length < 2 ^ (prefixWord ++ tailWord_2158418).sum := by decide
  have hdescent : baseEnd_2158418 < baseStart_2158418 := by decide
  rcases family_descends (prefixWord ++ tailWord_2158418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2158431 : List Nat := [1, 1, 2, 3, 1, 4, 1, 4, 2, 3]
def baseStart_2158431 : Nat := 118140960795 + 2158431 * 2 ^ 59
def prefixEnd_2158431 : Nat := 4983230072969 + 3 ^ 40 * 2158431 * 2
def baseEnd_2158431 : Nat := 738875041709833241657375

theorem tailTrace_2158431 : CollatzResearch.WordTrace tailWord_2158431 prefixEnd_2158431 738875041709833241657375 := by
  unfold tailWord_2158431
  simp only [CollatzResearch.WordTrace]
  refine ⟨78724446043380592511723147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52482964028920395007815431 78724446043380592511723147)
  ·
    refine ⟨118086669065070888767584721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78724446043380592511723147 118086669065070888767584721)
    ·
      refine ⟨88565001798803166575688541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 118086669065070888767584721 88565001798803166575688541)
      ·
        refine ⟨33211875674551187465883203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 88565001798803166575688541 33211875674551187465883203)
        ·
          refine ⟨49817813511826781198824805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33211875674551187465883203 49817813511826781198824805)
          ·
            refine ⟨9340840033467521474779651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 49817813511826781198824805 9340840033467521474779651)
            ·
              refine ⟨14011260050201282212169477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9340840033467521474779651 14011260050201282212169477)
              ·
                refine ⟨2627111259412740414781777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14011260050201282212169477 2627111259412740414781777)
                ·
                  refine ⟨1970333444559555311086333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2627111259412740414781777 1970333444559555311086333)
                  ·
                    refine ⟨738875041709833241657375, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1970333444559555311086333 738875041709833241657375)
                    ·
                      rfl

theorem cell22_2158431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 1, 4, 2, 3].length) (baseStart_2158431 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2158431 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2158431 prefixEnd_2158431 := by exact prefixLift 2158431
  have htrace : WordTrace (prefixWord ++ tailWord_2158431) baseStart_2158431 baseEnd_2158431 := by
    simpa [prefixWord, tailWord_2158431, baseEnd_2158431] using wordTrace_append hprefix tailTrace_2158431
  have hstable : (prefixWord ++ tailWord_2158431).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2158431).length < 2 ^ (prefixWord ++ tailWord_2158431).sum := by decide
  have hdescent : baseEnd_2158431 < baseStart_2158431 := by decide
  rcases family_descends (prefixWord ++ tailWord_2158431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2158444 : List Nat := [2, 2, 1, 1, 4, 2, 3, 7]
def baseStart_2158444 : Nat := 118140960795 + 2158444 * 2 ^ 59
def prefixEnd_2158444 : Nat := 4983230072969 + 3 ^ 40 * 2158444 * 2
def baseEnd_2158444 : Nat := 82097721319500615675815

theorem tailTrace_2158444 : CollatzResearch.WordTrace tailWord_2158444 prefixEnd_2158444 82097721319500615675815 := by
  unfold tailWord_2158444
  simp only [CollatzResearch.WordTrace]
  refine ⟨39362460096166747865973193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52483280128222330487964257 39362460096166747865973193)
  ·
    refine ⟨29521845072125060899479895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39362460096166747865973193 29521845072125060899479895)
    ·
      refine ⟨44282767608187591349219843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29521845072125060899479895 44282767608187591349219843)
      ·
        refine ⟨66424151412281387023829765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44282767608187591349219843 66424151412281387023829765)
        ·
          refine ⟨12454528389802760066968081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 66424151412281387023829765 12454528389802760066968081)
          ·
            refine ⟨9340896292352070050226061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12454528389802760066968081 9340896292352070050226061)
            ·
              refine ⟨3502836109632026268834773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9340896292352070050226061 3502836109632026268834773)
              ·
                refine ⟨82097721319500615675815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3502836109632026268834773 82097721319500615675815)
                ·
                  rfl

theorem cell22_2158444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 3, 7].length) (baseStart_2158444 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2158444 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2158444 prefixEnd_2158444 := by exact prefixLift 2158444
  have htrace : WordTrace (prefixWord ++ tailWord_2158444) baseStart_2158444 baseEnd_2158444 := by
    simpa [prefixWord, tailWord_2158444, baseEnd_2158444] using wordTrace_append hprefix tailTrace_2158444
  have hstable : (prefixWord ++ tailWord_2158444).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2158444).length < 2 ^ (prefixWord ++ tailWord_2158444).sum := by decide
  have hdescent : baseEnd_2158444 < baseStart_2158444 := by decide
  rcases family_descends (prefixWord ++ tailWord_2158444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2158493 : List Nat := [1, 4, 2, 1, 2, 3, 2, 1, 3, 3]
def baseStart_2158493 : Nat := 118140960795 + 2158493 * 2 ^ 59
def prefixEnd_2158493 : Nat := 4983230072969 + 3 ^ 40 * 2158493 * 2
def baseEnd_2158493 : Nat := 738896265576885746607185

theorem tailTrace_2158493 : CollatzResearch.WordTrace tailWord_2158493 prefixEnd_2158493 738896265576885746607185 := by
  unfold tailWord_2158493
  simp only [CollatzResearch.WordTrace]
  refine ⟨78726707369155977100480133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52484471579437318066986755 78726707369155977100480133)
  ·
    refine ⟨14761257631716745706340025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 78726707369155977100480133 14761257631716745706340025)
    ·
      refine ⟨11070943223787559279755019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14761257631716745706340025 11070943223787559279755019)
      ·
        refine ⟨16606414835681338919632529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11070943223787559279755019 16606414835681338919632529)
        ·
          refine ⟨12454811126761004189724397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16606414835681338919632529 12454811126761004189724397)
          ·
            refine ⟨4670554172535376571146649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12454811126761004189724397 4670554172535376571146649)
            ·
              refine ⟨3502915629401532428359987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4670554172535376571146649 3502915629401532428359987)
              ·
                refine ⟨5254373444102298642539981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3502915629401532428359987 5254373444102298642539981)
                ·
                  refine ⟨1970390041538361990952493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5254373444102298642539981 1970390041538361990952493)
                  ·
                    refine ⟨738896265576885746607185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1970390041538361990952493 738896265576885746607185)
                    ·
                      rfl

theorem cell22_2158493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 2, 1, 3, 3].length) (baseStart_2158493 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2158493 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2158493 prefixEnd_2158493 := by exact prefixLift 2158493
  have htrace : WordTrace (prefixWord ++ tailWord_2158493) baseStart_2158493 baseEnd_2158493 := by
    simpa [prefixWord, tailWord_2158493, baseEnd_2158493] using wordTrace_append hprefix tailTrace_2158493
  have hstable : (prefixWord ++ tailWord_2158493).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2158493).length < 2 ^ (prefixWord ++ tailWord_2158493).sum := by decide
  have hdescent : baseEnd_2158493 < baseStart_2158493 := by decide
  rcases family_descends (prefixWord ++ tailWord_2158493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2158557 : List Nat := [1, 4, 3, 1, 4, 1, 2, 1, 5]
def baseStart_2158557 : Nat := 118140960795 + 2158557 * 2 ^ 59
def prefixEnd_2158557 : Nat := 4983230072969 + 3 ^ 40 * 2158557 * 2
def baseEnd_2158557 : Nat := 246306058028270304335663

theorem tailTrace_2158557 : CollatzResearch.WordTrace tailWord_2158557 prefixEnd_2158557 246306058028270304335663 := by
  unfold tailWord_2158557
  simp only [CollatzResearch.WordTrace]
  refine ⟨78729041640924116030809925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52486027760616077353873283 78729041640924116030809925)
  ·
    refine ⟨14761695307673271755776861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 78729041640924116030809925 14761695307673271755776861)
    ·
      refine ⟨5535635740377476908416323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14761695307673271755776861 5535635740377476908416323)
      ·
        refine ⟨8303453610566215362624485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5535635740377476908416323 8303453610566215362624485)
        ·
          refine ⟨1556897551981165380492091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8303453610566215362624485 1556897551981165380492091)
          ·
            refine ⟨2335346327971748070738137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1556897551981165380492091 2335346327971748070738137)
            ·
              refine ⟨1751509745978811053053603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2335346327971748070738137 1751509745978811053053603)
              ·
                refine ⟨2627264618968216579580405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1751509745978811053053603 2627264618968216579580405)
                ·
                  refine ⟨246306058028270304335663, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2627264618968216579580405 246306058028270304335663)
                  ·
                    rfl

theorem cell22_2158557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 4, 1, 2, 1, 5].length) (baseStart_2158557 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2158557 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2158557 prefixEnd_2158557 := by exact prefixLift 2158557
  have htrace : WordTrace (prefixWord ++ tailWord_2158557) baseStart_2158557 baseEnd_2158557 := by
    simpa [prefixWord, tailWord_2158557, baseEnd_2158557] using wordTrace_append hprefix tailTrace_2158557
  have hstable : (prefixWord ++ tailWord_2158557).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2158557).length < 2 ^ (prefixWord ++ tailWord_2158557).sum := by decide
  have hdescent : baseEnd_2158557 < baseStart_2158557 := by decide
  rcases family_descends (prefixWord ++ tailWord_2158557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2158596 : List Nat := [2, 3, 2, 4, 11]
def baseStart_2158596 : Nat := 118140960795 + 2158596 * 2 ^ 59
def prefixEnd_2158596 : Nat := 4983230072969 + 3 ^ 40 * 2158596 * 2
def baseEnd_2158596 : Nat := 3040870471530155601983

theorem tailTrace_2158596 : CollatzResearch.WordTrace tailWord_2158596 prefixEnd_2158596 3040870471530155601983 := by
  unfold tailWord_2158596
  simp only [CollatzResearch.WordTrace]
  refine ⟨39365232043891412845739821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52486976058521883794319761 39365232043891412845739821)
  ·
    refine ⟨14761962016459279817152433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39365232043891412845739821 14761962016459279817152433)
    ·
      refine ⟨11071471512344459862864325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14761962016459279817152433 11071471512344459862864325)
      ·
        refine ⟨2075900908564586224287061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11071471512344459862864325 2075900908564586224287061)
        ·
          refine ⟨3040870471530155601983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 2075900908564586224287061 3040870471530155601983)
          ·
            rfl

theorem cell22_2158596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 11].length) (baseStart_2158596 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2158596 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2158596 prefixEnd_2158596 := by exact prefixLift 2158596
  have htrace : WordTrace (prefixWord ++ tailWord_2158596) baseStart_2158596 baseEnd_2158596 := by
    simpa [prefixWord, tailWord_2158596, baseEnd_2158596] using wordTrace_append hprefix tailTrace_2158596
  have hstable : (prefixWord ++ tailWord_2158596).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2158596).length < 2 ^ (prefixWord ++ tailWord_2158596).sum := by decide
  have hdescent : baseEnd_2158596 < baseStart_2158596 := by decide
  rcases family_descends (prefixWord ++ tailWord_2158596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2158602 : List Nat := [3, 1, 2, 2, 4, 2, 2, 2, 4]
def baseStart_2158602 : Nat := 118140960795 + 2158602 * 2 ^ 59
def prefixEnd_2158602 : Nat := 4983230072969 + 3 ^ 40 * 2158602 * 2
def baseEnd_2158602 : Nat := 246311192834815265210617

theorem tailTrace_2158602 : CollatzResearch.WordTrace tailWord_2158602 prefixEnd_2158602 246311192834815265210617 := by
  unfold tailWord_2158602
  simp only [CollatzResearch.WordTrace]
  refine ⟨19682670731440272179049515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52487121950507392477465373 19682670731440272179049515)
  ·
    refine ⟨29524006097160408268574273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19682670731440272179049515 29524006097160408268574273)
    ·
      refine ⟨22143004572870306201430705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29524006097160408268574273 22143004572870306201430705)
      ·
        refine ⟨16607253429652729651073029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22143004572870306201430705 16607253429652729651073029)
        ·
          refine ⟨3113860018059886809576193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16607253429652729651073029 3113860018059886809576193)
          ·
            refine ⟨2335395013544915107182145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3113860018059886809576193 2335395013544915107182145)
            ·
              refine ⟨1751546260158686330386609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2335395013544915107182145 1751546260158686330386609)
              ·
                refine ⟨1313659695119014747789957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1751546260158686330386609 1313659695119014747789957)
                ·
                  refine ⟨246311192834815265210617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1313659695119014747789957 246311192834815265210617)
                  ·
                    rfl

theorem cell22_2158602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 2, 2, 2, 4].length) (baseStart_2158602 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2158602 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2158602 prefixEnd_2158602 := by exact prefixLift 2158602
  have htrace : WordTrace (prefixWord ++ tailWord_2158602) baseStart_2158602 baseEnd_2158602 := by
    simpa [prefixWord, tailWord_2158602, baseEnd_2158602] using wordTrace_append hprefix tailTrace_2158602
  have hstable : (prefixWord ++ tailWord_2158602).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2158602).length < 2 ^ (prefixWord ++ tailWord_2158602).sum := by decide
  have hdescent : baseEnd_2158602 < baseStart_2158602 := by decide
  rcases family_descends (prefixWord ++ tailWord_2158602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2158613 : List Nat := [1, 3, 2, 1, 5, 2, 1, 7]
def baseStart_2158613 : Nat := 118140960795 + 2158613 * 2 ^ 59
def prefixEnd_2158613 : Nat := 4983230072969 + 3 ^ 40 * 2158613 * 2
def baseEnd_2158613 : Nat := 82104149336582825956313

theorem tailTrace_2158613 : CollatzResearch.WordTrace tailWord_2158613 prefixEnd_2158613 82104149336582825956313 := by
  unfold tailWord_2158613
  simp only [CollatzResearch.WordTrace]
  refine ⟨78731084128721237594848493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52487389419147491729898995 78731084128721237594848493)
  ·
    refine ⟨29524156548270464098068185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 78731084128721237594848493 29524156548270464098068185)
    ·
      refine ⟨22143117411202848073551139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29524156548270464098068185 22143117411202848073551139)
      ·
        refine ⟨33214676116804272110326709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22143117411202848073551139 33214676116804272110326709)
        ·
          refine ⟨3113875885950400510343129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 33214676116804272110326709 3113875885950400510343129)
          ·
            refine ⟨2335406914462800382757347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3113875885950400510343129 2335406914462800382757347)
            ·
              refine ⟨3503110371694200574136021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2335406914462800382757347 3503110371694200574136021)
              ·
                refine ⟨82104149336582825956313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3503110371694200574136021 82104149336582825956313)
                ·
                  rfl

theorem cell22_2158613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 2, 1, 7].length) (baseStart_2158613 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2158613 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2158613 prefixEnd_2158613 := by exact prefixLift 2158613
  have htrace : WordTrace (prefixWord ++ tailWord_2158613) baseStart_2158613 baseEnd_2158613 := by
    simpa [prefixWord, tailWord_2158613, baseEnd_2158613] using wordTrace_append hprefix tailTrace_2158613
  have hstable : (prefixWord ++ tailWord_2158613).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2158613).length < 2 ^ (prefixWord ++ tailWord_2158613).sum := by decide
  have hdescent : baseEnd_2158613 < baseStart_2158613 := by decide
  rcases family_descends (prefixWord ++ tailWord_2158613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2158626 : List Nat := [3, 3, 1, 1, 1, 2, 1, 2, 2, 6]
def baseStart_2158626 : Nat := 118140960795 + 2158626 * 2 ^ 59
def prefixEnd_2158626 : Nat := 4983230072969 + 3 ^ 40 * 2158626 * 2
def baseEnd_2158626 : Nat := 738941794194917733031777

theorem tailTrace_2158626 : CollatzResearch.WordTrace tailWord_2158626 prefixEnd_2158626 738941794194917733031777 := by
  unfold tailWord_2158626
  simp only [CollatzResearch.WordTrace]
  refine ⟨19682889569418535203767933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52487705518449427210047821 19682889569418535203767933)
  ·
    refine ⟨7381083588531950701412975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19682889569418535203767933 7381083588531950701412975)
    ·
      refine ⟨11071625382797926052119463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7381083588531950701412975 11071625382797926052119463)
      ·
        refine ⟨16607438074196889078179195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11071625382797926052119463 16607438074196889078179195)
        ·
          refine ⟨24911157111295333617268793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16607438074196889078179195 24911157111295333617268793)
          ·
            refine ⟨18683367833471500212951595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24911157111295333617268793 18683367833471500212951595)
            ·
              refine ⟨28025051750207250319427393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18683367833471500212951595 28025051750207250319427393)
              ·
                refine ⟨21018788812655437739570545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28025051750207250319427393 21018788812655437739570545)
                ·
                  refine ⟨15764091609491578304677909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21018788812655437739570545 15764091609491578304677909)
                  ·
                    refine ⟨738941794194917733031777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15764091609491578304677909 738941794194917733031777)
                    ·
                      rfl

theorem cell22_2158626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 2, 2, 6].length) (baseStart_2158626 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2158626 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2158626 prefixEnd_2158626 := by exact prefixLift 2158626
  have htrace : WordTrace (prefixWord ++ tailWord_2158626) baseStart_2158626 baseEnd_2158626 := by
    simpa [prefixWord, tailWord_2158626, baseEnd_2158626] using wordTrace_append hprefix tailTrace_2158626
  have hstable : (prefixWord ++ tailWord_2158626).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2158626).length < 2 ^ (prefixWord ++ tailWord_2158626).sum := by decide
  have hdescent : baseEnd_2158626 < baseStart_2158626 := by decide
  rcases family_descends (prefixWord ++ tailWord_2158626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2158632 : List Nat := [2, 1, 5, 3, 1, 2, 1, 1, 2, 4]
def baseStart_2158632 : Nat := 118140960795 + 2158632 * 2 ^ 59
def prefixEnd_2158632 : Nat := 4983230072969 + 3 ^ 40 * 2158632 * 2
def baseEnd_2158632 : Nat := 738943848117535717381759

theorem tailTrace_2158632 : CollatzResearch.WordTrace tailWord_2158632 prefixEnd_2158632 738943848117535717381759 := by
  unfold tailWord_2158632
  simp only [CollatzResearch.WordTrace]
  refine ⟨39365888557826201919895075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52487851410434935893193433 39365888557826201919895075)
  ·
    refine ⟨59048832836739302879842613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39365888557826201919895075 59048832836739302879842613)
    ·
      refine ⟨5535828078444309644985245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 59048832836739302879842613 5535828078444309644985245)
      ·
        refine ⟨2075935529416616116869467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5535828078444309644985245 2075935529416616116869467)
        ·
          refine ⟨3113903294124924175304201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2075935529416616116869467 3113903294124924175304201)
          ·
            refine ⟨2335427470593693131478151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3113903294124924175304201 2335427470593693131478151)
            ·
              refine ⟨3503141205890539697217227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2335427470593693131478151 3503141205890539697217227)
              ·
                refine ⟨5254711808835809545825841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3503141205890539697217227 5254711808835809545825841)
                ·
                  refine ⟨3941033856626857159369381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5254711808835809545825841 3941033856626857159369381)
                  ·
                    refine ⟨738943848117535717381759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3941033856626857159369381 738943848117535717381759)
                    ·
                      rfl

theorem cell22_2158632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 2, 1, 1, 2, 4].length) (baseStart_2158632 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2158632 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2158632 prefixEnd_2158632 := by exact prefixLift 2158632
  have htrace : WordTrace (prefixWord ++ tailWord_2158632) baseStart_2158632 baseEnd_2158632 := by
    simpa [prefixWord, tailWord_2158632, baseEnd_2158632] using wordTrace_append hprefix tailTrace_2158632
  have hstable : (prefixWord ++ tailWord_2158632).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2158632).length < 2 ^ (prefixWord ++ tailWord_2158632).sum := by decide
  have hdescent : baseEnd_2158632 < baseStart_2158632 := by decide
  rcases family_descends (prefixWord ++ tailWord_2158632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2158645 : List Nat := [1, 3, 3, 1, 1, 1, 3, 5, 1, 3]
def baseStart_2158645 : Nat := 118140960795 + 2158645 * 2 ^ 59
def prefixEnd_2158645 : Nat := 4983230072969 + 3 ^ 40 * 2158645 * 2
def baseEnd_2158645 : Nat := 738948298283208016806719

theorem tailTrace_2158645 : CollatzResearch.WordTrace tailWord_2158645 prefixEnd_2158645 738948298283208016806719 := by
  unfold tailWord_2158645
  simp only [CollatzResearch.WordTrace]
  refine ⟨78732251264605307060013389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52488167509736871373342259 78732251264605307060013389)
  ·
    refine ⟨29524594224226990147505021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 78732251264605307060013389 29524594224226990147505021)
    ·
      refine ⟨11071722834085121305314383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29524594224226990147505021 11071722834085121305314383)
      ·
        refine ⟨16607584251127681957971575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11071722834085121305314383 16607584251127681957971575)
        ·
          refine ⟨24911376376691522936957363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16607584251127681957971575 24911376376691522936957363)
          ·
            refine ⟨37367064565037284405436045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24911376376691522936957363 37367064565037284405436045)
            ·
              refine ⟨14012649211888981652038517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37367064565037284405436045 14012649211888981652038517)
              ·
                refine ⟨1313685863614592029878611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 14012649211888981652038517 1313685863614592029878611)
                ·
                  refine ⟨1970528795421888044817917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1313685863614592029878611 1970528795421888044817917)
                  ·
                    refine ⟨738948298283208016806719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1970528795421888044817917 738948298283208016806719)
                    ·
                      rfl

theorem cell22_2158645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 3, 5, 1, 3].length) (baseStart_2158645 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2158645 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2158645 prefixEnd_2158645 := by exact prefixLift 2158645
  have htrace : WordTrace (prefixWord ++ tailWord_2158645) baseStart_2158645 baseEnd_2158645 := by
    simpa [prefixWord, tailWord_2158645, baseEnd_2158645] using wordTrace_append hprefix tailTrace_2158645
  have hstable : (prefixWord ++ tailWord_2158645).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2158645).length < 2 ^ (prefixWord ++ tailWord_2158645).sum := by decide
  have hdescent : baseEnd_2158645 < baseStart_2158645 := by decide
  rcases family_descends (prefixWord ++ tailWord_2158645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2158656 : List Nat := [2, 1, 1, 2, 2, 4, 1, 2, 2, 5]
def baseStart_2158656 : Nat := 118140960795 + 2158656 * 2 ^ 59
def prefixEnd_2158656 : Nat := 4983230072969 + 3 ^ 40 * 2158656 * 2
def baseEnd_2158656 : Nat := 738952063808007654781685

theorem tailTrace_2158656 : CollatzResearch.WordTrace tailWord_2158656 prefixEnd_2158656 738952063808007654781685 := by
  unfold tailWord_2158656
  simp only [CollatzResearch.WordTrace]
  refine ⟨39366326233782727969331911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52488434978376970625775881 39366326233782727969331911)
  ·
    refine ⟨59049489350674091953997867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39366326233782727969331911 59049489350674091953997867)
    ·
      refine ⟨88574234026011137930996801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59049489350674091953997867 88574234026011137930996801)
      ·
        refine ⟨66430675519508353448247601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 88574234026011137930996801 66430675519508353448247601)
        ·
          refine ⟨49823006639631265086185701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66430675519508353448247601 49823006639631265086185701)
          ·
            refine ⟨9341813744930862203659819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 49823006639631265086185701 9341813744930862203659819)
            ·
              refine ⟨14012720617396293305489729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9341813744930862203659819 14012720617396293305489729)
              ·
                refine ⟨10509540463047219979117297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14012720617396293305489729 10509540463047219979117297)
                ·
                  refine ⟨7882155347285414984337973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10509540463047219979117297 7882155347285414984337973)
                  ·
                    refine ⟨738952063808007654781685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7882155347285414984337973 738952063808007654781685)
                    ·
                      rfl

theorem cell22_2158656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 1, 2, 2, 5].length) (baseStart_2158656 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2158656 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2158656 prefixEnd_2158656 := by exact prefixLift 2158656
  have htrace : WordTrace (prefixWord ++ tailWord_2158656) baseStart_2158656 baseEnd_2158656 := by
    simpa [prefixWord, tailWord_2158656, baseEnd_2158656] using wordTrace_append hprefix tailTrace_2158656
  have hstable : (prefixWord ++ tailWord_2158656).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2158656).length < 2 ^ (prefixWord ++ tailWord_2158656).sum := by decide
  have hdescent : baseEnd_2158656 < baseStart_2158656 := by decide
  rcases family_descends (prefixWord ++ tailWord_2158656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2158662 : List Nat := [6, 1, 1, 1, 1, 1, 4, 1, 3, 3]
def baseStart_2158662 : Nat := 118140960795 + 2158662 * 2 ^ 59
def prefixEnd_2158662 : Nat := 4983230072969 + 3 ^ 40 * 2158662 * 2
def baseEnd_2158662 : Nat := 738954117730625639131667

theorem tailTrace_2158662 : CollatzResearch.WordTrace tailWord_2158662 prefixEnd_2158662 738954117730625639131667 := by
  unfold tailWord_2158662
  simp only [CollatzResearch.WordTrace]
  refine ⟨2460402228298241217605695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 52488580870362479308921493 2460402228298241217605695)
  ·
    refine ⟨3690603342447361826408543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2460402228298241217605695 3690603342447361826408543)
    ·
      refine ⟨5535905013671042739612815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3690603342447361826408543 5535905013671042739612815)
      ·
        refine ⟨8303857520506564109419223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5535905013671042739612815 8303857520506564109419223)
        ·
          refine ⟨12455786280759846164128835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8303857520506564109419223 12455786280759846164128835)
          ·
            refine ⟨18683679421139769246193253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12455786280759846164128835 18683679421139769246193253)
            ·
              refine ⟨3503189891463706733661235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18683679421139769246193253 3503189891463706733661235)
              ·
                refine ⟨5254784837195560100491853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3503189891463706733661235 5254784837195560100491853)
                ·
                  refine ⟨1970544313948335037684445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5254784837195560100491853 1970544313948335037684445)
                  ·
                    refine ⟨738954117730625639131667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1970544313948335037684445 738954117730625639131667)
                    ·
                      rfl

theorem cell22_2158662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 4, 1, 3, 3].length) (baseStart_2158662 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2158662 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2158662 prefixEnd_2158662 := by exact prefixLift 2158662
  have htrace : WordTrace (prefixWord ++ tailWord_2158662) baseStart_2158662 baseEnd_2158662 := by
    simpa [prefixWord, tailWord_2158662, baseEnd_2158662] using wordTrace_append hprefix tailTrace_2158662
  have hstable : (prefixWord ++ tailWord_2158662).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2158662).length < 2 ^ (prefixWord ++ tailWord_2158662).sum := by decide
  have hdescent : baseEnd_2158662 < baseStart_2158662 := by decide
  rcases family_descends (prefixWord ++ tailWord_2158662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2158688 : List Nat := [2, 1, 1, 3, 2, 3, 1, 4, 1, 4]
def baseStart_2158688 : Nat := 118140960795 + 2158688 * 2 ^ 59
def prefixEnd_2158688 : Nat := 4983230072969 + 3 ^ 40 * 2158688 * 2
def baseEnd_2158688 : Nat := 738963018061970237981587

theorem tailTrace_2158688 : CollatzResearch.WordTrace tailWord_2158688 prefixEnd_2158688 738963018061970237981587 := by
  unfold tailWord_2158688
  simp only [CollatzResearch.WordTrace]
  refine ⟨39366909801724762701914359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52489213068966350269219145 39366909801724762701914359)
  ·
    refine ⟨59050364702587144052871539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39366909801724762701914359 59050364702587144052871539)
    ·
      refine ⟨88575547053880716079307309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59050364702587144052871539 88575547053880716079307309)
      ·
        refine ⟨33215830145205268529740241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 88575547053880716079307309 33215830145205268529740241)
        ·
          refine ⟨24911872608903951397305181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33215830145205268529740241 24911872608903951397305181)
          ·
            refine ⟨9341952228338981773989443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24911872608903951397305181 9341952228338981773989443)
            ·
              refine ⟨14012928342508472660984165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9341952228338981773989443 14012928342508472660984165)
              ·
                refine ⟨2627424064220338623934531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14012928342508472660984165 2627424064220338623934531)
                ·
                  refine ⟨3941136096330507935901797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2627424064220338623934531 3941136096330507935901797)
                  ·
                    refine ⟨738963018061970237981587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3941136096330507935901797 738963018061970237981587)
                    ·
                      rfl

theorem cell22_2158688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 1, 4, 1, 4].length) (baseStart_2158688 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2158688 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2158688 prefixEnd_2158688 := by exact prefixLift 2158688
  have htrace : WordTrace (prefixWord ++ tailWord_2158688) baseStart_2158688 baseEnd_2158688 := by
    simpa [prefixWord, tailWord_2158688, baseEnd_2158688] using wordTrace_append hprefix tailTrace_2158688
  have hstable : (prefixWord ++ tailWord_2158688).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2158688).length < 2 ^ (prefixWord ++ tailWord_2158688).sum := by decide
  have hdescent : baseEnd_2158688 < baseStart_2158688 := by decide
  rcases family_descends (prefixWord ++ tailWord_2158688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2158782 : List Nat := [4, 2, 1, 1, 5, 1, 1, 7]
def baseStart_2158782 : Nat := 118140960795 + 2158782 * 2 ^ 59
def prefixEnd_2158782 : Nat := 4983230072969 + 3 ^ 40 * 2158782 * 2
def baseEnd_2158782 : Nat := 82110577353665036236811

theorem tailTrace_2158782 : CollatzResearch.WordTrace tailWord_2158782 prefixEnd_2158782 82110577353665036236811 := by
  unfold tailWord_2158782
  simp only [CollatzResearch.WordTrace]
  refine ⟨9842156008138622432218825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 52491498710072652971833733 9842156008138622432218825)
  ·
    refine ⟨7381617006103966824164119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9842156008138622432218825 7381617006103966824164119)
    ·
      refine ⟨11072425509155950236246179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7381617006103966824164119 11072425509155950236246179)
      ·
        refine ⟨16608638263733925354369269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11072425509155950236246179 16608638263733925354369269)
        ·
          refine ⟨1557059837225055501972119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 16608638263733925354369269 1557059837225055501972119)
          ·
            refine ⟨2335589755837583252958179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1557059837225055501972119 2335589755837583252958179)
            ·
              refine ⟨3503384633756374879437269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2335589755837583252958179 3503384633756374879437269)
              ·
                refine ⟨82110577353665036236811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3503384633756374879437269 82110577353665036236811)
                ·
                  rfl

theorem cell22_2158782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 5, 1, 1, 7].length) (baseStart_2158782 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2158782 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2158782 prefixEnd_2158782 := by exact prefixLift 2158782
  have htrace : WordTrace (prefixWord ++ tailWord_2158782) baseStart_2158782 baseEnd_2158782 := by
    simpa [prefixWord, tailWord_2158782, baseEnd_2158782] using wordTrace_append hprefix tailTrace_2158782
  have hstable : (prefixWord ++ tailWord_2158782).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2158782).length < 2 ^ (prefixWord ++ tailWord_2158782).sum := by decide
  have hdescent : baseEnd_2158782 < baseStart_2158782 := by decide
  rcases family_descends (prefixWord ++ tailWord_2158782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2158853 : List Nat := [1, 3, 1, 1, 2, 1, 2, 5, 1, 5]
def baseStart_2158853 : Nat := 118140960795 + 2158853 * 2 ^ 59
def prefixEnd_2158853 : Nat := 4983230072969 + 3 ^ 40 * 2158853 * 2
def baseEnd_2158853 : Nat := 739019500933964807606081

theorem tailTrace_2158853 : CollatzResearch.WordTrace tailWord_2158853 prefixEnd_2158853 739019500933964807606081 := by
  unfold tailWord_2158853
  simp only [CollatzResearch.WordTrace]
  refine ⟨78739837647851758583585213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52493225098567839055723475 78739837647851758583585213)
  ·
    refine ⟨29527439117944409468844455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 78739837647851758583585213 29527439117944409468844455)
    ·
      refine ⟨44291158676916614203266683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29527439117944409468844455 44291158676916614203266683)
      ·
        refine ⟨66436738015374921304900025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44291158676916614203266683 66436738015374921304900025)
        ·
          refine ⟨49827553511531190978675019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66436738015374921304900025 49827553511531190978675019)
          ·
            refine ⟨74741330267296786468012529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49827553511531190978675019 74741330267296786468012529)
            ·
              refine ⟨56055997700472589851009397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 74741330267296786468012529 56055997700472589851009397)
              ·
                refine ⟨5255249784419305298532131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 56055997700472589851009397 5255249784419305298532131)
                ·
                  refine ⟨7882874676628957947798197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5255249784419305298532131 7882874676628957947798197)
                  ·
                    refine ⟨739019500933964807606081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7882874676628957947798197 739019500933964807606081)
                    ·
                      rfl

theorem cell22_2158853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 5, 1, 5].length) (baseStart_2158853 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2158853 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2158853 prefixEnd_2158853 := by exact prefixLift 2158853
  have htrace : WordTrace (prefixWord ++ tailWord_2158853) baseStart_2158853 baseEnd_2158853 := by
    simpa [prefixWord, tailWord_2158853, baseEnd_2158853] using wordTrace_append hprefix tailTrace_2158853
  have hstable : (prefixWord ++ tailWord_2158853).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2158853).length < 2 ^ (prefixWord ++ tailWord_2158853).sum := by decide
  have hdescent : baseEnd_2158853 < baseStart_2158853 := by decide
  rcases family_descends (prefixWord ++ tailWord_2158853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2158900 : List Nat := [2, 5, 1, 1, 1, 2, 1, 9]
def baseStart_2158900 : Nat := 118140960795 + 2158900 * 2 ^ 59
def prefixEnd_2158900 : Nat := 4983230072969 + 3 ^ 40 * 2158900 * 2
def baseEnd_2158900 : Nat := 82115065554941372408993

theorem tailTrace_2158900 : CollatzResearch.WordTrace tailWord_2158900 prefixEnd_2158900 82115065554941372408993 := by
  unfold tailWord_2158900
  simp only [CollatzResearch.WordTrace]
  refine ⟨39370775939340742805273077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52494367919120990407030769 39370775939340742805273077)
  ·
    refine ⟨3691010244313194637994351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 39370775939340742805273077 3691010244313194637994351)
    ·
      refine ⟨5536515366469791956991527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3691010244313194637994351 5536515366469791956991527)
      ·
        refine ⟨8304773049704687935487291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5536515366469791956991527 8304773049704687935487291)
        ·
          refine ⟨12457159574557031903230937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8304773049704687935487291 12457159574557031903230937)
          ·
            refine ⟨9342869680917773927423203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12457159574557031903230937 9342869680917773927423203)
            ·
              refine ⟨14014304521376660891134805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9342869680917773927423203 14014304521376660891134805)
              ·
                refine ⟨82115065554941372408993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 14014304521376660891134805 82115065554941372408993)
                ·
                  rfl

theorem cell22_2158900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 1, 9].length) (baseStart_2158900 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2158900 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2158900 prefixEnd_2158900 := by exact prefixLift 2158900
  have htrace : WordTrace (prefixWord ++ tailWord_2158900) baseStart_2158900 baseEnd_2158900 := by
    simpa [prefixWord, tailWord_2158900, baseEnd_2158900] using wordTrace_append hprefix tailTrace_2158900
  have hstable : (prefixWord ++ tailWord_2158900).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2158900).length < 2 ^ (prefixWord ++ tailWord_2158900).sum := by decide
  have hdescent : baseEnd_2158900 < baseStart_2158900 := by decide
  rcases family_descends (prefixWord ++ tailWord_2158900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2158915 : List Nat := [1, 1, 1, 3, 1, 3, 2, 4, 3, 3]
def baseStart_2158915 : Nat := 118140960795 + 2158915 * 2 ^ 59
def prefixEnd_2158915 : Nat := 4983230072969 + 3 ^ 40 * 2158915 * 2
def baseEnd_2158915 : Nat := 739040724801017312555891

theorem tailTrace_2158915 : CollatzResearch.WordTrace tailWord_2158915 prefixEnd_2158915 739040724801017312555891 := by
  unfold tailWord_2158915
  simp only [CollatzResearch.WordTrace]
  refine ⟨78742098973627143172342199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52494732649084762114894799 78742098973627143172342199)
  ·
    refine ⟨118113148460440714758513299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78742098973627143172342199 118113148460440714758513299)
    ·
      refine ⟨177169722690661072137769949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118113148460440714758513299 177169722690661072137769949)
      ·
        refine ⟨66438646008997902051663731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 177169722690661072137769949 66438646008997902051663731)
        ·
          refine ⟨99657969013496853077495597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66438646008997902051663731 99657969013496853077495597)
          ·
            refine ⟨37371738380061319904060849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 99657969013496853077495597 37371738380061319904060849)
            ·
              refine ⟨28028803785045989928045637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37371738380061319904060849 28028803785045989928045637)
              ·
                refine ⟨5255400709696123111508557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 28028803785045989928045637 5255400709696123111508557)
                ·
                  refine ⟨1970775266136046166815709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5255400709696123111508557 1970775266136046166815709)
                  ·
                    refine ⟨739040724801017312555891, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1970775266136046166815709 739040724801017312555891)
                    ·
                      rfl

theorem cell22_2158915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 4, 3, 3].length) (baseStart_2158915 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2158915 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2158915 prefixEnd_2158915 := by exact prefixLift 2158915
  have htrace : WordTrace (prefixWord ++ tailWord_2158915) baseStart_2158915 baseEnd_2158915 := by
    simpa [prefixWord, tailWord_2158915, baseEnd_2158915] using wordTrace_append hprefix tailTrace_2158915
  have hstable : (prefixWord ++ tailWord_2158915).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2158915).length < 2 ^ (prefixWord ++ tailWord_2158915).sum := by decide
  have hdescent : baseEnd_2158915 < baseStart_2158915 := by decide
  rcases family_descends (prefixWord ++ tailWord_2158915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2158949 : List Nat := [1, 3, 1, 3, 1, 4, 1, 4, 1, 3]
def baseStart_2158949 : Nat := 118140960795 + 2158949 * 2 ^ 59
def prefixEnd_2158949 : Nat := 4983230072969 + 3 ^ 40 * 2158949 * 2
def baseEnd_2158949 : Nat := 739052363695852557205787

theorem tailTrace_2158949 : CollatzResearch.WordTrace tailWord_2158949 prefixEnd_2158949 739052363695852557205787 := by
  unfold tailWord_2158949
  simp only [CollatzResearch.WordTrace]
  refine ⟨78743339055503966979079901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52495559370335977986053267 78743339055503966979079901)
  ·
    refine ⟨29528752145813987617154963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 78743339055503966979079901 29528752145813987617154963)
    ·
      refine ⟨44293128218720981425732445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29528752145813987617154963 44293128218720981425732445)
      ·
        refine ⟨16609923082020368034649667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44293128218720981425732445 16609923082020368034649667)
        ·
          refine ⟨24914884623030552051974501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16609923082020368034649667 24914884623030552051974501)
          ·
            refine ⟨4671540866818228509745219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24914884623030552051974501 4671540866818228509745219)
            ·
              refine ⟨7007311300227342764617829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4671540866818228509745219 7007311300227342764617829)
              ·
                refine ⟨1313870868792626768365843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7007311300227342764617829 1313870868792626768365843)
                ·
                  refine ⟨1970806303188940152548765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1313870868792626768365843 1970806303188940152548765)
                  ·
                    refine ⟨739052363695852557205787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1970806303188940152548765 739052363695852557205787)
                    ·
                      rfl

theorem cell22_2158949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 1, 4, 1, 3].length) (baseStart_2158949 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2158949 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2158949 prefixEnd_2158949 := by exact prefixLift 2158949
  have htrace : WordTrace (prefixWord ++ tailWord_2158949) baseStart_2158949 baseEnd_2158949 := by
    simpa [prefixWord, tailWord_2158949, baseEnd_2158949] using wordTrace_append hprefix tailTrace_2158949
  have hstable : (prefixWord ++ tailWord_2158949).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2158949).length < 2 ^ (prefixWord ++ tailWord_2158949).sum := by decide
  have hdescent : baseEnd_2158949 < baseStart_2158949 := by decide
  rcases family_descends (prefixWord ++ tailWord_2158949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2158960 : List Nat := [2, 1, 1, 1, 4, 4, 1, 1, 2, 5]
def baseStart_2158960 : Nat := 118140960795 + 2158960 * 2 ^ 59
def prefixEnd_2158960 : Nat := 4983230072969 + 3 ^ 40 * 2158960 * 2
def baseEnd_2158960 : Nat := 739056129220652195180753

theorem tailTrace_2158960 : CollatzResearch.WordTrace tailWord_2158960 prefixEnd_2158960 739056129220652195180753 := by
  unfold tailWord_2158960
  simp only [CollatzResearch.WordTrace]
  refine ⟨39371870129232057928865167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52495826838976077238486889 39371870129232057928865167)
  ·
    refine ⟨59057805193848086893297751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39371870129232057928865167 59057805193848086893297751)
    ·
      refine ⟨88586707790772130339946627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59057805193848086893297751 88586707790772130339946627)
      ·
        refine ⟨132880061686158195509919941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88586707790772130339946627 132880061686158195509919941)
        ·
          refine ⟨24915011566154661658109989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 132880061686158195509919941 24915011566154661658109989)
          ·
            refine ⟨4671564668653999060895623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24915011566154661658109989 4671564668653999060895623)
            ·
              refine ⟨7007347002980998591343435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4671564668653999060895623 7007347002980998591343435)
              ·
                refine ⟨10511020504471497887015153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7007347002980998591343435 10511020504471497887015153)
                ·
                  refine ⟨7883265378353623415261365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10511020504471497887015153 7883265378353623415261365)
                  ·
                    refine ⟨739056129220652195180753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7883265378353623415261365 739056129220652195180753)
                    ·
                      rfl

theorem cell22_2158960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 1, 1, 2, 5].length) (baseStart_2158960 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2158960 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2158960 prefixEnd_2158960 := by exact prefixLift 2158960
  have htrace : WordTrace (prefixWord ++ tailWord_2158960) baseStart_2158960 baseEnd_2158960 := by
    simpa [prefixWord, tailWord_2158960, baseEnd_2158960] using wordTrace_append hprefix tailTrace_2158960
  have hstable : (prefixWord ++ tailWord_2158960).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2158960).length < 2 ^ (prefixWord ++ tailWord_2158960).sum := by decide
  have hdescent : baseEnd_2158960 < baseStart_2158960 := by decide
  rcases family_descends (prefixWord ++ tailWord_2158960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2158966 : List Nat := [5, 1, 1, 4, 1, 1, 1, 2, 3, 3]
def baseStart_2158966 : Nat := 118140960795 + 2158966 * 2 ^ 59
def prefixEnd_2158966 : Nat := 4983230072969 + 3 ^ 40 * 2158966 * 2
def baseEnd_2158966 : Nat := 739058183143270179530735

theorem tailTrace_2158966 : CollatzResearch.WordTrace tailWord_2158966 prefixEnd_2158966 739058183143270179530735 := by
  unfold tailWord_2158966
  simp only [CollatzResearch.WordTrace]
  refine ⟨4921497443527648680153047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 52495972730961585921632501 4921497443527648680153047)
  ·
    refine ⟨7382246165291473020229571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4921497443527648680153047 7382246165291473020229571)
    ·
      refine ⟨11073369247937209530344357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7382246165291473020229571 11073369247937209530344357)
      ·
        refine ⟨2076256733988226786939567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11073369247937209530344357 2076256733988226786939567)
        ·
          refine ⟨3114385100982340180409351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2076256733988226786939567 3114385100982340180409351)
          ·
            refine ⟨4671577651473510270614027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3114385100982340180409351 4671577651473510270614027)
            ·
              refine ⟨7007366477210265405921041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4671577651473510270614027 7007366477210265405921041)
              ·
                refine ⟨5255524857907699054440781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7007366477210265405921041 5255524857907699054440781)
                ·
                  refine ⟨1970821821715387145415293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5255524857907699054440781 1970821821715387145415293)
                  ·
                    refine ⟨739058183143270179530735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1970821821715387145415293 739058183143270179530735)
                    ·
                      rfl

theorem cell22_2158966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 1, 2, 3, 3].length) (baseStart_2158966 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2158966 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2158966 prefixEnd_2158966 := by exact prefixLift 2158966
  have htrace : WordTrace (prefixWord ++ tailWord_2158966) baseStart_2158966 baseEnd_2158966 := by
    simpa [prefixWord, tailWord_2158966, baseEnd_2158966] using wordTrace_append hprefix tailTrace_2158966
  have hstable : (prefixWord ++ tailWord_2158966).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2158966).length < 2 ^ (prefixWord ++ tailWord_2158966).sum := by decide
  have hdescent : baseEnd_2158966 < baseStart_2158966 := by decide
  rcases family_descends (prefixWord ++ tailWord_2158966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2158996 : List Nat := [2, 4, 2, 1, 4, 1, 1, 2, 5]
def baseStart_2158996 : Nat := 118140960795 + 2158996 * 2 ^ 59
def prefixEnd_2158996 : Nat := 4983230072969 + 3 ^ 40 * 2158996 * 2
def baseEnd_2158996 : Nat := 246356150918786700426881

theorem tailTrace_2158996 : CollatzResearch.WordTrace tailWord_2158996 prefixEnd_2158996 246356150918786700426881 := by
  unfold tailWord_2158996
  simp only [CollatzResearch.WordTrace]
  refine ⟨39372526643166847003020421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52496702190889129337360561 39372526643166847003020421)
  ·
    refine ⟨7382348745593783813066329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 39372526643166847003020421 7382348745593783813066329)
    ·
      refine ⟨5536761559195337859799747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7382348745593783813066329 5536761559195337859799747)
      ·
        refine ⟨8305142338793006789699621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5536761559195337859799747 8305142338793006789699621)
        ·
          refine ⟨1557214188523688773068679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8305142338793006789699621 1557214188523688773068679)
          ·
            refine ⟨2335821282785533159603019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1557214188523688773068679 2335821282785533159603019)
            ·
              refine ⟨3503731924178299739404529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2335821282785533159603019 3503731924178299739404529)
              ·
                refine ⟨2627798943133724804553397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3503731924178299739404529 2627798943133724804553397)
                ·
                  refine ⟨246356150918786700426881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2627798943133724804553397 246356150918786700426881)
                  ·
                    rfl

theorem cell22_2158996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 4, 1, 1, 2, 5].length) (baseStart_2158996 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2158996 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2158996 prefixEnd_2158996 := by exact prefixLift 2158996
  have htrace : WordTrace (prefixWord ++ tailWord_2158996) baseStart_2158996 baseEnd_2158996 := by
    simpa [prefixWord, tailWord_2158996, baseEnd_2158996] using wordTrace_append hprefix tailTrace_2158996
  have hstable : (prefixWord ++ tailWord_2158996).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2158996).length < 2 ^ (prefixWord ++ tailWord_2158996).sum := by decide
  have hdescent : baseEnd_2158996 < baseStart_2158996 := by decide
  rcases family_descends (prefixWord ++ tailWord_2158996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2159007 : List Nat := [1, 1, 2, 5, 1, 1, 1, 6, 4]
def baseStart_2159007 : Nat := 118140960795 + 2159007 * 2 ^ 59
def prefixEnd_2159007 : Nat := 4983230072969 + 3 ^ 40 * 2159007 * 2
def baseEnd_2159007 : Nat := 246357406093719913085203

theorem tailTrace_2159007 : CollatzResearch.WordTrace tailWord_2159007 prefixEnd_2159007 246357406093719913085203 := by
  unfold tailWord_2159007
  simp only [CollatzResearch.WordTrace]
  refine ⟨78745454489293842884691275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52496969659529228589794183 78745454489293842884691275)
  ·
    refine ⟨118118181733940764327036913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78745454489293842884691275 118118181733940764327036913)
    ·
      refine ⟨88588636300455573245277685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 118118181733940764327036913 88588636300455573245277685)
      ·
        refine ⟨8305184653167709991744783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 88588636300455573245277685 8305184653167709991744783)
        ·
          refine ⟨12457776979751564987617175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8305184653167709991744783 12457776979751564987617175)
          ·
            refine ⟨18686665469627347481425763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12457776979751564987617175 18686665469627347481425763)
            ·
              refine ⟨28029998204441021222138645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18686665469627347481425763 28029998204441021222138645)
              ·
                refine ⟨1313906165833172869787749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 28029998204441021222138645 1313906165833172869787749)
                ·
                  refine ⟨246357406093719913085203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1313906165833172869787749 246357406093719913085203)
                  ·
                    rfl

theorem cell22_2159007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 6, 4].length) (baseStart_2159007 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2159007 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2159007 prefixEnd_2159007 := by exact prefixLift 2159007
  have htrace : WordTrace (prefixWord ++ tailWord_2159007) baseStart_2159007 baseEnd_2159007 := by
    simpa [prefixWord, tailWord_2159007, baseEnd_2159007] using wordTrace_append hprefix tailTrace_2159007
  have hstable : (prefixWord ++ tailWord_2159007).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2159007).length < 2 ^ (prefixWord ++ tailWord_2159007).sum := by decide
  have hdescent : baseEnd_2159007 < baseStart_2159007 := by decide
  rcases family_descends (prefixWord ++ tailWord_2159007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2159052 : List Nat := [2, 2, 1, 4, 3, 2, 8]
def baseStart_2159052 : Nat := 118140960795 + 2159052 * 2 ^ 59
def prefixEnd_2159052 : Nat := 4983230072969 + 3 ^ 40 * 2159052 * 2
def baseEnd_2159052 : Nat := 27373615655584985995573

theorem tailTrace_2159052 : CollatzResearch.WordTrace tailWord_2159052 prefixEnd_2159052 27373615655584985995573 := by
  unfold tailWord_2159052
  simp only [CollatzResearch.WordTrace]
  refine ⟨39373547887065407785039705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52498063849420543713386273 39373547887065407785039705)
  ·
    refine ⟨29530160915299055838779779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39373547887065407785039705 29530160915299055838779779)
    ·
      refine ⟨44295241372948583758169669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29530160915299055838779779 44295241372948583758169669)
      ·
        refine ⟨8305357757427859454656813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 44295241372948583758169669 8305357757427859454656813)
        ·
          refine ⟨3114509159035447295496305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8305357757427859454656813 3114509159035447295496305)
          ·
            refine ⟨2335881869276585471622229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3114509159035447295496305 2335881869276585471622229)
            ·
              refine ⟨27373615655584985995573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2335881869276585471622229 27373615655584985995573)
              ·
                rfl

theorem cell22_2159052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 2, 8].length) (baseStart_2159052 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2159052 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2159052 prefixEnd_2159052 := by exact prefixLift 2159052
  have htrace : WordTrace (prefixWord ++ tailWord_2159052) baseStart_2159052 baseEnd_2159052 := by
    simpa [prefixWord, tailWord_2159052, baseEnd_2159052] using wordTrace_append hprefix tailTrace_2159052
  have hstable : (prefixWord ++ tailWord_2159052).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2159052).length < 2 ^ (prefixWord ++ tailWord_2159052).sum := by decide
  have hdescent : baseEnd_2159052 < baseStart_2159052 := by decide
  rcases family_descends (prefixWord ++ tailWord_2159052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2159058 : List Nat := [3, 2, 2, 4, 1, 1, 3, 2, 4]
def baseStart_2159058 : Nat := 118140960795 + 2159058 * 2 ^ 59
def prefixEnd_2159058 : Nat := 4983230072969 + 3 ^ 40 * 2159058 * 2
def baseEnd_2159058 : Nat := 246363225541137535410151

theorem tailTrace_2159058 : CollatzResearch.WordTrace tailWord_2159058 prefixEnd_2159058 246363225541137535410151 := by
  unfold tailWord_2159058
  simp only [CollatzResearch.WordTrace]
  refine ⟨19686828653027269648699457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52498209741406052396531885 19686828653027269648699457)
  ·
    refine ⟨14765121489770452236524593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19686828653027269648699457 14765121489770452236524593)
    ·
      refine ⟨11073841117327839177393445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14765121489770452236524593 11073841117327839177393445)
      ·
        refine ⟨2076345209498969845761271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11073841117327839177393445 2076345209498969845761271)
        ·
          refine ⟨3114517814248454768641907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2076345209498969845761271 3114517814248454768641907)
          ·
            refine ⟨4671776721372682152962861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3114517814248454768641907 4671776721372682152962861)
            ·
              refine ⟨1751916270514755807361073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4671776721372682152962861 1751916270514755807361073)
              ·
                refine ⟨1313937202886066855520805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1751916270514755807361073 1313937202886066855520805)
                ·
                  refine ⟨246363225541137535410151, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1313937202886066855520805 246363225541137535410151)
                  ·
                    rfl

theorem cell22_2159058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 3, 2, 4].length) (baseStart_2159058 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2159058 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2159058 prefixEnd_2159058 := by exact prefixLift 2159058
  have htrace : WordTrace (prefixWord ++ tailWord_2159058) baseStart_2159058 baseEnd_2159058 := by
    simpa [prefixWord, tailWord_2159058, baseEnd_2159058] using wordTrace_append hprefix tailTrace_2159058
  have hstable : (prefixWord ++ tailWord_2159058).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2159058).length < 2 ^ (prefixWord ++ tailWord_2159058).sum := by decide
  have hdescent : baseEnd_2159058 < baseStart_2159058 := by decide
  rcases family_descends (prefixWord ++ tailWord_2159058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2159065 : List Nat := [1, 2, 1, 2, 4, 1, 2, 1, 2, 6]
def baseStart_2159065 : Nat := 118140960795 + 2159065 * 2 ^ 59
def prefixEnd_2159065 : Nat := 4983230072969 + 3 ^ 40 * 2159065 * 2
def baseEnd_2159065 : Nat := 739092072866466921305431

theorem tailTrace_2159065 : CollatzResearch.WordTrace tailWord_2159065 prefixEnd_2159065 739092072866466921305431 := by
  unfold tailWord_2159065
  simp only [CollatzResearch.WordTrace]
  refine ⟨78747569923083718790302649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52498379948722479193535099 78747569923083718790302649)
  ·
    refine ⟨59060677442312789092726987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78747569923083718790302649 59060677442312789092726987)
    ·
      refine ⟨88591016163469183639090481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59060677442312789092726987 88591016163469183639090481)
      ·
        refine ⟨66443262122601887729317861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 88591016163469183639090481 66443262122601887729317861)
        ·
          refine ⟨12458111647987853949247099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 66443262122601887729317861 12458111647987853949247099)
          ·
            refine ⟨18687167471981780923870649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12458111647987853949247099 18687167471981780923870649)
            ·
              refine ⟨14015375603986335692902987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18687167471981780923870649 14015375603986335692902987)
              ·
                refine ⟨21023063405979503539354481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14015375603986335692902987 21023063405979503539354481)
                ·
                  refine ⟨15767297554484627654515861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21023063405979503539354481 15767297554484627654515861)
                  ·
                    refine ⟨739092072866466921305431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15767297554484627654515861 739092072866466921305431)
                    ·
                      rfl

theorem cell22_2159065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 2, 1, 2, 6].length) (baseStart_2159065 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2159065 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2159065 prefixEnd_2159065 := by exact prefixLift 2159065
  have htrace : WordTrace (prefixWord ++ tailWord_2159065) baseStart_2159065 baseEnd_2159065 := by
    simpa [prefixWord, tailWord_2159065, baseEnd_2159065] using wordTrace_append hprefix tailTrace_2159065
  have hstable : (prefixWord ++ tailWord_2159065).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2159065).length < 2 ^ (prefixWord ++ tailWord_2159065).sum := by decide
  have hdescent : baseEnd_2159065 < baseStart_2159065 := by decide
  rcases family_descends (prefixWord ++ tailWord_2159065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2159118 : List Nat := [4, 1, 1, 2, 3, 1, 4, 2, 1, 3]
def baseStart_2159118 : Nat := 118140960795 + 2159118 * 2 ^ 59
def prefixEnd_2159118 : Nat := 4983230072969 + 3 ^ 40 * 2159118 * 2
def baseEnd_2159118 : Nat := 739110215849592449730269

theorem tailTrace_2159118 : CollatzResearch.WordTrace tailWord_2159118 prefixEnd_2159118 739110215849592449730269 := by
  unfold tailWord_2159118
  simp only [CollatzResearch.WordTrace]
  refine ⟨9843687873986463605247751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 52499668661261139227988005 9843687873986463605247751)
  ·
    refine ⟨14765531810979695407871627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9843687873986463605247751 14765531810979695407871627)
    ·
      refine ⟨22148297716469543111807441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14765531810979695407871627 22148297716469543111807441)
      ·
        refine ⟨16611223287352157333855581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22148297716469543111807441 16611223287352157333855581)
        ·
          refine ⟨6229208732757059000195843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16611223287352157333855581 6229208732757059000195843)
          ·
            refine ⟨9343813099135588500293765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6229208732757059000195843 9343813099135588500293765)
            ·
              refine ⟨1751964956087922843805081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9343813099135588500293765 1751964956087922843805081)
              ·
                refine ⟨1313973717065942132853811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1751964956087922843805081 1313973717065942132853811)
                ·
                  refine ⟨1970960575598913199280717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1313973717065942132853811 1970960575598913199280717)
                  ·
                    refine ⟨739110215849592449730269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1970960575598913199280717 739110215849592449730269)
                    ·
                      rfl

theorem cell22_2159118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 4, 2, 1, 3].length) (baseStart_2159118 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2159118 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2159118 prefixEnd_2159118 := by exact prefixLift 2159118
  have htrace : WordTrace (prefixWord ++ tailWord_2159118) baseStart_2159118 baseEnd_2159118 := by
    simpa [prefixWord, tailWord_2159118, baseEnd_2159118] using wordTrace_append hprefix tailTrace_2159118
  have hstable : (prefixWord ++ tailWord_2159118).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2159118).length < 2 ^ (prefixWord ++ tailWord_2159118).sum := by decide
  have hdescent : baseEnd_2159118 < baseStart_2159118 := by decide
  rcases family_descends (prefixWord ++ tailWord_2159118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2159144 : List Nat := [2, 1, 5, 2, 1, 1, 2, 1, 3, 4]
def baseStart_2159144 : Nat := 118140960795 + 2159144 * 2 ^ 59
def prefixEnd_2159144 : Nat := 4983230072969 + 3 ^ 40 * 2159144 * 2
def baseEnd_2159144 : Nat := 739119116180937048580189

theorem tailTrace_2159144 : CollatzResearch.WordTrace tailWord_2159144 prefixEnd_2159144 739119116180937048580189 := by
  unfold tailWord_2159144
  simp only [CollatzResearch.WordTrace]
  refine ⟨39375225644898757641214243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52500300859865010188285657 39375225644898757641214243)
  ·
    refine ⟨59062838467348136461821365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39375225644898757641214243 59062838467348136461821365)
    ·
      refine ⟨5537141106313887793295753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 59062838467348136461821365 5537141106313887793295753)
      ·
        refine ⟨4152855829735415844971815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5537141106313887793295753 4152855829735415844971815)
        ·
          refine ⟨6229283744603123767457723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4152855829735415844971815 6229283744603123767457723)
          ·
            refine ⟨9343925616904685651186585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6229283744603123767457723 9343925616904685651186585)
            ·
              refine ⟨7007944212678514238389939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9343925616904685651186585 7007944212678514238389939)
              ·
                refine ⟨10511916319017771357584909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7007944212678514238389939 10511916319017771357584909)
                ·
                  refine ⟨3941968619631664259094341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10511916319017771357584909 3941968619631664259094341)
                  ·
                    refine ⟨739119116180937048580189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3941968619631664259094341 739119116180937048580189)
                    ·
                      rfl

theorem cell22_2159144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 2, 1, 3, 4].length) (baseStart_2159144 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2159144 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2159144 prefixEnd_2159144 := by exact prefixLift 2159144
  have htrace : WordTrace (prefixWord ++ tailWord_2159144) baseStart_2159144 baseEnd_2159144 := by
    simpa [prefixWord, tailWord_2159144, baseEnd_2159144] using wordTrace_append hprefix tailTrace_2159144
  have hstable : (prefixWord ++ tailWord_2159144).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2159144).length < 2 ^ (prefixWord ++ tailWord_2159144).sum := by decide
  have hdescent : baseEnd_2159144 < baseStart_2159144 := by decide
  rcases family_descends (prefixWord ++ tailWord_2159144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2159157 : List Nat := [1, 3, 3, 1, 1, 2, 1, 4, 1, 5]
def baseStart_2159157 : Nat := 118140960795 + 2159157 * 2 ^ 59
def prefixEnd_2159157 : Nat := 4983230072969 + 3 ^ 40 * 2159157 * 2
def baseEnd_2159157 : Nat := 739123566346609348005149

theorem tailTrace_2159157 : CollatzResearch.WordTrace tailWord_2159157 prefixEnd_2159157 739123566346609348005149 := by
  unfold tailWord_2159157
  simp only [CollatzResearch.WordTrace]
  refine ⟨78750925438750418502651725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52500616959166945668434483 78750925438750418502651725)
  ·
    refine ⟨29531597039531406938494397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 78750925438750418502651725 29531597039531406938494397)
    ·
      refine ⟨11074348889824277601935399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29531597039531406938494397 11074348889824277601935399)
      ·
        refine ⟨16611523334736416402903099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11074348889824277601935399 16611523334736416402903099)
        ·
          refine ⟨24917285002104624604354649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16611523334736416402903099 24917285002104624604354649)
          ·
            refine ⟨18687963751578468453265987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24917285002104624604354649 18687963751578468453265987)
            ·
              refine ⟨28031945627367702679898981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18687963751578468453265987 28031945627367702679898981)
              ·
                refine ⟨5255989805131444252481059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 28031945627367702679898981 5255989805131444252481059)
                ·
                  refine ⟨7883984707697166378721589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5255989805131444252481059 7883984707697166378721589)
                  ·
                    refine ⟨739123566346609348005149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7883984707697166378721589 739123566346609348005149)
                    ·
                      rfl

theorem cell22_2159157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 4, 1, 5].length) (baseStart_2159157 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2159157 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2159157 prefixEnd_2159157 := by exact prefixLift 2159157
  have htrace : WordTrace (prefixWord ++ tailWord_2159157) baseStart_2159157 baseEnd_2159157 := by
    simpa [prefixWord, tailWord_2159157, baseEnd_2159157] using wordTrace_append hprefix tailTrace_2159157
  have hstable : (prefixWord ++ tailWord_2159157).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2159157).length < 2 ^ (prefixWord ++ tailWord_2159157).sum := by decide
  have hdescent : baseEnd_2159157 < baseStart_2159157 := by decide
  rcases family_descends (prefixWord ++ tailWord_2159157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2159159 : List Nat := [1, 1, 3, 1, 2, 3, 4, 3, 4]
def baseStart_2159159 : Nat := 118140960795 + 2159159 * 2 ^ 59
def prefixEnd_2159159 : Nat := 4983230072969 + 3 ^ 40 * 2159159 * 2
def baseEnd_2159159 : Nat := 246374750329160669818381

theorem tailTrace_2159159 : CollatzResearch.WordTrace tailWord_2159159 prefixEnd_2159159 246374750329160669818381 := by
  unfold tailWord_2159159
  simp only [CollatzResearch.WordTrace]
  refine ⟨78750998384743172844224531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52500665589828781896149687 78750998384743172844224531)
  ·
    refine ⟨118126497577114759266336797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78750998384743172844224531 118126497577114759266336797)
    ·
      refine ⟨44297436591418034724876299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 118126497577114759266336797 44297436591418034724876299)
      ·
        refine ⟨66446154887127052087314449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44297436591418034724876299 66446154887127052087314449)
        ·
          refine ⟨49834616165345289065485837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66446154887127052087314449 49834616165345289065485837)
          ·
            refine ⟨18687981062004483399557189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 49834616165345289065485837 18687981062004483399557189)
            ·
              refine ⟨3503996449125840637416973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18687981062004483399557189 3503996449125840637416973)
              ·
                refine ⟨1313998668422190239031365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3503996449125840637416973 1313998668422190239031365)
                ·
                  refine ⟨246374750329160669818381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1313998668422190239031365 246374750329160669818381)
                  ·
                    rfl

theorem cell22_2159159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 4, 3, 4].length) (baseStart_2159159 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2159159 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2159159 prefixEnd_2159159 := by exact prefixLift 2159159
  have htrace : WordTrace (prefixWord ++ tailWord_2159159) baseStart_2159159 baseEnd_2159159 := by
    simpa [prefixWord, tailWord_2159159, baseEnd_2159159] using wordTrace_append hprefix tailTrace_2159159
  have hstable : (prefixWord ++ tailWord_2159159).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2159159).length < 2 ^ (prefixWord ++ tailWord_2159159).sum := by decide
  have hdescent : baseEnd_2159159 < baseStart_2159159 := by decide
  rcases family_descends (prefixWord ++ tailWord_2159159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2159191 : List Nat := [1, 1, 3, 2, 2, 2, 5, 1, 2, 3]
def baseStart_2159191 : Nat := 118140960795 + 2159191 * 2 ^ 59
def prefixEnd_2159191 : Nat := 4983230072969 + 3 ^ 40 * 2159191 * 2
def baseEnd_2159191 : Nat := 739135205241444592655045

theorem tailTrace_2159191 : CollatzResearch.WordTrace tailWord_2159191 prefixEnd_2159191 739135205241444592655045 := by
  unfold tailWord_2159191
  simp only [CollatzResearch.WordTrace]
  refine ⟨78752165520627242309389427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52501443680418161539592951 78752165520627242309389427)
  ·
    refine ⟨118128248280940863464084141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78752165520627242309389427 118128248280940863464084141)
    ·
      refine ⟨44298093105352823799031553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 118128248280940863464084141 44298093105352823799031553)
      ·
        refine ⟨33223569829014617849273665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44298093105352823799031553 33223569829014617849273665)
        ·
          refine ⟨24917677371760963386955249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33223569829014617849273665 24917677371760963386955249)
          ·
            refine ⟨18688258028820722540216437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24917677371760963386955249 18688258028820722540216437)
            ·
              refine ⟨1752024190201942738145291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 18688258028820722540216437 1752024190201942738145291)
              ·
                refine ⟨2628036285302914107217937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1752024190201942738145291 2628036285302914107217937)
                ·
                  refine ⟨1971027213977185580413453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2628036285302914107217937 1971027213977185580413453)
                  ·
                    refine ⟨739135205241444592655045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1971027213977185580413453 739135205241444592655045)
                    ·
                      rfl

theorem cell22_2159191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 5, 1, 2, 3].length) (baseStart_2159191 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2159191 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2159191 prefixEnd_2159191 := by exact prefixLift 2159191
  have htrace : WordTrace (prefixWord ++ tailWord_2159191) baseStart_2159191 baseEnd_2159191 := by
    simpa [prefixWord, tailWord_2159191, baseEnd_2159191] using wordTrace_append hprefix tailTrace_2159191
  have hstable : (prefixWord ++ tailWord_2159191).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2159191).length < 2 ^ (prefixWord ++ tailWord_2159191).sum := by decide
  have hdescent : baseEnd_2159191 < baseStart_2159191 := by decide
  rcases family_descends (prefixWord ++ tailWord_2159191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2159221 : List Nat := [1, 3, 4, 2, 3, 1, 8]
def baseStart_2159221 : Nat := 118140960795 + 2159221 * 2 ^ 59
def prefixEnd_2159221 : Nat := 4983230072969 + 3 ^ 40 * 2159221 * 2
def baseEnd_2159221 : Nat := 27375758327945722755739

theorem tailTrace_2159221 : CollatzResearch.WordTrace tailWord_2159221 prefixEnd_2159221 27375758327945722755739 := by
  unfold tailWord_2159221
  simp only [CollatzResearch.WordTrace]
  refine ⟨78753259710518557432981517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52502173140345704955321011 78753259710518557432981517)
  ·
    refine ⟨29532472391444459037368069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 78753259710518557432981517 29532472391444459037368069)
    ·
      refine ⟨5537338573395836069506513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 29532472391444459037368069 5537338573395836069506513)
      ·
        refine ⟨4153003930046877052129885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5537338573395836069506513 4153003930046877052129885)
        ·
          refine ⟨1557376473767578894548707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4153003930046877052129885 1557376473767578894548707)
          ·
            refine ⟨2336064710651368341823061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1557376473767578894548707 2336064710651368341823061)
            ·
              refine ⟨27375758327945722755739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2336064710651368341823061 27375758327945722755739)
              ·
                rfl

theorem cell22_2159221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 3, 1, 8].length) (baseStart_2159221 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2159221 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2159221 prefixEnd_2159221 := by exact prefixLift 2159221
  have htrace : WordTrace (prefixWord ++ tailWord_2159221) baseStart_2159221 baseEnd_2159221 := by
    simpa [prefixWord, tailWord_2159221, baseEnd_2159221] using wordTrace_append hprefix tailTrace_2159221
  have hstable : (prefixWord ++ tailWord_2159221).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2159221).length < 2 ^ (prefixWord ++ tailWord_2159221).sum := by decide
  have hdescent : baseEnd_2159221 < baseStart_2159221 := by decide
  rcases family_descends (prefixWord ++ tailWord_2159221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2159232 : List Nat := [2, 1, 1, 2, 1, 5, 2, 1, 7]
def baseStart_2159232 : Nat := 118140960795 + 2159232 * 2 ^ 59
def prefixEnd_2159232 : Nat := 4983230072969 + 3 ^ 40 * 2159232 * 2
def baseEnd_2159232 : Nat := 246383080126444717459973

theorem tailTrace_2159232 : CollatzResearch.WordTrace tailWord_2159232 prefixEnd_2159232 246383080126444717459973 := by
  unfold tailWord_2159232
  simp only [CollatzResearch.WordTrace]
  refine ⟨39376830456739353155815975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52502440608985804207754633 39376830456739353155815975)
  ·
    refine ⟨59065245685109029733723963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39376830456739353155815975 59065245685109029733723963)
    ·
      refine ⟨88597868527663544600585945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59065245685109029733723963 88597868527663544600585945)
      ·
        refine ⟨66448401395747658450439459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 88597868527663544600585945 66448401395747658450439459)
        ·
          refine ⟨99672602093621487675659189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66448401395747658450439459 99672602093621487675659189)
          ·
            refine ⟨9344306446277014469593049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 99672602093621487675659189 9344306446277014469593049)
            ·
              refine ⟨7008229834707760852194787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9344306446277014469593049 7008229834707760852194787)
              ·
                refine ⟨10512344752061641278292181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7008229834707760852194787 10512344752061641278292181)
                ·
                  refine ⟨246383080126444717459973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10512344752061641278292181 246383080126444717459973)
                  ·
                    rfl

theorem cell22_2159232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 2, 1, 7].length) (baseStart_2159232 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2159232 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2159232 prefixEnd_2159232 := by exact prefixLift 2159232
  have htrace : WordTrace (prefixWord ++ tailWord_2159232) baseStart_2159232 baseEnd_2159232 := by
    simpa [prefixWord, tailWord_2159232, baseEnd_2159232] using wordTrace_append hprefix tailTrace_2159232
  have hstable : (prefixWord ++ tailWord_2159232).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2159232).length < 2 ^ (prefixWord ++ tailWord_2159232).sum := by decide
  have hdescent : baseEnd_2159232 < baseStart_2159232 := by decide
  rcases family_descends (prefixWord ++ tailWord_2159232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2159236 : List Nat := [2, 3, 2, 1, 3, 1, 3, 1, 3, 3]
def baseStart_2159236 : Nat := 118140960795 + 2159236 * 2 ^ 59
def prefixEnd_2159236 : Nat := 4983230072969 + 3 ^ 40 * 2159236 * 2
def baseEnd_2159236 : Nat := 739150609661079475279907

theorem tailTrace_2159236 : CollatzResearch.WordTrace tailWord_2159236 prefixEnd_2159236 739150609661079475279907 := by
  unfold tailWord_2159236
  simp only [CollatzResearch.WordTrace]
  refine ⟨39376903402732107497388781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52502537870309476663185041 39376903402732107497388781)
  ·
    refine ⟨14766338776024540311520793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39376903402732107497388781 14766338776024540311520793)
    ·
      refine ⟨11074754082018405233640595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14766338776024540311520793 11074754082018405233640595)
      ·
        refine ⟨16612131123027607850460893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11074754082018405233640595 16612131123027607850460893)
        ·
          refine ⟨6229549171135352943922835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16612131123027607850460893 6229549171135352943922835)
          ·
            refine ⟨9344323756703029415884253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6229549171135352943922835 9344323756703029415884253)
            ·
              refine ⟨3504121408763636030956595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9344323756703029415884253 3504121408763636030956595)
              ·
                refine ⟨5256182113145454046434893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3504121408763636030956595 5256182113145454046434893)
                ·
                  refine ⟨1971068292429545267413085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5256182113145454046434893 1971068292429545267413085)
                  ·
                    refine ⟨739150609661079475279907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1971068292429545267413085 739150609661079475279907)
                    ·
                      rfl

theorem cell22_2159236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 3, 1, 3, 3].length) (baseStart_2159236 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2159236 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2159236 prefixEnd_2159236 := by exact prefixLift 2159236
  have htrace : WordTrace (prefixWord ++ tailWord_2159236) baseStart_2159236 baseEnd_2159236 := by
    simpa [prefixWord, tailWord_2159236, baseEnd_2159236] using wordTrace_append hprefix tailTrace_2159236
  have hstable : (prefixWord ++ tailWord_2159236).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2159236).length < 2 ^ (prefixWord ++ tailWord_2159236).sum := by decide
  have hdescent : baseEnd_2159236 < baseStart_2159236 := by decide
  rcases family_descends (prefixWord ++ tailWord_2159236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2159287 : List Nat := [1, 1, 3, 1, 7, 1, 2, 2, 1, 3]
def baseStart_2159287 : Nat := 118140960795 + 2159287 * 2 ^ 59
def prefixEnd_2159287 : Nat := 4983230072969 + 3 ^ 40 * 2159287 * 2
def baseEnd_2159287 : Nat := 739168068003332342254751

theorem tailTrace_2159287 : CollatzResearch.WordTrace tailWord_2159287 prefixEnd_2159287 739168068003332342254751 := by
  unfold tailWord_2159287
  simp only [CollatzResearch.WordTrace]
  refine ⟨78755666928279450704884115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52503777952186300469922743 78755666928279450704884115)
  ·
    refine ⟨118133500392419176057326173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78755666928279450704884115 118133500392419176057326173)
    ·
      refine ⟨44300062647157191021497315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 118133500392419176057326173 44300062647157191021497315)
      ·
        refine ⟨66450093970735786532245973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44300062647157191021497315 66450093970735786532245973)
        ·
          refine ⟨1557424077439119996849515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 66450093970735786532245973 1557424077439119996849515)
          ·
            refine ⟨2336136116158679995274273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1557424077439119996849515 2336136116158679995274273)
            ·
              refine ⟨1752102087119009996455705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2336136116158679995274273 1752102087119009996455705)
              ·
                refine ⟨1314076565339257497341779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1752102087119009996455705 1314076565339257497341779)
                ·
                  refine ⟨1971114848008886246012669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1314076565339257497341779 1971114848008886246012669)
                  ·
                    refine ⟨739168068003332342254751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1971114848008886246012669 739168068003332342254751)
                    ·
                      rfl

theorem cell22_2159287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 7, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 7, 1, 2, 2, 1, 3].length) (baseStart_2159287 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2159287 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2159287 prefixEnd_2159287 := by exact prefixLift 2159287
  have htrace : WordTrace (prefixWord ++ tailWord_2159287) baseStart_2159287 baseEnd_2159287 := by
    simpa [prefixWord, tailWord_2159287, baseEnd_2159287] using wordTrace_append hprefix tailTrace_2159287
  have hstable : (prefixWord ++ tailWord_2159287).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2159287).length < 2 ^ (prefixWord ++ tailWord_2159287).sum := by decide
  have hdescent : baseEnd_2159287 < baseStart_2159287 := by decide
  rcases family_descends (prefixWord ++ tailWord_2159287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2159294 : List Nat := [4, 2, 1, 1, 2, 1, 2, 3, 6]
def baseStart_2159294 : Nat := 118140960795 + 2159294 * 2 ^ 59
def prefixEnd_2159294 : Nat := 4983230072969 + 3 ^ 40 * 2159294 * 2
def baseEnd_2159294 : Nat := 246390154748795552443243

theorem tailTrace_2159294 : CollatzResearch.WordTrace tailWord_2159294 prefixEnd_2159294 246390154748795552443243 := by
  unfold tailWord_2159294
  simp only [CollatzResearch.WordTrace]
  refine ⟨9844490279906761362548617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 52503948159502727266925957 9844490279906761362548617)
  ·
    refine ⟨7383367709930071021911463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9844490279906761362548617 7383367709930071021911463)
    ·
      refine ⟨11075051564895106532867195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7383367709930071021911463 11075051564895106532867195)
      ·
        refine ⟨16612577347342659799300793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11075051564895106532867195 16612577347342659799300793)
        ·
          refine ⟨12459433010506994849475595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16612577347342659799300793 12459433010506994849475595)
          ·
            refine ⟨18689149515760492274213393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12459433010506994849475595 18689149515760492274213393)
            ·
              refine ⟨14016862136820369205660045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18689149515760492274213393 14016862136820369205660045)
              ·
                refine ⟨5256323301307638452122517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14016862136820369205660045 5256323301307638452122517)
                ·
                  refine ⟨246390154748795552443243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5256323301307638452122517 246390154748795552443243)
                  ·
                    rfl

theorem cell22_2159294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 2, 3, 6].length) (baseStart_2159294 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2159294 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2159294 prefixEnd_2159294 := by exact prefixLift 2159294
  have htrace : WordTrace (prefixWord ++ tailWord_2159294) baseStart_2159294 baseEnd_2159294 := by
    simpa [prefixWord, tailWord_2159294, baseEnd_2159294] using wordTrace_append hprefix tailTrace_2159294
  have hstable : (prefixWord ++ tailWord_2159294).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2159294).length < 2 ^ (prefixWord ++ tailWord_2159294).sum := by decide
  have hdescent : baseEnd_2159294 < baseStart_2159294 := by decide
  rcases family_descends (prefixWord ++ tailWord_2159294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2159343 : List Nat := [1, 1, 2, 1, 5, 4, 1, 2, 2, 3]
def baseStart_2159343 : Nat := 118140960795 + 2159343 * 2 ^ 59
def prefixEnd_2159343 : Nat := 4983230072969 + 3 ^ 40 * 2159343 * 2
def baseEnd_2159343 : Nat := 739187237947766862854579

theorem tailTrace_2159343 : CollatzResearch.WordTrace tailWord_2159343 prefixEnd_2159343 739187237947766862854579 := by
  unfold tailWord_2159343
  simp only [CollatzResearch.WordTrace]
  refine ⟨78757709416076572268922683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52505139610717714845948455 78757709416076572268922683)
  ·
    refine ⟨118136564124114858403384025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78757709416076572268922683 118136564124114858403384025)
    ·
      refine ⟨88602423093086143802538019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 118136564124114858403384025 88602423093086143802538019)
      ·
        refine ⟨132903634639629215703807029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88602423093086143802538019 132903634639629215703807029)
        ·
          refine ⟨12459715747465238972231909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 132903634639629215703807029 12459715747465238972231909)
          ·
            refine ⟨2336196702649732307293483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12459715747465238972231909 2336196702649732307293483)
            ·
              refine ⟨3504295053974598460940225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2336196702649732307293483 3504295053974598460940225)
              ·
                refine ⟨2628221290480948845705169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3504295053974598460940225 2628221290480948845705169)
                ·
                  refine ⟨1971165967860711634278877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2628221290480948845705169 1971165967860711634278877)
                  ·
                    refine ⟨739187237947766862854579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1971165967860711634278877 739187237947766862854579)
                    ·
                      rfl

theorem cell22_2159343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 4, 1, 2, 2, 3].length) (baseStart_2159343 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2159343 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2159343 prefixEnd_2159343 := by exact prefixLift 2159343
  have htrace : WordTrace (prefixWord ++ tailWord_2159343) baseStart_2159343 baseEnd_2159343 := by
    simpa [prefixWord, tailWord_2159343, baseEnd_2159343] using wordTrace_append hprefix tailTrace_2159343
  have hstable : (prefixWord ++ tailWord_2159343).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2159343).length < 2 ^ (prefixWord ++ tailWord_2159343).sum := by decide
  have hdescent : baseEnd_2159343 < baseStart_2159343 := by decide
  rcases family_descends (prefixWord ++ tailWord_2159343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2159461 : List Nat := [1, 3, 1, 3, 1, 1, 2, 3, 4, 3]
def baseStart_2159461 : Nat := 118140960795 + 2159461 * 2 ^ 59
def prefixEnd_2159461 : Nat := 4983230072969 + 3 ^ 40 * 2159461 * 2
def baseEnd_2159461 : Nat := 739227631759253888404217

theorem tailTrace_2159461 : CollatzResearch.WordTrace tailWord_2159461 prefixEnd_2159461 739227631759253888404217 := by
  unfold tailWord_2159461
  simp only [CollatzResearch.WordTrace]
  refine ⟨78762013229649078421718237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52508008819766052281145491 78762013229649078421718237)
  ·
    refine ⟨29535754961118404408144339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 78762013229649078421718237 29535754961118404408144339)
    ·
      refine ⟨44303632441677606612216509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29535754961118404408144339 44303632441677606612216509)
      ·
        refine ⟨16613862165629102479581191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44303632441677606612216509 16613862165629102479581191)
        ·
          refine ⟨24920793248443653719371787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16613862165629102479581191 24920793248443653719371787)
          ·
            refine ⟨37381189872665480579057681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24920793248443653719371787 37381189872665480579057681)
            ·
              refine ⟨28035892404499110434293261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37381189872665480579057681 28035892404499110434293261)
              ·
                refine ⟨10513459651687166412859973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28035892404499110434293261 10513459651687166412859973)
                ·
                  refine ⟨1971273684691343702411245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10513459651687166412859973 1971273684691343702411245)
                  ·
                    refine ⟨739227631759253888404217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1971273684691343702411245 739227631759253888404217)
                    ·
                      rfl

theorem cell22_2159461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 3, 4, 3].length) (baseStart_2159461 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2159461 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2159461 prefixEnd_2159461 := by exact prefixLift 2159461
  have htrace : WordTrace (prefixWord ++ tailWord_2159461) baseStart_2159461 baseEnd_2159461 := by
    simpa [prefixWord, tailWord_2159461, baseEnd_2159461] using wordTrace_append hprefix tailTrace_2159461
  have hstable : (prefixWord ++ tailWord_2159461).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2159461).length < 2 ^ (prefixWord ++ tailWord_2159461).sum := by decide
  have hdescent : baseEnd_2159461 < baseStart_2159461 := by decide
  rcases family_descends (prefixWord ++ tailWord_2159461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2159463 : List Nat := [1, 1, 5, 1, 2, 3, 1, 4, 4]
def baseStart_2159463 : Nat := 118140960795 + 2159463 * 2 ^ 59
def prefixEnd_2159463 : Nat := 4983230072969 + 3 ^ 40 * 2159463 * 2
def baseEnd_2159463 : Nat := 246409438800042183284737

theorem tailTrace_2159463 : CollatzResearch.WordTrace tailWord_2159463 prefixEnd_2159463 246409438800042183284737 := by
  unfold tailWord_2159463
  simp only [CollatzResearch.WordTrace]
  refine ⟨78762086175641832763291043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52508057450427888508860695 78762086175641832763291043)
  ·
    refine ⟨118143129263462749144936565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78762086175641832763291043 118143129263462749144936565)
    ·
      refine ⟨11075918368449632732337803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 118143129263462749144936565 11075918368449632732337803)
      ·
        refine ⟨16613877552674449098506705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11075918368449632732337803 16613877552674449098506705)
        ·
          refine ⟨12460408164505836823880029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16613877552674449098506705 12460408164505836823880029)
          ·
            refine ⟨4672653061689688808955011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12460408164505836823880029 4672653061689688808955011)
            ·
              refine ⟨7008979592534533213432517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4672653061689688808955011 7008979592534533213432517)
              ·
                refine ⟨1314183673600224977518597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7008979592534533213432517 1314183673600224977518597)
                ·
                  refine ⟨246409438800042183284737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1314183673600224977518597 246409438800042183284737)
                  ·
                    rfl

theorem cell22_2159463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 1, 4, 4].length) (baseStart_2159463 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2159463 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2159463 prefixEnd_2159463 := by exact prefixLift 2159463
  have htrace : WordTrace (prefixWord ++ tailWord_2159463) baseStart_2159463 baseEnd_2159463 := by
    simpa [prefixWord, tailWord_2159463, baseEnd_2159463] using wordTrace_append hprefix tailTrace_2159463
  have hstable : (prefixWord ++ tailWord_2159463).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2159463).length < 2 ^ (prefixWord ++ tailWord_2159463).sum := by decide
  have hdescent : baseEnd_2159463 < baseStart_2159463 := by decide
  rcases family_descends (prefixWord ++ tailWord_2159463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2159478 : List Nat := [5, 1, 1, 3, 1, 1, 1, 3, 1, 5]
def baseStart_2159478 : Nat := 118140960795 + 2159478 * 2 ^ 59
def prefixEnd_2159478 : Nat := 4983230072969 + 3 ^ 40 * 2159478 * 2
def baseEnd_2159478 : Nat := 739233451206671510729165

theorem tailTrace_2159478 : CollatzResearch.WordTrace tailWord_2159478 prefixEnd_2159478 739233451206671510729165 := by
  unfold tailWord_2159478
  simp only [CollatzResearch.WordTrace]
  refine ⟨4922664579411718145317943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 52508422180391660216724725 4922664579411718145317943)
  ·
    refine ⟨7383996869117577217976915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4922664579411718145317943 7383996869117577217976915)
    ·
      refine ⟨11075995303676365826965373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7383996869117577217976915 11075995303676365826965373)
      ·
        refine ⟨4153498238878637185112015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11075995303676365826965373 4153498238878637185112015)
        ·
          refine ⟨6230247358317955777668023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4153498238878637185112015 6230247358317955777668023)
          ·
            refine ⟨9345371037476933666502035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6230247358317955777668023 9345371037476933666502035)
            ·
              refine ⟨14018056556215400499753053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9345371037476933666502035 14018056556215400499753053)
              ·
                refine ⟨5256771208580775187407395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14018056556215400499753053 5256771208580775187407395)
                ·
                  refine ⟨7885156812871162781111093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5256771208580775187407395 7885156812871162781111093)
                  ·
                    refine ⟨739233451206671510729165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7885156812871162781111093 739233451206671510729165)
                    ·
                      rfl

theorem cell22_2159478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 1, 3, 1, 5].length) (baseStart_2159478 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2159478 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2159478 prefixEnd_2159478 := by exact prefixLift 2159478
  have htrace : WordTrace (prefixWord ++ tailWord_2159478) baseStart_2159478 baseEnd_2159478 := by
    simpa [prefixWord, tailWord_2159478, baseEnd_2159478] using wordTrace_append hprefix tailTrace_2159478
  have hstable : (prefixWord ++ tailWord_2159478).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2159478).length < 2 ^ (prefixWord ++ tailWord_2159478).sum := by decide
  have hdescent : baseEnd_2159478 < baseStart_2159478 := by decide
  rcases family_descends (prefixWord ++ tailWord_2159478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2159491 : List Nat := [1, 1, 1, 3, 4, 1, 5, 6]
def baseStart_2159491 : Nat := 118140960795 + 2159491 * 2 ^ 59
def prefixEnd_2159491 : Nat := 4983230072969 + 3 ^ 40 * 2159491 * 2
def baseEnd_2159491 : Nat := 82137544596927090017125

theorem tailTrace_2159491 : CollatzResearch.WordTrace tailWord_2159491 prefixEnd_2159491 82137544596927090017125 := by
  unfold tailWord_2159491
  simp only [CollatzResearch.WordTrace]
  refine ⟨78763107419540393545310327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52508738279693595696873551 78763107419540393545310327)
  ·
    refine ⟨118144661129310590317965491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78763107419540393545310327 118144661129310590317965491)
    ·
      refine ⟨177216991693965885476948237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118144661129310590317965491 177216991693965885476948237)
      ·
        refine ⟨66456371885237207053855589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 177216991693965885476948237 66456371885237207053855589)
        ·
          refine ⟨12460569728481976322597923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 66456371885237207053855589 12460569728481976322597923)
          ·
            refine ⟨18690854592722964483896885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12460569728481976322597923 18690854592722964483896885)
            ·
              refine ⟨1752267618067777920365333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 18690854592722964483896885 1752267618067777920365333)
              ·
                refine ⟨82137544596927090017125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1752267618067777920365333 82137544596927090017125)
                ·
                  rfl

theorem cell22_2159491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 5, 6].length) (baseStart_2159491 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2159491 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2159491 prefixEnd_2159491 := by exact prefixLift 2159491
  have htrace : WordTrace (prefixWord ++ tailWord_2159491) baseStart_2159491 baseEnd_2159491 := by
    simpa [prefixWord, tailWord_2159491, baseEnd_2159491] using wordTrace_append hprefix tailTrace_2159491
  have hstable : (prefixWord ++ tailWord_2159491).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2159491).length < 2 ^ (prefixWord ++ tailWord_2159491).sum := by decide
  have hdescent : baseEnd_2159491 < baseStart_2159491 := by decide
  rcases family_descends (prefixWord ++ tailWord_2159491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2159493 : List Nat := [1, 3, 1, 1, 3, 5, 1, 1, 2, 4]
def baseStart_2159493 : Nat := 118140960795 + 2159493 * 2 ^ 59
def prefixEnd_2159493 : Nat := 4983230072969 + 3 ^ 40 * 2159493 * 2
def baseEnd_2159493 : Nat := 739238586013216471604119

theorem tailTrace_2159493 : CollatzResearch.WordTrace tailWord_2159493 prefixEnd_2159493 739238586013216471604119 := by
  unfold tailWord_2159493
  simp only [CollatzResearch.WordTrace]
  refine ⟨78763180365533147886883133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52508786910355431924588755 78763180365533147886883133)
  ·
    refine ⟨29536192637074930457581175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 78763180365533147886883133 29536192637074930457581175)
    ·
      refine ⟨44304288955612395686371763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29536192637074930457581175 44304288955612395686371763)
      ·
        refine ⟨66456433433418593529557645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44304288955612395686371763 66456433433418593529557645)
        ·
          refine ⟨24921162537531972573584117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 66456433433418593529557645 24921162537531972573584117)
          ·
            refine ⟨2336358987893622428773511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 24921162537531972573584117 2336358987893622428773511)
            ·
              refine ⟨3504538481840433643160267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2336358987893622428773511 3504538481840433643160267)
              ·
                refine ⟨5256807722760650464740401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3504538481840433643160267 5256807722760650464740401)
                ·
                  refine ⟨3942605792070487848555301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5256807722760650464740401 3942605792070487848555301)
                  ·
                    refine ⟨739238586013216471604119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3942605792070487848555301 739238586013216471604119)
                    ·
                      rfl

theorem cell22_2159493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 5, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 5, 1, 1, 2, 4].length) (baseStart_2159493 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2159493 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2159493 prefixEnd_2159493 := by exact prefixLift 2159493
  have htrace : WordTrace (prefixWord ++ tailWord_2159493) baseStart_2159493 baseEnd_2159493 := by
    simpa [prefixWord, tailWord_2159493, baseEnd_2159493] using wordTrace_append hprefix tailTrace_2159493
  have hstable : (prefixWord ++ tailWord_2159493).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2159493).length < 2 ^ (prefixWord ++ tailWord_2159493).sum := by decide
  have hdescent : baseEnd_2159493 < baseStart_2159493 := by decide
  rcases family_descends (prefixWord ++ tailWord_2159493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2159542 : List Nat := [5, 1, 4, 1, 1, 1, 1, 8]
def baseStart_2159542 : Nat := 118140960795 + 2159542 * 2 ^ 59
def prefixEnd_2159542 : Nat := 4983230072969 + 3 ^ 40 * 2159542 * 2
def baseEnd_2159542 : Nat := 82139484412732964125441

theorem tailTrace_2159542 : CollatzResearch.WordTrace tailWord_2159542 prefixEnd_2159542 82139484412732964125441 := by
  unfold tailWord_2159542
  simp only [CollatzResearch.WordTrace]
  refine ⟨4922810471397226828463555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 52509978361570419503611253 4922810471397226828463555)
  ·
    refine ⟨7384215707095840242695333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4922810471397226828463555 7384215707095840242695333)
    ·
      refine ⟨1384540445080470045505375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7384215707095840242695333 1384540445080470045505375)
      ·
        refine ⟨2076810667620705068258063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1384540445080470045505375 2076810667620705068258063)
        ·
          refine ⟨3115216001431057602387095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2076810667620705068258063 3115216001431057602387095)
          ·
            refine ⟨4672824002146586403580643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3115216001431057602387095 4672824002146586403580643)
            ·
              refine ⟨7009236003219879605370965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4672824002146586403580643 7009236003219879605370965)
              ·
                refine ⟨82139484412732964125441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7009236003219879605370965 82139484412732964125441)
                ·
                  rfl

theorem cell22_2159542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 1, 8].length) (baseStart_2159542 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2159542 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2159542 prefixEnd_2159542 := by exact prefixLift 2159542
  have htrace : WordTrace (prefixWord ++ tailWord_2159542) baseStart_2159542 baseEnd_2159542 := by
    simpa [prefixWord, tailWord_2159542, baseEnd_2159542] using wordTrace_append hprefix tailTrace_2159542
  have hstable : (prefixWord ++ tailWord_2159542).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2159542).length < 2 ^ (prefixWord ++ tailWord_2159542).sum := by decide
  have hdescent : baseEnd_2159542 < baseStart_2159542 := by decide
  rcases family_descends (prefixWord ++ tailWord_2159542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2159626 : List Nat := [3, 1, 2, 2, 3, 11]
def baseStart_2159626 : Nat := 118140960795 + 2159626 * 2 ^ 59
def prefixEnd_2159626 : Nat := 4983230072969 + 3 ^ 40 * 2159626 * 2
def baseEnd_2159626 : Nat := 9126964378163561210231

theorem tailTrace_2159626 : CollatzResearch.WordTrace tailWord_2159626 prefixEnd_2159626 9126964378163561210231 := by
  unfold tailWord_2159626
  simp only [CollatzResearch.WordTrace]
  refine ⟨19692007818512827900368683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52512020849367541067649821 19692007818512827900368683)
  ·
    refine ⟨29538011727769241850553025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19692007818512827900368683 29538011727769241850553025)
    ·
      refine ⟨22153508795826931387914769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29538011727769241850553025 22153508795826931387914769)
      ·
        refine ⟨16615131596870198540936077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22153508795826931387914769 16615131596870198540936077)
        ·
          refine ⟨6230674348826324452851029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16615131596870198540936077 6230674348826324452851029)
          ·
            refine ⟨9126964378163561210231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 6230674348826324452851029 9126964378163561210231)
            ·
              rfl

theorem cell22_2159626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 11].length) (baseStart_2159626 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2159626 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2159626 prefixEnd_2159626 := by exact prefixLift 2159626
  have htrace : WordTrace (prefixWord ++ tailWord_2159626) baseStart_2159626 baseEnd_2159626 := by
    simpa [prefixWord, tailWord_2159626, baseEnd_2159626] using wordTrace_append hprefix tailTrace_2159626
  have hstable : (prefixWord ++ tailWord_2159626).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2159626).length < 2 ^ (prefixWord ++ tailWord_2159626).sum := by decide
  have hdescent : baseEnd_2159626 < baseStart_2159626 := by decide
  rcases family_descends (prefixWord ++ tailWord_2159626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2159628 : List Nat := [2, 2, 1, 2, 3, 2, 2, 2, 2, 4]
def baseStart_2159628 : Nat := 118140960795 + 2159628 * 2 ^ 59
def prefixEnd_2159628 : Nat := 4983230072969 + 3 ^ 40 * 2159628 * 2
def baseEnd_2159628 : Nat := 739284799272121119478705

theorem tailTrace_2159628 : CollatzResearch.WordTrace tailWord_2159628 prefixEnd_2159628 739284799272121119478705 := by
  unfold tailWord_2159628
  simp only [CollatzResearch.WordTrace]
  refine ⟨39384052110022032971523769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52512069480029377295365025 39384052110022032971523769)
  ·
    refine ⟨29538039082516524728642827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39384052110022032971523769 29538039082516524728642827)
    ·
      refine ⟨44307058623774787092964241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29538039082516524728642827 44307058623774787092964241)
      ·
        refine ⟨33230293967831090319723181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44307058623774787092964241 33230293967831090319723181)
        ·
          refine ⟨12461360237936658869896193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33230293967831090319723181 12461360237936658869896193)
          ·
            refine ⟨9346020178452494152422145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12461360237936658869896193 9346020178452494152422145)
            ·
              refine ⟨7009515133839370614316609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9346020178452494152422145 7009515133839370614316609)
              ·
                refine ⟨5257136350379527960737457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7009515133839370614316609 5257136350379527960737457)
                ·
                  refine ⟨3942852262784645970553093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5257136350379527960737457 3942852262784645970553093)
                  ·
                    refine ⟨739284799272121119478705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3942852262784645970553093 739284799272121119478705)
                    ·
                      rfl

theorem cell22_2159628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 2, 2, 2, 4].length) (baseStart_2159628 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2159628 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2159628 prefixEnd_2159628 := by exact prefixLift 2159628
  have htrace : WordTrace (prefixWord ++ tailWord_2159628) baseStart_2159628 baseEnd_2159628 := by
    simpa [prefixWord, tailWord_2159628, baseEnd_2159628] using wordTrace_append hprefix tailTrace_2159628
  have hstable : (prefixWord ++ tailWord_2159628).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2159628).length < 2 ^ (prefixWord ++ tailWord_2159628).sum := by decide
  have hdescent : baseEnd_2159628 < baseStart_2159628 := by decide
  rcases family_descends (prefixWord ++ tailWord_2159628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2159630 : List Nat := [4, 1, 1, 2, 2, 2, 1, 4, 2, 3]
def baseStart_2159630 : Nat := 118140960795 + 2159630 * 2 ^ 59
def prefixEnd_2159630 : Nat := 4983230072969 + 3 ^ 40 * 2159630 * 2
def baseEnd_2159630 : Nat := 739285483912993780928699

theorem tailTrace_2159630 : CollatzResearch.WordTrace tailWord_2159630 prefixEnd_2159630 739285483912993780928699 := by
  unfold tailWord_2159630
  simp only [CollatzResearch.WordTrace]
  refine ⟨9846022145754602535577543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 52512118110691213523080229 9846022145754602535577543)
  ·
    refine ⟨14769033218631903803366315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9846022145754602535577543 14769033218631903803366315)
    ·
      refine ⟨22153549827947855705049473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14769033218631903803366315 22153549827947855705049473)
      ·
        refine ⟨16615162370960891778787105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22153549827947855705049473 16615162370960891778787105)
        ·
          refine ⟨12461371778220668834090329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16615162370960891778787105 12461371778220668834090329)
          ·
            refine ⟨9346028833665501625567747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12461371778220668834090329 9346028833665501625567747)
            ·
              refine ⟨14019043250498252438351621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9346028833665501625567747 14019043250498252438351621)
              ·
                refine ⟨2628570609468422332190929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14019043250498252438351621 2628570609468422332190929)
                ·
                  refine ⟨1971427957101316749143197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2628570609468422332190929 1971427957101316749143197)
                  ·
                    refine ⟨739285483912993780928699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1971427957101316749143197 739285483912993780928699)
                    ·
                      rfl

theorem cell22_2159630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 1, 4, 2, 3].length) (baseStart_2159630 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2159630 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2159630 prefixEnd_2159630 := by exact prefixLift 2159630
  have htrace : WordTrace (prefixWord ++ tailWord_2159630) baseStart_2159630 baseEnd_2159630 := by
    simpa [prefixWord, tailWord_2159630, baseEnd_2159630] using wordTrace_append hprefix tailTrace_2159630
  have hstable : (prefixWord ++ tailWord_2159630).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2159630).length < 2 ^ (prefixWord ++ tailWord_2159630).sum := by decide
  have hdescent : baseEnd_2159630 < baseStart_2159630 := by decide
  rcases family_descends (prefixWord ++ tailWord_2159630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2159671 : List Nat := [1, 1, 3, 1, 2, 2, 1, 4, 7]
def baseStart_2159671 : Nat := 118140960795 + 2159671 * 2 ^ 59
def prefixEnd_2159671 : Nat := 4983230072969 + 3 ^ 40 * 2159671 * 2
def baseEnd_2159671 : Nat := 246433173016961113551191

theorem tailTrace_2159671 : CollatzResearch.WordTrace tailWord_2159671 prefixEnd_2159671 246433173016961113551191 := by
  unfold tailWord_2159671
  simp only [CollatzResearch.WordTrace]
  refine ⟨78769672558888284286862867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52513115039258856191241911 78769672558888284286862867)
  ·
    refine ⟨118154508838332426430294301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78769672558888284286862867 118154508838332426430294301)
    ·
      refine ⟨44307940814374659911360363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 118154508838332426430294301 44307940814374659911360363)
      ·
        refine ⟨66461911221561989867040545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44307940814374659911360363 66461911221561989867040545)
        ·
          refine ⟨49846433416171492400280409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66461911221561989867040545 49846433416171492400280409)
          ·
            refine ⟨37384825062128619300210307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49846433416171492400280409 37384825062128619300210307)
            ·
              refine ⟨56077237593192928950315461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37384825062128619300210307 56077237593192928950315461)
              ·
                refine ⟨10514482048723674178184149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 56077237593192928950315461 10514482048723674178184149)
                ·
                  refine ⟨246433173016961113551191, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10514482048723674178184149 246433173016961113551191)
                  ·
                    rfl

theorem cell22_2159671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 4, 7].length) (baseStart_2159671 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2159671 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2159671 prefixEnd_2159671 := by exact prefixLift 2159671
  have htrace : WordTrace (prefixWord ++ tailWord_2159671) baseStart_2159671 baseEnd_2159671 := by
    simpa [prefixWord, tailWord_2159671, baseEnd_2159671] using wordTrace_append hprefix tailTrace_2159671
  have hstable : (prefixWord ++ tailWord_2159671).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2159671).length < 2 ^ (prefixWord ++ tailWord_2159671).sum := by decide
  have hdescent : baseEnd_2159671 < baseStart_2159671 := by decide
  rcases family_descends (prefixWord ++ tailWord_2159671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2159780 : List Nat := [2, 3, 1, 2, 3, 1, 1, 3, 2, 4]
def baseStart_2159780 : Nat := 118140960795 + 2159780 * 2 ^ 59
def prefixEnd_2159780 : Nat := 4983230072969 + 3 ^ 40 * 2159780 * 2
def baseEnd_2159780 : Nat := 739336831978443389678239

theorem tailTrace_2159780 : CollatzResearch.WordTrace tailWord_2159780 prefixEnd_2159780 739336831978443389678239 := by
  unfold tailWord_2159780
  simp only [CollatzResearch.WordTrace]
  refine ⟨39386824057746697951290397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52515765410328930601720529 39386824057746697951290397)
  ·
    refine ⟨14770059021655011731733899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39386824057746697951290397 14770059021655011731733899)
    ·
      refine ⟨22155088532482517597600849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14770059021655011731733899 22155088532482517597600849)
      ·
        refine ⟨16616316399361888198200637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22155088532482517597600849 16616316399361888198200637)
        ·
          refine ⟨6231118649760708074325239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16616316399361888198200637 6231118649760708074325239)
          ·
            refine ⟨9346677974641062111487859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6231118649760708074325239 9346677974641062111487859)
            ·
              refine ⟨14020016961961593167231789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9346677974641062111487859 14020016961961593167231789)
              ·
                refine ⟨5257506360735597437711921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14020016961961593167231789 5257506360735597437711921)
                ·
                  refine ⟨3943129770551698078283941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5257506360735597437711921 3943129770551698078283941)
                  ·
                    refine ⟨739336831978443389678239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3943129770551698078283941 739336831978443389678239)
                    ·
                      rfl

theorem cell22_2159780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 1, 3, 2, 4].length) (baseStart_2159780 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2159780 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2159780 prefixEnd_2159780 := by exact prefixLift 2159780
  have htrace : WordTrace (prefixWord ++ tailWord_2159780) baseStart_2159780 baseEnd_2159780 := by
    simpa [prefixWord, tailWord_2159780, baseEnd_2159780] using wordTrace_append hprefix tailTrace_2159780
  have hstable : (prefixWord ++ tailWord_2159780).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2159780).length < 2 ^ (prefixWord ++ tailWord_2159780).sum := by decide
  have hdescent : baseEnd_2159780 < baseStart_2159780 := by decide
  rcases family_descends (prefixWord ++ tailWord_2159780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2159812 : List Nat := [2, 3, 3, 1, 3, 2, 1, 7]
def baseStart_2159812 : Nat := 118140960795 + 2159812 * 2 ^ 59
def prefixEnd_2159812 : Nat := 4983230072969 + 3 ^ 40 * 2159812 * 2
def baseEnd_2159812 : Nat := 82149754025822885875349

theorem tailTrace_2159812 : CollatzResearch.WordTrace tailWord_2159812 prefixEnd_2159812 82149754025822885875349 := by
  unfold tailWord_2159812
  simp only [CollatzResearch.WordTrace]
  refine ⟨39387407625688732683872845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52516543500918310245163793 39387407625688732683872845)
  ·
    refine ⟨14770277859633274756452317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39387407625688732683872845 14770277859633274756452317)
    ·
      refine ⟨5538854197362478033669619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14770277859633274756452317 5538854197362478033669619)
      ·
        refine ⟨8308281296043717050504429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5538854197362478033669619 8308281296043717050504429)
        ·
          refine ⟨3115605486016393893939161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8308281296043717050504429 3115605486016393893939161)
          ·
            refine ⟨2336704114512295420454371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3115605486016393893939161 2336704114512295420454371)
            ·
              refine ⟨3505056171768443130681557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2336704114512295420454371 3505056171768443130681557)
              ·
                refine ⟨82149754025822885875349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3505056171768443130681557 82149754025822885875349)
                ·
                  rfl

theorem cell22_2159812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 2, 1, 7].length) (baseStart_2159812 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2159812 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2159812 prefixEnd_2159812 := by exact prefixLift 2159812
  have htrace : WordTrace (prefixWord ++ tailWord_2159812) baseStart_2159812 baseEnd_2159812 := by
    simpa [prefixWord, tailWord_2159812, baseEnd_2159812] using wordTrace_append hprefix tailTrace_2159812
  have hstable : (prefixWord ++ tailWord_2159812).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2159812).length < 2 ^ (prefixWord ++ tailWord_2159812).sum := by decide
  have hdescent : baseEnd_2159812 < baseStart_2159812 := by decide
  rcases family_descends (prefixWord ++ tailWord_2159812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2159900 : List Nat := [2, 2, 3, 1, 1, 1, 2, 4, 1, 5]
def baseStart_2159900 : Nat := 118140960795 + 2159900 * 2 ^ 59
def prefixEnd_2159900 : Nat := 4983230072969 + 3 ^ 40 * 2159900 * 2
def baseEnd_2159900 : Nat := 739377910430803076677871

theorem tailTrace_2159900 : CollatzResearch.WordTrace tailWord_2159900 prefixEnd_2159900 739377910430803076677871 := by
  unfold tailWord_2159900
  simp only [CollatzResearch.WordTrace]
  refine ⟨39389012437529328198474577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52518683250039104264632769 39389012437529328198474577)
  ·
    refine ⟨29541759328146996148855933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39389012437529328198474577 29541759328146996148855933)
    ·
      refine ⟨11078159748055123555820975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29541759328146996148855933 11078159748055123555820975)
      ·
        refine ⟨16617239622082685333731463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11078159748055123555820975 16617239622082685333731463)
        ·
          refine ⟨24925859433124028000597195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16617239622082685333731463 24925859433124028000597195)
          ·
            refine ⟨37388789149686042000895793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24925859433124028000597195 37388789149686042000895793)
            ·
              refine ⟨28041591862264531500671845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37388789149686042000895793 28041591862264531500671845)
              ·
                refine ⟨5257798474174599656375971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 28041591862264531500671845 5257798474174599656375971)
                ·
                  refine ⟨7886697711261899484563957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5257798474174599656375971 7886697711261899484563957)
                  ·
                    refine ⟨739377910430803076677871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7886697711261899484563957 739377910430803076677871)
                    ·
                      rfl

theorem cell22_2159900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 4, 1, 5].length) (baseStart_2159900 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2159900 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2159900 prefixEnd_2159900 := by exact prefixLift 2159900
  have htrace : WordTrace (prefixWord ++ tailWord_2159900) baseStart_2159900 baseEnd_2159900 := by
    simpa [prefixWord, tailWord_2159900, baseEnd_2159900] using wordTrace_append hprefix tailTrace_2159900
  have hstable : (prefixWord ++ tailWord_2159900).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2159900).length < 2 ^ (prefixWord ++ tailWord_2159900).sum := by decide
  have hdescent : baseEnd_2159900 < baseStart_2159900 := by decide
  rcases family_descends (prefixWord ++ tailWord_2159900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2159930 : List Nat := [3, 1, 1, 1, 4, 1, 4, 7]
def baseStart_2159930 : Nat := 118140960795 + 2159930 * 2 ^ 59
def prefixEnd_2159930 : Nat := 4983230072969 + 3 ^ 40 * 2159930 * 2
def baseEnd_2159930 : Nat := 82154242227099222047531

theorem tailTrace_2159930 : CollatzResearch.WordTrace tailWord_2159930 prefixEnd_2159930 82154242227099222047531 := by
  unfold tailWord_2159930
  simp only [CollatzResearch.WordTrace]
  refine ⟨19694779766237492880135311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52519412709966647680360829 19694779766237492880135311)
  ·
    refine ⟨29542169649356239320202967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19694779766237492880135311 29542169649356239320202967)
    ·
      refine ⟨44313254474034358980304451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29542169649356239320202967 44313254474034358980304451)
      ·
        refine ⟨66469881711051538470456677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44313254474034358980304451 66469881711051538470456677)
        ·
          refine ⟨12463102820822163463210627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 66469881711051538470456677 12463102820822163463210627)
          ·
            refine ⟨18694654231233245194815941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12463102820822163463210627 18694654231233245194815941)
            ·
              refine ⟨3505247668356233474027989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18694654231233245194815941 3505247668356233474027989)
              ·
                refine ⟨82154242227099222047531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3505247668356233474027989 82154242227099222047531)
                ·
                  rfl

theorem cell22_2159930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 4, 7].length) (baseStart_2159930 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2159930 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2159930 prefixEnd_2159930 := by exact prefixLift 2159930
  have htrace : WordTrace (prefixWord ++ tailWord_2159930) baseStart_2159930 baseEnd_2159930 := by
    simpa [prefixWord, tailWord_2159930, baseEnd_2159930] using wordTrace_append hprefix tailTrace_2159930
  have hstable : (prefixWord ++ tailWord_2159930).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2159930).length < 2 ^ (prefixWord ++ tailWord_2159930).sum := by decide
  have hdescent : baseEnd_2159930 < baseStart_2159930 := by decide
  rcases family_descends (prefixWord ++ tailWord_2159930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2159934 : List Nat := [4, 2, 1, 2, 1, 1, 3, 3, 2, 3]
def baseStart_2159934 : Nat := 118140960795 + 2159934 * 2 ^ 59
def prefixEnd_2159934 : Nat := 4983230072969 + 3 ^ 40 * 2159934 * 2
def baseEnd_2159934 : Nat := 739389549325638321327767

theorem tailTrace_2159934 : CollatzResearch.WordTrace tailWord_2159934 prefixEnd_2159934 739389549325638321327767 := by
  unfold tailWord_2159934
  simp only [CollatzResearch.WordTrace]
  refine ⟨9847408119616935025460857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 52519509971290320135791237 9847408119616935025460857)
  ·
    refine ⟨7385556089712701269095643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9847408119616935025460857 7385556089712701269095643)
    ·
      refine ⟨11078334134569051903643465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7385556089712701269095643 11078334134569051903643465)
      ·
        refine ⟨8308750600926788927732599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11078334134569051903643465 8308750600926788927732599)
        ·
          refine ⟨12463125901390183391598899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8308750600926788927732599 12463125901390183391598899)
          ·
            refine ⟨18694688852085275087398349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12463125901390183391598899 18694688852085275087398349)
            ·
              refine ⟨7010508319531978157774381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18694688852085275087398349 7010508319531978157774381)
              ·
                refine ⟨2628940619824491809165393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7010508319531978157774381 2628940619824491809165393)
                ·
                  refine ⟨1971705464868368856874045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2628940619824491809165393 1971705464868368856874045)
                  ·
                    refine ⟨739389549325638321327767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1971705464868368856874045 739389549325638321327767)
                    ·
                      rfl

theorem cell22_2159934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 3, 3, 2, 3].length) (baseStart_2159934 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2159934 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2159934 prefixEnd_2159934 := by exact prefixLift 2159934
  have htrace : WordTrace (prefixWord ++ tailWord_2159934) baseStart_2159934 baseEnd_2159934 := by
    simpa [prefixWord, tailWord_2159934, baseEnd_2159934] using wordTrace_append hprefix tailTrace_2159934
  have hstable : (prefixWord ++ tailWord_2159934).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2159934).length < 2 ^ (prefixWord ++ tailWord_2159934).sum := by decide
  have hdescent : baseEnd_2159934 < baseStart_2159934 := by decide
  rcases family_descends (prefixWord ++ tailWord_2159934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2160080 : List Nat := [2, 1, 1, 1, 1, 2, 2, 2, 1, 9]
def baseStart_2160080 : Nat := 118140960795 + 2160080 * 2 ^ 59
def prefixEnd_2160080 : Nat := 4983230072969 + 3 ^ 40 * 2160080 * 2
def baseEnd_2160080 : Nat := 739439528109342607177319

theorem tailTrace_2160080 : CollatzResearch.WordTrace tailWord_2160080 prefixEnd_2160080 739439528109342607177319 := by
  unfold tailWord_2160080
  simp only [CollatzResearch.WordTrace]
  refine ⟨39392295007203273569250847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52523060009604364759001129 39392295007203273569250847)
  ·
    refine ⟨59088442510804910353876271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39392295007203273569250847 59088442510804910353876271)
    ·
      refine ⟨88632663766207365530814407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59088442510804910353876271 88632663766207365530814407)
      ·
        refine ⟨132948995649311048296221611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88632663766207365530814407 132948995649311048296221611)
        ·
          refine ⟨199423493473966572444332417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 132948995649311048296221611 199423493473966572444332417)
          ·
            refine ⟨149567620105474929333249313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 199423493473966572444332417 149567620105474929333249313)
            ·
              refine ⟨112175715079106196999936985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 149567620105474929333249313 112175715079106196999936985)
              ·
                refine ⟨84131786309329647749952739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 112175715079106196999936985 84131786309329647749952739)
                ·
                  refine ⟨126197679463994471624929109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 84131786309329647749952739 126197679463994471624929109)
                  ·
                    refine ⟨739439528109342607177319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 126197679463994471624929109 739439528109342607177319)
                    ·
                      rfl

theorem cell22_2160080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 2, 1, 9].length) (baseStart_2160080 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2160080 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2160080 prefixEnd_2160080 := by exact prefixLift 2160080
  have htrace : WordTrace (prefixWord ++ tailWord_2160080) baseStart_2160080 baseEnd_2160080 := by
    simpa [prefixWord, tailWord_2160080, baseEnd_2160080] using wordTrace_append hprefix tailTrace_2160080
  have hstable : (prefixWord ++ tailWord_2160080).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2160080).length < 2 ^ (prefixWord ++ tailWord_2160080).sum := by decide
  have hdescent : baseEnd_2160080 < baseStart_2160080 := by decide
  rcases family_descends (prefixWord ++ tailWord_2160080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2160086 : List Nat := [5, 2, 1, 1, 1, 2, 2, 1, 4, 3]
def baseStart_2160086 : Nat := 118140960795 + 2160086 * 2 ^ 59
def prefixEnd_2160086 : Nat := 4983230072969 + 3 ^ 40 * 2160086 * 2
def baseEnd_2160086 : Nat := 739441582031960591527301

theorem tailTrace_2160086 : CollatzResearch.WordTrace tailWord_2160086 prefixEnd_2160086 739441582031960591527301 := by
  unfold tailWord_2160086
  simp only [CollatzResearch.WordTrace]
  refine ⟨4924050553274050635201257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 52523205901589873442146741 4924050553274050635201257)
  ·
    refine ⟨3693037914955537976400943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4924050553274050635201257 3693037914955537976400943)
    ·
      refine ⟨5539556872433306964601415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3693037914955537976400943 5539556872433306964601415)
      ·
        refine ⟨8309335308649960446902123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5539556872433306964601415 8309335308649960446902123)
        ·
          refine ⟨12464002962974940670353185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8309335308649960446902123 12464002962974940670353185)
          ·
            refine ⟨9348002222231205502764889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12464002962974940670353185 9348002222231205502764889)
            ·
              refine ⟨7011001666673404127073667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9348002222231205502764889 7011001666673404127073667)
              ·
                refine ⟨10516502500010106190610501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7011001666673404127073667 10516502500010106190610501)
                ·
                  refine ⟨1971844218751894910739469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10516502500010106190610501 1971844218751894910739469)
                  ·
                    refine ⟨739441582031960591527301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1971844218751894910739469 739441582031960591527301)
                    ·
                      rfl

theorem cell22_2160086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 2, 1, 4, 3].length) (baseStart_2160086 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2160086 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2160086 prefixEnd_2160086 := by exact prefixLift 2160086
  have htrace : WordTrace (prefixWord ++ tailWord_2160086) baseStart_2160086 baseEnd_2160086 := by
    simpa [prefixWord, tailWord_2160086, baseEnd_2160086] using wordTrace_append hprefix tailTrace_2160086
  have hstable : (prefixWord ++ tailWord_2160086).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2160086).length < 2 ^ (prefixWord ++ tailWord_2160086).sum := by decide
  have hdescent : baseEnd_2160086 < baseStart_2160086 := by decide
  rcases family_descends (prefixWord ++ tailWord_2160086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2160103 : List Nat := [1, 1, 5, 2, 1, 4, 2, 1, 2, 3]
def baseStart_2160103 : Nat := 118140960795 + 2160103 * 2 ^ 59
def prefixEnd_2160103 : Nat := 4983230072969 + 3 ^ 40 * 2160103 * 2
def baseEnd_2160103 : Nat := 739447401479378213852249

theorem tailTrace_2160103 : CollatzResearch.WordTrace tailWord_2160103 prefixEnd_2160103 739447401479378213852249 := by
  unfold tailWord_2160103
  simp only [CollatzResearch.WordTrace]
  refine ⟨78785428893323222066588963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52523619262215481377725975 78785428893323222066588963)
  ·
    refine ⟨118178143339984833099883445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78785428893323222066588963 118178143339984833099883445)
    ·
      refine ⟨11079200938123578103114073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 118178143339984833099883445 11079200938123578103114073)
      ·
        refine ⟨8309400703592683577335555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11079200938123578103114073 8309400703592683577335555)
        ·
          refine ⟨12464101055389025366003333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8309400703592683577335555 12464101055389025366003333)
          ·
            refine ⟨2337018947885442256125625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12464101055389025366003333 2337018947885442256125625)
            ·
              refine ⟨1752764210914081692094219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2337018947885442256125625 1752764210914081692094219)
              ·
                refine ⟨2629146316371122538141329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1752764210914081692094219 2629146316371122538141329)
                ·
                  refine ⟨1971859737278341903605997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2629146316371122538141329 1971859737278341903605997)
                  ·
                    refine ⟨739447401479378213852249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1971859737278341903605997 739447401479378213852249)
                    ·
                      rfl

theorem cell22_2160103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 4, 2, 1, 2, 3].length) (baseStart_2160103 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2160103 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2160103 prefixEnd_2160103 := by exact prefixLift 2160103
  have htrace : WordTrace (prefixWord ++ tailWord_2160103) baseStart_2160103 baseEnd_2160103 := by
    simpa [prefixWord, tailWord_2160103, baseEnd_2160103] using wordTrace_append hprefix tailTrace_2160103
  have hstable : (prefixWord ++ tailWord_2160103).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2160103).length < 2 ^ (prefixWord ++ tailWord_2160103).sum := by decide
  have hdescent : baseEnd_2160103 < baseStart_2160103 := by decide
  rcases family_descends (prefixWord ++ tailWord_2160103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2160191 : List Nat := [1, 1, 2, 2, 3, 3, 4, 1, 1, 4]
def baseStart_2160191 : Nat := 118140960795 + 2160191 * 2 ^ 59
def prefixEnd_2160191 : Nat := 4983230072969 + 3 ^ 40 * 2160191 * 2
def baseEnd_2160191 : Nat := 739477525677775317651979

theorem tailTrace_2160191 : CollatzResearch.WordTrace tailWord_2160191 prefixEnd_2160191 739477525677775317651979 := by
  unfold tailWord_2160191
  simp only [CollatzResearch.WordTrace]
  refine ⟨78788638517004413095792427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52525759011336275397194951 78788638517004413095792427)
  ·
    refine ⟨118182957775506619643688641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78788638517004413095792427 118182957775506619643688641)
    ·
      refine ⟨88637218331629964732766481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 118182957775506619643688641 88637218331629964732766481)
      ·
        refine ⟨66477913748722473549574861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 88637218331629964732766481 66477913748722473549574861)
        ·
          refine ⟨24929217655770927581090573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 66477913748722473549574861 24929217655770927581090573)
          ·
            refine ⟨9348456620914097842908965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24929217655770927581090573 9348456620914097842908965)
            ·
              refine ⟨1752835616421393345545431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9348456620914097842908965 1752835616421393345545431)
              ·
                refine ⟨2629253424632090018318147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1752835616421393345545431 2629253424632090018318147)
                ·
                  refine ⟨3943880136948135027477221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2629253424632090018318147 3943880136948135027477221)
                  ·
                    refine ⟨739477525677775317651979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3943880136948135027477221 739477525677775317651979)
                    ·
                      rfl

theorem cell22_2160191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 4, 1, 1, 4].length) (baseStart_2160191 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2160191 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2160191 prefixEnd_2160191 := by exact prefixLift 2160191
  have htrace : WordTrace (prefixWord ++ tailWord_2160191) baseStart_2160191 baseEnd_2160191 := by
    simpa [prefixWord, tailWord_2160191, baseEnd_2160191] using wordTrace_append hprefix tailTrace_2160191
  have hstable : (prefixWord ++ tailWord_2160191).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2160191).length < 2 ^ (prefixWord ++ tailWord_2160191).sum := by decide
  have hdescent : baseEnd_2160191 < baseStart_2160191 := by decide
  rcases family_descends (prefixWord ++ tailWord_2160191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2160234 : List Nat := [3, 1, 3, 2, 1, 3, 1, 8]
def baseStart_2160234 : Nat := 118140960795 + 2160234 * 2 ^ 59
def prefixEnd_2160234 : Nat := 4983230072969 + 3 ^ 40 * 2160234 * 2
def baseEnd_2160234 : Nat := 82165805050726393202983

theorem tailTrace_2160234 : CollatzResearch.WordTrace tailWord_2160234 prefixEnd_2160234 82165805050726393202983 := by
  unfold tailWord_2160234
  simp only [CollatzResearch.WordTrace]
  refine ⟨19697551713962157859901939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52526804570565754293071837 19697551713962157859901939)
  ·
    refine ⟨29546327570943236789852909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19697551713962157859901939 29546327570943236789852909)
    ·
      refine ⟨11079872839103713796194841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29546327570943236789852909 11079872839103713796194841)
      ·
        refine ⟨8309904629327785347146131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11079872839103713796194841 8309904629327785347146131)
        ·
          refine ⟨12464856943991678020719197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8309904629327785347146131 12464856943991678020719197)
          ·
            refine ⟨4674321353996879257769699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12464856943991678020719197 4674321353996879257769699)
            ·
              refine ⟨7011482030995318886654549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4674321353996879257769699 7011482030995318886654549)
              ·
                refine ⟨82165805050726393202983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7011482030995318886654549 82165805050726393202983)
                ·
                  rfl

theorem cell22_2160234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 1, 8].length) (baseStart_2160234 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2160234 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2160234 prefixEnd_2160234 := by exact prefixLift 2160234
  have htrace : WordTrace (prefixWord ++ tailWord_2160234) baseStart_2160234 baseEnd_2160234 := by
    simpa [prefixWord, tailWord_2160234, baseEnd_2160234] using wordTrace_append hprefix tailTrace_2160234
  have hstable : (prefixWord ++ tailWord_2160234).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2160234).length < 2 ^ (prefixWord ++ tailWord_2160234).sum := by decide
  have hdescent : baseEnd_2160234 < baseStart_2160234 := by decide
  rcases family_descends (prefixWord ++ tailWord_2160234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2160247 : List Nat := [1, 1, 3, 1, 1, 3, 1, 2, 1, 8]
def baseStart_2160247 : Nat := 118140960795 + 2160247 * 2 ^ 59
def prefixEnd_2160247 : Nat := 4983230072969 + 3 ^ 40 * 2160247 * 2
def baseEnd_2160247 : Nat := 739496695622209838251807

theorem tailTrace_2160247 : CollatzResearch.WordTrace tailWord_2160247 prefixEnd_2160247 739496695622209838251807 := by
  unfold tailWord_2160247
  simp only [CollatzResearch.WordTrace]
  refine ⟨78790681004801534659830995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52527120669867689773220663 78790681004801534659830995)
  ·
    refine ⟨118186021507202301989746493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78790681004801534659830995 118186021507202301989746493)
    ·
      refine ⟨44319758065200863246154935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 118186021507202301989746493 44319758065200863246154935)
      ·
        refine ⟨66479637097801294869232403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44319758065200863246154935 66479637097801294869232403)
        ·
          refine ⟨99719455646701942303848605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66479637097801294869232403 99719455646701942303848605)
          ·
            refine ⟨37394795867513228363943227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 99719455646701942303848605 37394795867513228363943227)
            ·
              refine ⟨56092193801269842545914841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37394795867513228363943227 56092193801269842545914841)
              ·
                refine ⟨42069145350952381909436131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 56092193801269842545914841 42069145350952381909436131)
                ·
                  refine ⟨63103718026428572864154197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 42069145350952381909436131 63103718026428572864154197)
                  ·
                    refine ⟨739496695622209838251807, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 63103718026428572864154197 739496695622209838251807)
                    ·
                      rfl

theorem cell22_2160247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 2, 1, 8].length) (baseStart_2160247 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2160247 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2160247 prefixEnd_2160247 := by exact prefixLift 2160247
  have htrace : WordTrace (prefixWord ++ tailWord_2160247) baseStart_2160247 baseEnd_2160247 := by
    simpa [prefixWord, tailWord_2160247, baseEnd_2160247] using wordTrace_append hprefix tailTrace_2160247
  have hstable : (prefixWord ++ tailWord_2160247).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2160247).length < 2 ^ (prefixWord ++ tailWord_2160247).sum := by decide
  have hdescent : baseEnd_2160247 < baseStart_2160247 := by decide
  rcases family_descends (prefixWord ++ tailWord_2160247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2160356 : List Nat := [2, 3, 1, 1, 1, 3, 2, 2, 4, 3]
def baseStart_2160356 : Nat := 118140960795 + 2160356 * 2 ^ 59
def prefixEnd_2160356 : Nat := 4983230072969 + 3 ^ 40 * 2160356 * 2
def baseEnd_2160356 : Nat := 739534008549769887276473

theorem tailTrace_2160356 : CollatzResearch.WordTrace tailWord_2160356 prefixEnd_2160356 739534008549769887276473 := by
  unfold tailWord_2160356
  simp only [CollatzResearch.WordTrace]
  refine ⟨39397328280703323137774461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52529771040937764183699281 39397328280703323137774461)
  ·
    refine ⟨14773998105263746176665423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39397328280703323137774461 14773998105263746176665423)
    ·
      refine ⟨22160997157895619264998135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14773998105263746176665423 22160997157895619264998135)
      ·
        refine ⟨33241495736843428897497203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22160997157895619264998135 33241495736843428897497203)
        ·
          refine ⟨49862243605265143346245805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33241495736843428897497203 49862243605265143346245805)
          ·
            refine ⟨18698341351974428754842177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 49862243605265143346245805 18698341351974428754842177)
            ·
              refine ⟨14023756013980821566131633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18698341351974428754842177 14023756013980821566131633)
              ·
                refine ⟨10517817010485616174598725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14023756013980821566131633 10517817010485616174598725)
                ·
                  refine ⟨1972090689466053032737261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10517817010485616174598725 1972090689466053032737261)
                  ·
                    refine ⟨739534008549769887276473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1972090689466053032737261 739534008549769887276473)
                    ·
                      rfl

theorem cell22_2160356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 2, 2, 4, 3].length) (baseStart_2160356 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2160356 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2160356 prefixEnd_2160356 := by exact prefixLift 2160356
  have htrace : WordTrace (prefixWord ++ tailWord_2160356) baseStart_2160356 baseEnd_2160356 := by
    simpa [prefixWord, tailWord_2160356, baseEnd_2160356] using wordTrace_append hprefix tailTrace_2160356
  have hstable : (prefixWord ++ tailWord_2160356).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2160356).length < 2 ^ (prefixWord ++ tailWord_2160356).sum := by decide
  have hdescent : baseEnd_2160356 < baseStart_2160356 := by decide
  rcases family_descends (prefixWord ++ tailWord_2160356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2160360 : List Nat := [2, 1, 4, 1, 3, 3, 2, 1, 1, 4]
def baseStart_2160360 : Nat := 118140960795 + 2160360 * 2 ^ 59
def prefixEnd_2160360 : Nat := 4983230072969 + 3 ^ 40 * 2160360 * 2
def baseEnd_2160360 : Nat := 739535377831515210176461

theorem tailTrace_2160360 : CollatzResearch.WordTrace tailWord_2160360 prefixEnd_2160360 739535377831515210176461 := by
  unfold tailWord_2160360
  simp only [CollatzResearch.WordTrace]
  refine ⟨39397401226696077479347267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52529868302261436639129689 39397401226696077479347267)
  ·
    refine ⟨59096101840044116219020901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39397401226696077479347267 59096101840044116219020901)
    ·
      refine ⟨11080519095008271791066419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 59096101840044116219020901 11080519095008271791066419)
      ·
        refine ⟨16620778642512407686599629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11080519095008271791066419 16620778642512407686599629)
        ·
          refine ⟨6232791990942152882474861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16620778642512407686599629 6232791990942152882474861)
          ·
            refine ⟨2337296996603307330928073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6232791990942152882474861 2337296996603307330928073)
            ·
              refine ⟨1752972747452480498196055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2337296996603307330928073 1752972747452480498196055)
              ·
                refine ⟨2629459121178720747294083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1752972747452480498196055 2629459121178720747294083)
                ·
                  refine ⟨3944188681768081120941125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2629459121178720747294083 3944188681768081120941125)
                  ·
                    refine ⟨739535377831515210176461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3944188681768081120941125 739535377831515210176461)
                    ·
                      rfl

theorem cell22_2160360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 3, 2, 1, 1, 4].length) (baseStart_2160360 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2160360 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2160360 prefixEnd_2160360 := by exact prefixLift 2160360
  have htrace : WordTrace (prefixWord ++ tailWord_2160360) baseStart_2160360 baseEnd_2160360 := by
    simpa [prefixWord, tailWord_2160360, baseEnd_2160360] using wordTrace_append hprefix tailTrace_2160360
  have hstable : (prefixWord ++ tailWord_2160360).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2160360).length < 2 ^ (prefixWord ++ tailWord_2160360).sum := by decide
  have hdescent : baseEnd_2160360 < baseStart_2160360 := by decide
  rcases family_descends (prefixWord ++ tailWord_2160360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2160369 : List Nat := [1, 2, 2, 2, 2, 4, 9]
def baseStart_2160369 : Nat := 118140960795 + 2160369 * 2 ^ 59
def prefixEnd_2160369 : Nat := 4983230072969 + 3 ^ 40 * 2160369 * 2
def baseEnd_2160369 : Nat := 27390313285757118025979

theorem tailTrace_2160369 : CollatzResearch.WordTrace tailWord_2160369 prefixEnd_2160369 27390313285757118025979 := by
  unfold tailWord_2160369
  simp only [CollatzResearch.WordTrace]
  refine ⟨78795130710359549495772161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52530087140239699663848107 78795130710359549495772161)
  ·
    refine ⟨59096348032769662121829121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78795130710359549495772161 59096348032769662121829121)
    ·
      refine ⟨44322261024577246591371841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59096348032769662121829121 44322261024577246591371841)
      ·
        refine ⟨33241695768432934943528881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44322261024577246591371841 33241695768432934943528881)
        ·
          refine ⟨24931271826324701207646661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33241695768432934943528881 24931271826324701207646661)
          ·
            refine ⟨4674613467435881476433749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24931271826324701207646661 4674613467435881476433749)
            ·
              refine ⟨27390313285757118025979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4674613467435881476433749 27390313285757118025979)
              ·
                rfl

theorem cell22_2160369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 9].length) (baseStart_2160369 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2160369 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2160369 prefixEnd_2160369 := by exact prefixLift 2160369
  have htrace : WordTrace (prefixWord ++ tailWord_2160369) baseStart_2160369 baseEnd_2160369 := by
    simpa [prefixWord, tailWord_2160369, baseEnd_2160369] using wordTrace_append hprefix tailTrace_2160369
  have hstable : (prefixWord ++ tailWord_2160369).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2160369).length < 2 ^ (prefixWord ++ tailWord_2160369).sum := by decide
  have hdescent : baseEnd_2160369 < baseStart_2160369 := by decide
  rcases family_descends (prefixWord ++ tailWord_2160369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2160386 : List Nat := [3, 4, 1, 1, 1, 1, 2, 9]
def baseStart_2160386 : Nat := 118140960795 + 2160386 * 2 ^ 59
def prefixEnd_2160386 : Nat := 4983230072969 + 3 ^ 40 * 2160386 * 2
def baseEnd_2160386 : Nat := 82171586462539978780709

theorem tailTrace_2160386 : CollatzResearch.WordTrace tailWord_2160386 prefixEnd_2160386 82171586462539978780709 := by
  unfold tailWord_2160386
  simp only [CollatzResearch.WordTrace]
  refine ⟨19698937687824490349785253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52530500500865307599427341 19698937687824490349785253)
  ·
    refine ⟨3693550816467091940584735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19698937687824490349785253 3693550816467091940584735)
    ·
      refine ⟨5540326224700637910877103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3693550816467091940584735 5540326224700637910877103)
      ·
        refine ⟨8310489337050956866315655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5540326224700637910877103 8310489337050956866315655)
        ·
          refine ⟨12465734005576435299473483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8310489337050956866315655 12465734005576435299473483)
          ·
            refine ⟨18698601008364652949210225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12465734005576435299473483 18698601008364652949210225)
            ·
              refine ⟨14023950756273489711907669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18698601008364652949210225 14023950756273489711907669)
              ·
                refine ⟨82171586462539978780709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 14023950756273489711907669 82171586462539978780709)
                ·
                  rfl

theorem cell22_2160386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 2, 9].length) (baseStart_2160386 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2160386 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2160386 prefixEnd_2160386 := by exact prefixLift 2160386
  have htrace : WordTrace (prefixWord ++ tailWord_2160386) baseStart_2160386 baseEnd_2160386 := by
    simpa [prefixWord, tailWord_2160386, baseEnd_2160386] using wordTrace_append hprefix tailTrace_2160386
  have hstable : (prefixWord ++ tailWord_2160386).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2160386).length < 2 ^ (prefixWord ++ tailWord_2160386).sum := by decide
  have hdescent : baseEnd_2160386 < baseStart_2160386 := by decide
  rcases family_descends (prefixWord ++ tailWord_2160386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2160435 : List Nat := [1, 1, 1, 2, 7, 2, 1, 1, 3, 3]
def baseStart_2160435 : Nat := 118140960795 + 2160435 * 2 ^ 59
def prefixEnd_2160435 : Nat := 4983230072969 + 3 ^ 40 * 2160435 * 2
def baseEnd_2160435 : Nat := 739561051864240014551231

theorem tailTrace_2160435 : CollatzResearch.WordTrace tailWord_2160435 prefixEnd_2160435 739561051864240014551231 := by
  unfold tailWord_2160435
  simp only [CollatzResearch.WordTrace]
  refine ⟨78797537928120442767674759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52531691952080295178449839 78797537928120442767674759)
  ·
    refine ⟨118196306892180664151512139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78797537928120442767674759 118196306892180664151512139)
    ·
      refine ⟨177294460338270996227268209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118196306892180664151512139 177294460338270996227268209)
      ·
        refine ⟨132970845253703247170451157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 177294460338270996227268209 132970845253703247170451157)
        ·
          refine ⟨3116504185633669855557449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 132970845253703247170451157 3116504185633669855557449)
          ·
            refine ⟨2337378139225252391668087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3116504185633669855557449 2337378139225252391668087)
            ·
              refine ⟨3506067208837878587502131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2337378139225252391668087 3506067208837878587502131)
              ·
                refine ⟨5259100813256817881253197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3506067208837878587502131 5259100813256817881253197)
                ·
                  refine ⟨1972162804971306705469949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5259100813256817881253197 1972162804971306705469949)
                  ·
                    refine ⟨739561051864240014551231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1972162804971306705469949 739561051864240014551231)
                    ·
                      rfl

theorem cell22_2160435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 2, 1, 1, 3, 3].length) (baseStart_2160435 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2160435 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2160435 prefixEnd_2160435 := by exact prefixLift 2160435
  have htrace : WordTrace (prefixWord ++ tailWord_2160435) baseStart_2160435 baseEnd_2160435 := by
    simpa [prefixWord, tailWord_2160435, baseEnd_2160435] using wordTrace_append hprefix tailTrace_2160435
  have hstable : (prefixWord ++ tailWord_2160435).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2160435).length < 2 ^ (prefixWord ++ tailWord_2160435).sum := by decide
  have hdescent : baseEnd_2160435 < baseStart_2160435 := by decide
  rcases family_descends (prefixWord ++ tailWord_2160435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2160506 : List Nat := [3, 1, 1, 1, 1, 1, 4, 2, 4, 4]
def baseStart_2160506 : Nat := 118140960795 + 2160506 * 2 ^ 59
def prefixEnd_2160506 : Nat := 4983230072969 + 3 ^ 40 * 2160506 * 2
def baseEnd_2160506 : Nat := 739585356615219496026013

theorem tailTrace_2160506 : CollatzResearch.WordTrace tailWord_2160506 prefixEnd_2160506 739585356615219496026013 := by
  unfold tailWord_2160506
  simp only [CollatzResearch.WordTrace]
  refine ⟨19700031877715805473377343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52533418340575481262339581 19700031877715805473377343)
  ·
    refine ⟨29550047816573708210066015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19700031877715805473377343 29550047816573708210066015)
    ·
      refine ⟨44325071724860562315099023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29550047816573708210066015 44325071724860562315099023)
      ·
        refine ⟨66487607587290843472648535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44325071724860562315099023 66487607587290843472648535)
        ·
          refine ⟨99731411380936265208972803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66487607587290843472648535 99731411380936265208972803)
          ·
            refine ⟨149597117071404397813459205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 99731411380936265208972803 149597117071404397813459205)
            ·
              refine ⟨28049459450888324590023601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 149597117071404397813459205 28049459450888324590023601)
              ·
                refine ⟨21037094588166243442517701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28049459450888324590023601 21037094588166243442517701)
                ·
                  refine ⟨3944455235281170645472069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21037094588166243442517701 3944455235281170645472069)
                  ·
                    refine ⟨739585356615219496026013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3944455235281170645472069 739585356615219496026013)
                    ·
                      rfl

theorem cell22_2160506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 2, 4, 4].length) (baseStart_2160506 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2160506 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2160506 prefixEnd_2160506 := by exact prefixLift 2160506
  have htrace : WordTrace (prefixWord ++ tailWord_2160506) baseStart_2160506 baseEnd_2160506 := by
    simpa [prefixWord, tailWord_2160506, baseEnd_2160506] using wordTrace_append hprefix tailTrace_2160506
  have hstable : (prefixWord ++ tailWord_2160506).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2160506).length < 2 ^ (prefixWord ++ tailWord_2160506).sum := by decide
  have hdescent : baseEnd_2160506 < baseStart_2160506 := by decide
  rcases family_descends (prefixWord ++ tailWord_2160506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2160510 : List Nat := [4, 2, 3, 1, 1, 2, 1, 2, 6]
def baseStart_2160510 : Nat := 118140960795 + 2160510 * 2 ^ 59
def prefixEnd_2160510 : Nat := 4983230072969 + 3 ^ 40 * 2160510 * 2
def baseEnd_2160510 : Nat := 246528908632321606308667

theorem tailTrace_2160510 : CollatzResearch.WordTrace tailWord_2160510 prefixEnd_2160510 246528908632321606308667 := by
  unfold tailWord_2160510
  simp only [CollatzResearch.WordTrace]
  refine ⟨9850034175356091322081873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 52533515601899153717769989 9850034175356091322081873)
  ·
    refine ⟨7387525631517068491561405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9850034175356091322081873 7387525631517068491561405)
    ·
      refine ⟨2770322111818900684335527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7387525631517068491561405 2770322111818900684335527)
      ·
        refine ⟨4155483167728351026503291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2770322111818900684335527 4155483167728351026503291)
        ·
          refine ⟨6233224751592526539754937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4155483167728351026503291 6233224751592526539754937)
          ·
            refine ⟨4674918563694394904816203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6233224751592526539754937 4674918563694394904816203)
            ·
              refine ⟨7012377845541592357224305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4674918563694394904816203 7012377845541592357224305)
              ·
                refine ⟨5259283384156194267918229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7012377845541592357224305 5259283384156194267918229)
                ·
                  refine ⟨246528908632321606308667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5259283384156194267918229 246528908632321606308667)
                  ·
                    rfl

theorem cell22_2160510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 1, 2, 6].length) (baseStart_2160510 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2160510 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2160510 prefixEnd_2160510 := by exact prefixLift 2160510
  have htrace : WordTrace (prefixWord ++ tailWord_2160510) baseStart_2160510 baseEnd_2160510 := by
    simpa [prefixWord, tailWord_2160510, baseEnd_2160510] using wordTrace_append hprefix tailTrace_2160510
  have hstable : (prefixWord ++ tailWord_2160510).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2160510).length < 2 ^ (prefixWord ++ tailWord_2160510).sum := by decide
  have hdescent : baseEnd_2160510 < baseStart_2160510 := by decide
  rcases family_descends (prefixWord ++ tailWord_2160510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2160572 : List Nat := [2, 2, 2, 5, 1, 2, 2, 6]
def baseStart_2160572 : Nat := 118140960795 + 2160572 * 2 ^ 59
def prefixEnd_2160572 : Nat := 4983230072969 + 3 ^ 40 * 2160572 * 2
def baseEnd_2160572 : Nat := 82178661084890813763979

theorem tailTrace_2160572 : CollatzResearch.WordTrace tailWord_2160572 prefixEnd_2160572 82178661084890813763979 := by
  unfold tailWord_2160572
  simp only [CollatzResearch.WordTrace]
  refine ⟨39401267364312057582705985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52535023152416076776941313 39401267364312057582705985)
  ·
    refine ⟨29550950523234043187029489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39401267364312057582705985 29550950523234043187029489)
    ·
      refine ⟨22163212892425532390272117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29550950523234043187029489 22163212892425532390272117)
      ·
        refine ⟨2077801208664893661588011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 22163212892425532390272117 2077801208664893661588011)
        ·
          refine ⟨3116701812997340492382017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2077801208664893661588011 3116701812997340492382017)
          ·
            refine ⟨2337526359748005369286513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3116701812997340492382017 2337526359748005369286513)
            ·
              refine ⟨1753144769811004026964885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2337526359748005369286513 1753144769811004026964885)
              ·
                refine ⟨82178661084890813763979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1753144769811004026964885 82178661084890813763979)
                ·
                  rfl

theorem cell22_2160572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 2, 2, 6].length) (baseStart_2160572 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2160572 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2160572 prefixEnd_2160572 := by exact prefixLift 2160572
  have htrace : WordTrace (prefixWord ++ tailWord_2160572) baseStart_2160572 baseEnd_2160572 := by
    simpa [prefixWord, tailWord_2160572, baseEnd_2160572] using wordTrace_append hprefix tailTrace_2160572
  have hstable : (prefixWord ++ tailWord_2160572).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2160572).length < 2 ^ (prefixWord ++ tailWord_2160572).sum := by decide
  have hdescent : baseEnd_2160572 < baseStart_2160572 := by decide
  rcases family_descends (prefixWord ++ tailWord_2160572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2160581 : List Nat := [1, 3, 1, 1, 1, 1, 1, 4, 4, 5]
def baseStart_2160581 : Nat := 118140960795 + 2160581 * 2 ^ 59
def prefixEnd_2160581 : Nat := 4983230072969 + 3 ^ 40 * 2160581 * 2
def baseEnd_2160581 : Nat := 739611030647944300400783

theorem tailTrace_2160581 : CollatzResearch.WordTrace tailWord_2160581 prefixEnd_2160581 739611030647944300400783 := by
  unfold tailWord_2160581
  simp only [CollatzResearch.WordTrace]
  refine ⟨78802862985591509702489597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52535241990394339801659731 78802862985591509702489597)
  ·
    refine ⟨29551073619596816138433599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 78802862985591509702489597 29551073619596816138433599)
    ·
      refine ⟨44326610429395224207650399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29551073619596816138433599 44326610429395224207650399)
      ·
        refine ⟨66489915644092836311475599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44326610429395224207650399 66489915644092836311475599)
        ·
          refine ⟨99734873466139254467213399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66489915644092836311475599 99734873466139254467213399)
          ·
            refine ⟨149602310199208881700820099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 99734873466139254467213399 149602310199208881700820099)
            ·
              refine ⟨224403465298813322551230149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 149602310199208881700820099 224403465298813322551230149)
              ·
                refine ⟨42075649743527497978355653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 224403465298813322551230149 42075649743527497978355653)
                ·
                  refine ⟨7889184326911405870941685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 42075649743527497978355653 7889184326911405870941685)
                  ·
                    refine ⟨739611030647944300400783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7889184326911405870941685 739611030647944300400783)
                    ·
                      rfl

theorem cell22_2160581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 4, 4, 5].length) (baseStart_2160581 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2160581 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2160581 prefixEnd_2160581 := by exact prefixLift 2160581
  have htrace : WordTrace (prefixWord ++ tailWord_2160581) baseStart_2160581 baseEnd_2160581 := by
    simpa [prefixWord, tailWord_2160581, baseEnd_2160581] using wordTrace_append hprefix tailTrace_2160581
  have hstable : (prefixWord ++ tailWord_2160581).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2160581).length < 2 ^ (prefixWord ++ tailWord_2160581).sum := by decide
  have hdescent : baseEnd_2160581 < baseStart_2160581 := by decide
  rcases family_descends (prefixWord ++ tailWord_2160581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2160643 : List Nat := [1, 1, 1, 3, 2, 1, 1, 3, 6, 3]
def baseStart_2160643 : Nat := 118140960795 + 2160643 * 2 ^ 59
def prefixEnd_2160643 : Nat := 4983230072969 + 3 ^ 40 * 2160643 * 2
def baseEnd_2160643 : Nat := 739632254514996805350593

theorem tailTrace_2160643 : CollatzResearch.WordTrace tailWord_2160643 prefixEnd_2160643 739632254514996805350593 := by
  unfold tailWord_2160643
  simp only [CollatzResearch.WordTrace]
  refine ⟨78805124311366894291246583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52536749540911262860831055 78805124311366894291246583)
  ·
    refine ⟨118207686467050341436869875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78805124311366894291246583 118207686467050341436869875)
    ·
      refine ⟨177311529700575512155304813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118207686467050341436869875 177311529700575512155304813)
      ·
        refine ⟨66491823637715817058239305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 177311529700575512155304813 66491823637715817058239305)
        ·
          refine ⟨49868867728286862793679479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66491823637715817058239305 49868867728286862793679479)
          ·
            refine ⟨74803301592430294190519219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49868867728286862793679479 74803301592430294190519219)
            ·
              refine ⟨112204952388645441285778829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 74803301592430294190519219 112204952388645441285778829)
              ·
                refine ⟨42076857145742040482167061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 112204952388645441285778829 42076857145742040482167061)
                ·
                  refine ⟨1972352678706658147601581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 42076857145742040482167061 1972352678706658147601581)
                  ·
                    refine ⟨739632254514996805350593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1972352678706658147601581 739632254514996805350593)
                    ·
                      rfl

theorem cell22_2160643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 3, 6, 3].length) (baseStart_2160643 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2160643 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2160643 prefixEnd_2160643 := by exact prefixLift 2160643
  have htrace : WordTrace (prefixWord ++ tailWord_2160643) baseStart_2160643 baseEnd_2160643 := by
    simpa [prefixWord, tailWord_2160643, baseEnd_2160643] using wordTrace_append hprefix tailTrace_2160643
  have hstable : (prefixWord ++ tailWord_2160643).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2160643).length < 2 ^ (prefixWord ++ tailWord_2160643).sum := by decide
  have hdescent : baseEnd_2160643 < baseStart_2160643 := by decide
  rcases family_descends (prefixWord ++ tailWord_2160643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2160647 : List Nat := [1, 1, 4, 3, 1, 3, 3, 1, 1, 4]
def baseStart_2160647 : Nat := 118140960795 + 2160647 * 2 ^ 59
def prefixEnd_2160647 : Nat := 4983230072969 + 3 ^ 40 * 2160647 * 2
def baseEnd_2160647 : Nat := 739633623796742128250581

theorem tailTrace_2160647 : CollatzResearch.WordTrace tailWord_2160647 prefixEnd_2160647 739633623796742128250581 := by
  unfold tailWord_2160647
  simp only [CollatzResearch.WordTrace]
  refine ⟨78805270203352402974392195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52536846802234935316261463 78805270203352402974392195)
  ·
    refine ⟨118207905305028604461588293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78805270203352402974392195 118207905305028604461588293)
    ·
      refine ⟨22163982244692863336547805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 118207905305028604461588293 22163982244692863336547805)
      ·
        refine ⟨8311493341759823751205427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22163982244692863336547805 8311493341759823751205427)
        ·
          refine ⟨12467240012639735626808141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8311493341759823751205427 12467240012639735626808141)
          ·
            refine ⟨4675215004739900860053053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12467240012639735626808141 4675215004739900860053053)
            ·
              refine ⟨1753205626777462822519895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4675215004739900860053053 1753205626777462822519895)
              ·
                refine ⟨2629808440166194233779843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1753205626777462822519895 2629808440166194233779843)
                ·
                  refine ⟨3944712660249291350669765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2629808440166194233779843 3944712660249291350669765)
                  ·
                    refine ⟨739633623796742128250581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3944712660249291350669765 739633623796742128250581)
                    ·
                      rfl

theorem cell22_2160647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 3, 1, 1, 4].length) (baseStart_2160647 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2160647 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2160647 prefixEnd_2160647 := by exact prefixLift 2160647
  have htrace : WordTrace (prefixWord ++ tailWord_2160647) baseStart_2160647 baseEnd_2160647 := by
    simpa [prefixWord, tailWord_2160647, baseEnd_2160647] using wordTrace_append hprefix tailTrace_2160647
  have hstable : (prefixWord ++ tailWord_2160647).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2160647).length < 2 ^ (prefixWord ++ tailWord_2160647).sum := by decide
  have hdescent : baseEnd_2160647 < baseStart_2160647 := by decide
  rcases family_descends (prefixWord ++ tailWord_2160647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2160690 : List Nat := [3, 2, 1, 1, 2, 4, 3, 6]
def baseStart_2160690 : Nat := 118140960795 + 2160690 * 2 ^ 59
def prefixEnd_2160690 : Nat := 4983230072969 + 3 ^ 40 * 2160690 * 2
def baseEnd_2160690 : Nat := 82183149286167149936161

theorem tailTrace_2160690 : CollatzResearch.WordTrace tailWord_2160690 prefixEnd_2160690 82183149286167149936161 := by
  unfold tailWord_2160690
  simp only [CollatzResearch.WordTrace]
  refine ⟨19701709635549155329551881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52537892361464414212138349 19701709635549155329551881)
  ·
    refine ⟨14776282226661866497163911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19701709635549155329551881 14776282226661866497163911)
    ·
      refine ⟨22164423339992799745745867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14776282226661866497163911 22164423339992799745745867)
      ·
        refine ⟨33246635009989199618618801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22164423339992799745745867 33246635009989199618618801)
        ·
          refine ⟨24934976257491899713964101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33246635009989199618618801 24934976257491899713964101)
          ·
            refine ⟨4675308048279731196368269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24934976257491899713964101 4675308048279731196368269)
            ·
              refine ⟨1753240518104899198638101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4675308048279731196368269 1753240518104899198638101)
              ·
                refine ⟨82183149286167149936161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1753240518104899198638101 82183149286167149936161)
                ·
                  rfl

theorem cell22_2160690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 3, 6].length) (baseStart_2160690 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2160690 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2160690 prefixEnd_2160690 := by exact prefixLift 2160690
  have htrace : WordTrace (prefixWord ++ tailWord_2160690) baseStart_2160690 baseEnd_2160690 := by
    simpa [prefixWord, tailWord_2160690, baseEnd_2160690] using wordTrace_append hprefix tailTrace_2160690
  have hstable : (prefixWord ++ tailWord_2160690).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2160690).length < 2 ^ (prefixWord ++ tailWord_2160690).sum := by decide
  have hdescent : baseEnd_2160690 < baseStart_2160690 := by decide
  rcases family_descends (prefixWord ++ tailWord_2160690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2160692 : List Nat := [2, 5, 1, 2, 2, 1, 1, 1, 1, 6]
def baseStart_2160692 : Nat := 118140960795 + 2160692 * 2 ^ 59
def prefixEnd_2160692 : Nat := 4983230072969 + 3 ^ 40 * 2160692 * 2
def baseEnd_2160692 : Nat := 739649028216377010875443

theorem tailTrace_2160692 : CollatzResearch.WordTrace tailWord_2160692 prefixEnd_2160692 739649028216377010875443 := by
  unfold tailWord_2160692
  simp only [CollatzResearch.WordTrace]
  refine ⟨39403455744094687829890165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52537940992126250439853553 39403455744094687829890165)
  ·
    refine ⟨3694073976008876984052203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 39403455744094687829890165 3694073976008876984052203)
    ·
      refine ⟨5541110964013315476078305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3694073976008876984052203 5541110964013315476078305)
      ·
        refine ⟨4155833223009986607058729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5541110964013315476078305 4155833223009986607058729)
        ·
          refine ⟨3116874917257489955294047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4155833223009986607058729 3116874917257489955294047)
          ·
            refine ⟨4675312375886234932941071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3116874917257489955294047 4675312375886234932941071)
            ·
              refine ⟨7012968563829352399411607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4675312375886234932941071 7012968563829352399411607)
              ·
                refine ⟨10519452845744028599117411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7012968563829352399411607 10519452845744028599117411)
                ·
                  refine ⟨15779179268616042898676117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10519452845744028599117411 15779179268616042898676117)
                  ·
                    refine ⟨739649028216377010875443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15779179268616042898676117 739649028216377010875443)
                    ·
                      rfl

theorem cell22_2160692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 1, 1, 1, 6].length) (baseStart_2160692 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2160692 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2160692 prefixEnd_2160692 := by exact prefixLift 2160692
  have htrace : WordTrace (prefixWord ++ tailWord_2160692) baseStart_2160692 baseEnd_2160692 := by
    simpa [prefixWord, tailWord_2160692, baseEnd_2160692] using wordTrace_append hprefix tailTrace_2160692
  have hstable : (prefixWord ++ tailWord_2160692).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2160692).length < 2 ^ (prefixWord ++ tailWord_2160692).sum := by decide
  have hdescent : baseEnd_2160692 < baseStart_2160692 := by decide
  rcases family_descends (prefixWord ++ tailWord_2160692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2160793 : List Nat := [1, 2, 1, 2, 1, 2, 1, 3, 3, 6]
def baseStart_2160793 : Nat := 118140960795 + 2160793 * 2 ^ 59
def prefixEnd_2160793 : Nat := 4983230072969 + 3 ^ 40 * 2160793 * 2
def baseEnd_2160793 : Nat := 739683602580446414100133

theorem tailTrace_2160793 : CollatzResearch.WordTrace tailWord_2160793 prefixEnd_2160793 739683602580446414100133 := by
  unfold tailWord_2160793
  simp only [CollatzResearch.WordTrace]
  refine ⟨78810595260823469909207033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52540396840548979939471355 78810595260823469909207033)
  ·
    refine ⟨59107946445617602431905275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78810595260823469909207033 59107946445617602431905275)
    ·
      refine ⟨88661919668426403647857913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59107946445617602431905275 88661919668426403647857913)
      ·
        refine ⟨66496439751319802735893435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 88661919668426403647857913 66496439751319802735893435)
        ·
          refine ⟨99744659626979704103840153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66496439751319802735893435 99744659626979704103840153)
          ·
            refine ⟨74808494720234778077880115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 99744659626979704103840153 74808494720234778077880115)
            ·
              refine ⟨112212742080352167116820173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 74808494720234778077880115 112212742080352167116820173)
              ·
                refine ⟨42079778280132062668807565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 112212742080352167116820173 42079778280132062668807565)
                ·
                  refine ⟨15779916855049523500802837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 42079778280132062668807565 15779916855049523500802837)
                  ·
                    refine ⟨739683602580446414100133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15779916855049523500802837 739683602580446414100133)
                    ·
                      rfl

theorem cell22_2160793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 3, 3, 6].length) (baseStart_2160793 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2160793 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2160793 prefixEnd_2160793 := by exact prefixLift 2160793
  have htrace : WordTrace (prefixWord ++ tailWord_2160793) baseStart_2160793 baseEnd_2160793 := by
    simpa [prefixWord, tailWord_2160793, baseEnd_2160793] using wordTrace_append hprefix tailTrace_2160793
  have hstable : (prefixWord ++ tailWord_2160793).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2160793).length < 2 ^ (prefixWord ++ tailWord_2160793).sum := by decide
  have hdescent : baseEnd_2160793 < baseStart_2160793 := by decide
  rcases family_descends (prefixWord ++ tailWord_2160793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2160799 : List Nat := [1, 1, 2, 6, 1, 3, 1, 2, 1, 4]
def baseStart_2160799 : Nat := 118140960795 + 2160799 * 2 ^ 59
def prefixEnd_2160799 : Nat := 4983230072969 + 3 ^ 40 * 2160799 * 2
def baseEnd_2160799 : Nat := 739685656503064398450115

theorem tailTrace_2160799 : CollatzResearch.WordTrace tailWord_2160799 prefixEnd_2160799 739685656503064398450115 := by
  unfold tailWord_2160799
  simp only [CollatzResearch.WordTrace]
  refine ⟨78810814098801732933925451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52540542732534488622616967 78810814098801732933925451)
  ·
    refine ⟨118216221148202599400888177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78810814098801732933925451 118216221148202599400888177)
    ·
      refine ⟨88662165861151949550666133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 118216221148202599400888177 88662165861151949550666133)
      ·
        refine ⟨4156039024741497635187475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 88662165861151949550666133 4156039024741497635187475)
        ·
          refine ⟨6234058537112246452781213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4156039024741497635187475 6234058537112246452781213)
          ·
            refine ⟨2337771951417092419792955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6234058537112246452781213 2337771951417092419792955)
            ·
              refine ⟨3506657927125638629689433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2337771951417092419792955 3506657927125638629689433)
              ·
                refine ⟨2629993445344228972267075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3506657927125638629689433 2629993445344228972267075)
                ·
                  refine ⟨3944990168016343458400613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2629993445344228972267075 3944990168016343458400613)
                  ·
                    refine ⟨739685656503064398450115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3944990168016343458400613 739685656503064398450115)
                    ·
                      rfl

theorem cell22_2160799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 3, 1, 2, 1, 4].length) (baseStart_2160799 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2160799 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2160799 prefixEnd_2160799 := by exact prefixLift 2160799
  have htrace : WordTrace (prefixWord ++ tailWord_2160799) baseStart_2160799 baseEnd_2160799 := by
    simpa [prefixWord, tailWord_2160799, baseEnd_2160799] using wordTrace_append hprefix tailTrace_2160799
  have hstable : (prefixWord ++ tailWord_2160799).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2160799).length < 2 ^ (prefixWord ++ tailWord_2160799).sum := by decide
  have hdescent : baseEnd_2160799 < baseStart_2160799 := by decide
  rcases family_descends (prefixWord ++ tailWord_2160799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2160904 : List Nat := [2, 1, 3, 2, 3, 2, 3, 1, 5]
def baseStart_2160904 : Nat := 118140960795 + 2160904 * 2 ^ 59
def prefixEnd_2160904 : Nat := 4983230072969 + 3 ^ 40 * 2160904 * 2
def baseEnd_2160904 : Nat := 246573866716293041524931

theorem tailTrace_2160904 : CollatzResearch.WordTrace tailWord_2160904 prefixEnd_2160904 246573866716293041524931 := by
  unfold tailWord_2160904
  simp only [CollatzResearch.WordTrace]
  refine ⟨39407321881710667933248883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52543095842280890577665177 39407321881710667933248883)
  ·
    refine ⟨59110982822566001899873325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39407321881710667933248883 59110982822566001899873325)
    ·
      refine ⟨22166618558462250712452497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 59110982822566001899873325 22166618558462250712452497)
      ·
        refine ⟨16624963918846688034339373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22166618558462250712452497 16624963918846688034339373)
        ·
          refine ⟨6234361469567508012877265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16624963918846688034339373 6234361469567508012877265)
          ·
            refine ⟨4675771102175631009657949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6234361469567508012877265 4675771102175631009657949)
            ·
              refine ⟨1753414163315861628621731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4675771102175631009657949 1753414163315861628621731)
              ·
                refine ⟨2630121244973792442932597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1753414163315861628621731 2630121244973792442932597)
                ·
                  refine ⟨246573866716293041524931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2630121244973792442932597 246573866716293041524931)
                  ·
                    rfl

theorem cell22_2160904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 3, 1, 5].length) (baseStart_2160904 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2160904 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2160904 prefixEnd_2160904 := by exact prefixLift 2160904
  have htrace : WordTrace (prefixWord ++ tailWord_2160904) baseStart_2160904 baseEnd_2160904 := by
    simpa [prefixWord, tailWord_2160904, baseEnd_2160904] using wordTrace_append hprefix tailTrace_2160904
  have hstable : (prefixWord ++ tailWord_2160904).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2160904).length < 2 ^ (prefixWord ++ tailWord_2160904).sum := by decide
  have hdescent : baseEnd_2160904 < baseStart_2160904 := by decide
  rcases family_descends (prefixWord ++ tailWord_2160904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2160917 : List Nat := [1, 3, 2, 1, 2, 1, 3, 4, 1, 4]
def baseStart_2160917 : Nat := 118140960795 + 2160917 * 2 ^ 59
def prefixEnd_2160917 : Nat := 4983230072969 + 3 ^ 40 * 2160917 * 2
def baseEnd_2160917 : Nat := 739726050314551423999753

theorem tailTrace_2160917 : CollatzResearch.WordTrace tailWord_2160917 prefixEnd_2160917 739726050314551423999753 := by
  unfold tailWord_2160917
  simp only [CollatzResearch.WordTrace]
  refine ⟨78815117912374239086721005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52543411941582826057814003 78815117912374239086721005)
  ·
    refine ⟨29555669217140339657520377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 78815117912374239086721005 29555669217140339657520377)
    ·
      refine ⟨22166751912855254743140283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29555669217140339657520377 22166751912855254743140283)
      ·
        refine ⟨33250127869282882114710425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22166751912855254743140283 33250127869282882114710425)
        ·
          refine ⟨24937595901962161586032819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33250127869282882114710425 24937595901962161586032819)
          ·
            refine ⟨37406393852943242379049229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24937595901962161586032819 37406393852943242379049229)
            ·
              refine ⟨14027397694853715892143461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37406393852943242379049229 14027397694853715892143461)
              ·
                refine ⟨2630137067785071729776899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14027397694853715892143461 2630137067785071729776899)
                ·
                  refine ⟨3945205601677607594665349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2630137067785071729776899 3945205601677607594665349)
                  ·
                    refine ⟨739726050314551423999753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3945205601677607594665349 739726050314551423999753)
                    ·
                      rfl

theorem cell22_2160917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 3, 4, 1, 4].length) (baseStart_2160917 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2160917 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2160917 prefixEnd_2160917 := by exact prefixLift 2160917
  have htrace : WordTrace (prefixWord ++ tailWord_2160917) baseStart_2160917 baseEnd_2160917 := by
    simpa [prefixWord, tailWord_2160917, baseEnd_2160917] using wordTrace_append hprefix tailTrace_2160917
  have hstable : (prefixWord ++ tailWord_2160917).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2160917).length < 2 ^ (prefixWord ++ tailWord_2160917).sum := by decide
  have hdescent : baseEnd_2160917 < baseStart_2160917 := by decide
  rcases family_descends (prefixWord ++ tailWord_2160917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2160925 : List Nat := [1, 4, 2, 3, 3, 1, 1, 3, 1, 3]
def baseStart_2160925 : Nat := 118140960795 + 2160925 * 2 ^ 59
def prefixEnd_2160925 : Nat := 4983230072969 + 3 ^ 40 * 2160925 * 2
def baseEnd_2160925 : Nat := 739728788878042069799729

theorem tailTrace_2160925 : CollatzResearch.WordTrace tailWord_2160925 prefixEnd_2160925 739728788878042069799729 := by
  unfold tailWord_2160925
  simp only [CollatzResearch.WordTrace]
  refine ⟨78815409696345256453012229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52543606464230170968674819 78815409696345256453012229)
  ·
    refine ⟨14777889318064735584939793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 78815409696345256453012229 14777889318064735584939793)
    ·
      refine ⟨11083416988548551688704845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14777889318064735584939793 11083416988548551688704845)
      ·
        refine ⟨4156281370705706883264317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11083416988548551688704845 4156281370705706883264317)
        ·
          refine ⟨1558605514014640081224119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4156281370705706883264317 1558605514014640081224119)
          ·
            refine ⟨2337908271021960121836179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1558605514014640081224119 2337908271021960121836179)
            ·
              refine ⟨3506862406532940182754269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2337908271021960121836179 3506862406532940182754269)
              ·
                refine ⟨1315073402449852568532851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3506862406532940182754269 1315073402449852568532851)
                ·
                  refine ⟨1972610103674778852799277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1315073402449852568532851 1972610103674778852799277)
                  ·
                    refine ⟨739728788878042069799729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1972610103674778852799277 739728788878042069799729)
                    ·
                      rfl

theorem cell22_2160925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 3, 1, 1, 3, 1, 3].length) (baseStart_2160925 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2160925 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2160925 prefixEnd_2160925 := by exact prefixLift 2160925
  have htrace : WordTrace (prefixWord ++ tailWord_2160925) baseStart_2160925 baseEnd_2160925 := by
    simpa [prefixWord, tailWord_2160925, baseEnd_2160925] using wordTrace_append hprefix tailTrace_2160925
  have hstable : (prefixWord ++ tailWord_2160925).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2160925).length < 2 ^ (prefixWord ++ tailWord_2160925).sum := by decide
  have hdescent : baseEnd_2160925 < baseStart_2160925 := by decide
  rcases family_descends (prefixWord ++ tailWord_2160925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2160947 : List Nat := [1, 1, 1, 2, 5, 1, 1, 3, 4, 3]
def baseStart_2160947 : Nat := 118140960795 + 2160947 * 2 ^ 59
def prefixEnd_2160947 : Nat := 4983230072969 + 3 ^ 40 * 2160947 * 2
def baseEnd_2160947 : Nat := 739736319927641345749661

theorem tailTrace_2160947 : CollatzResearch.WordTrace tailWord_2160947 prefixEnd_2160947 739736319927641345749661 := by
  unfold tailWord_2160947
  simp only [CollatzResearch.WordTrace]
  refine ⟨78816212102265554210313095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52544141401510369473542063 78816212102265554210313095)
  ·
    refine ⟨118224318153398331315469643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78816212102265554210313095 118224318153398331315469643)
    ·
      refine ⟨177336477230097496973204465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118224318153398331315469643 177336477230097496973204465)
      ·
        refine ⟨133002357922573122729903349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 177336477230097496973204465 133002357922573122729903349)
        ·
          refine ⟨12468971055241230255928439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 133002357922573122729903349 12468971055241230255928439)
          ·
            refine ⟨18703456582861845383892659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12468971055241230255928439 18703456582861845383892659)
            ·
              refine ⟨28055184874292768075838989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18703456582861845383892659 28055184874292768075838989)
              ·
                refine ⟨10520694327859788028439621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28055184874292768075838989 10520694327859788028439621)
                ·
                  refine ⟨1972630186473710255332429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10520694327859788028439621 1972630186473710255332429)
                  ·
                    refine ⟨739736319927641345749661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1972630186473710255332429 739736319927641345749661)
                    ·
                      rfl

theorem cell22_2160947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 3, 4, 3].length) (baseStart_2160947 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2160947 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2160947 prefixEnd_2160947 := by exact prefixLift 2160947
  have htrace : WordTrace (prefixWord ++ tailWord_2160947) baseStart_2160947 baseEnd_2160947 := by
    simpa [prefixWord, tailWord_2160947, baseEnd_2160947] using wordTrace_append hprefix tailTrace_2160947
  have hstable : (prefixWord ++ tailWord_2160947).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2160947).length < 2 ^ (prefixWord ++ tailWord_2160947).sum := by decide
  have hdescent : baseEnd_2160947 < baseStart_2160947 := by decide
  rcases family_descends (prefixWord ++ tailWord_2160947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2161084 : List Nat := [2, 2, 2, 4, 1, 1, 2, 2, 6]
def baseStart_2161084 : Nat := 118140960795 + 2161084 * 2 ^ 59
def prefixEnd_2161084 : Nat := 4983230072969 + 3 ^ 40 * 2161084 * 2
def baseEnd_2161084 : Nat := 246594405942472885024747

theorem tailTrace_2161084 : CollatzResearch.WordTrace tailWord_2161084 prefixEnd_2161084 246594405942472885024747 := by
  unfold tailWord_2161084
  simp only [CollatzResearch.WordTrace]
  refine ⟨39410604451384613304025153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52547472601846151072033537 39410604451384613304025153)
  ·
    refine ⟨29557953338538459978018865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39410604451384613304025153 29557953338538459978018865)
    ·
      refine ⟨22168465003903844983514149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29557953338538459978018865 22168465003903844983514149)
      ·
        refine ⟨4156587188231970934408903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22168465003903844983514149 4156587188231970934408903)
        ·
          refine ⟨6234880782347956401613355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4156587188231970934408903 6234880782347956401613355)
          ·
            refine ⟨9352321173521934602420033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6234880782347956401613355 9352321173521934602420033)
            ·
              refine ⟨7014240880141450951815025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9352321173521934602420033 7014240880141450951815025)
              ·
                refine ⟨5260680660106088213861269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7014240880141450951815025 5260680660106088213861269)
                ·
                  refine ⟨246594405942472885024747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5260680660106088213861269 246594405942472885024747)
                  ·
                    rfl

theorem cell22_2161084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 2, 2, 6].length) (baseStart_2161084 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2161084 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2161084 prefixEnd_2161084 := by exact prefixLift 2161084
  have htrace : WordTrace (prefixWord ++ tailWord_2161084) baseStart_2161084 baseEnd_2161084 := by
    simpa [prefixWord, tailWord_2161084, baseEnd_2161084] using wordTrace_append hprefix tailTrace_2161084
  have hstable : (prefixWord ++ tailWord_2161084).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2161084).length < 2 ^ (prefixWord ++ tailWord_2161084).sum := by decide
  have hdescent : baseEnd_2161084 < baseStart_2161084 := by decide
  rcases family_descends (prefixWord ++ tailWord_2161084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2161097 : List Nat := [1, 2, 1, 1, 2, 1, 6, 1, 1, 6]
def baseStart_2161097 : Nat := 118140960795 + 2161097 * 2 ^ 59
def prefixEnd_2161097 : Nat := 4983230072969 + 3 ^ 40 * 2161097 * 2
def baseEnd_2161097 : Nat := 739787667993090954499201

theorem tailTrace_2161097 : CollatzResearch.WordTrace tailWord_2161097 prefixEnd_2161097 739787667993090954499201 := by
  unfold tailWord_2161097
  simp only [CollatzResearch.WordTrace]
  refine ⟨78821683051722129828273545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52547788701148086552182363 78821683051722129828273545)
  ·
    refine ⟨59116262288791597371205159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78821683051722129828273545 59116262288791597371205159)
    ·
      refine ⟨88674393433187396056807739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59116262288791597371205159 88674393433187396056807739)
      ·
        refine ⟨133011590149781094085211609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88674393433187396056807739 133011590149781094085211609)
        ·
          refine ⟨99758692612335820563908707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 133011590149781094085211609 99758692612335820563908707)
          ·
            refine ⟨149638038918503730845863061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 99758692612335820563908707 149638038918503730845863061)
            ·
              refine ⟨7014283074304862383399831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 149638038918503730845863061 7014283074304862383399831)
              ·
                refine ⟨10521424611457293575099747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7014283074304862383399831 10521424611457293575099747)
                ·
                  refine ⟨15782136917185940362649621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10521424611457293575099747 15782136917185940362649621)
                  ·
                    refine ⟨739787667993090954499201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15782136917185940362649621 739787667993090954499201)
                    ·
                      rfl

theorem cell22_2161097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 6, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 6, 1, 1, 6].length) (baseStart_2161097 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2161097 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2161097 prefixEnd_2161097 := by exact prefixLift 2161097
  have htrace : WordTrace (prefixWord ++ tailWord_2161097) baseStart_2161097 baseEnd_2161097 := by
    simpa [prefixWord, tailWord_2161097, baseEnd_2161097] using wordTrace_append hprefix tailTrace_2161097
  have hstable : (prefixWord ++ tailWord_2161097).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2161097).length < 2 ^ (prefixWord ++ tailWord_2161097).sum := by decide
  have hdescent : baseEnd_2161097 < baseStart_2161097 := by decide
  rcases family_descends (prefixWord ++ tailWord_2161097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2161114 : List Nat := [3, 1, 1, 2, 3, 1, 3, 2, 2, 4]
def baseStart_2161114 : Nat := 118140960795 + 2161114 * 2 ^ 59
def prefixEnd_2161114 : Nat := 4983230072969 + 3 ^ 40 * 2161114 * 2
def baseEnd_2161114 : Nat := 739793487440508576824149

theorem tailTrace_2161114 : CollatzResearch.WordTrace tailWord_2161114 prefixEnd_2161114 739793487440508576824149 := by
  unfold tailWord_2161114
  simp only [CollatzResearch.WordTrace]
  refine ⟨19705575773165135432910599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52548202061773694487761597 19705575773165135432910599)
  ·
    refine ⟨29558363659747703149365899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19705575773165135432910599 29558363659747703149365899)
    ·
      refine ⟨44337545489621554724048849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29558363659747703149365899 44337545489621554724048849)
      ·
        refine ⟨33253159117216166043036637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44337545489621554724048849 33253159117216166043036637)
        ·
          refine ⟨12469934668956062266138739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33253159117216166043036637 12469934668956062266138739)
          ·
            refine ⟨18704902003434093399208109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12469934668956062266138739 18704902003434093399208109)
            ·
              refine ⟨7014338251287785024703041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18704902003434093399208109 7014338251287785024703041)
              ·
                refine ⟨5260753688465838768527281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7014338251287785024703041 5260753688465838768527281)
                ·
                  refine ⟨3945565266349379076395461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5260753688465838768527281 3945565266349379076395461)
                  ·
                    refine ⟨739793487440508576824149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3945565266349379076395461 739793487440508576824149)
                    ·
                      rfl

theorem cell22_2161114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 3, 2, 2, 4].length) (baseStart_2161114 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2161114 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2161114 prefixEnd_2161114 := by exact prefixLift 2161114
  have htrace : WordTrace (prefixWord ++ tailWord_2161114) baseStart_2161114 baseEnd_2161114 := by
    simpa [prefixWord, tailWord_2161114, baseEnd_2161114] using wordTrace_append hprefix tailTrace_2161114
  have hstable : (prefixWord ++ tailWord_2161114).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2161114).length < 2 ^ (prefixWord ++ tailWord_2161114).sum := by decide
  have hdescent : baseEnd_2161114 < baseStart_2161114 := by decide
  rcases family_descends (prefixWord ++ tailWord_2161114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2161133 : List Nat := [1, 5, 1, 3, 1, 2, 1, 3, 2, 3]
def baseStart_2161133 : Nat := 118140960795 + 2161133 * 2 ^ 59
def prefixEnd_2161133 : Nat := 4983230072969 + 3 ^ 40 * 2161133 * 2
def baseEnd_2161133 : Nat := 739799991528798860599091

theorem tailTrace_2161133 : CollatzResearch.WordTrace tailWord_2161133 prefixEnd_2161133 739799991528798860599091 := by
  unfold tailWord_2161133
  simp only [CollatzResearch.WordTrace]
  refine ⟨78822996079591707976584053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52548664053061138651056035 78822996079591707976584053)
  ·
    refine ⟨7389655882461722622804755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 78822996079591707976584053 7389655882461722622804755)
    ·
      refine ⟨11084483823692583934207133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7389655882461722622804755 11084483823692583934207133)
      ·
        refine ⟨4156681433884718975327675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11084483823692583934207133 4156681433884718975327675)
        ·
          refine ⟨6235022150827078462991513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4156681433884718975327675 6235022150827078462991513)
          ·
            refine ⟨4676266613120308847243635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6235022150827078462991513 4676266613120308847243635)
            ·
              refine ⟨7014399919680463270865453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4676266613120308847243635 7014399919680463270865453)
              ·
                refine ⟨2630399969880173726574545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7014399919680463270865453 2630399969880173726574545)
                ·
                  refine ⟨1972799977410130294930909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2630399969880173726574545 1972799977410130294930909)
                  ·
                    refine ⟨739799991528798860599091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1972799977410130294930909 739799991528798860599091)
                    ·
                      rfl

theorem cell22_2161133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 1, 3, 2, 3].length) (baseStart_2161133 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2161133 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2161133 prefixEnd_2161133 := by exact prefixLift 2161133
  have htrace : WordTrace (prefixWord ++ tailWord_2161133) baseStart_2161133 baseEnd_2161133 := by
    simpa [prefixWord, tailWord_2161133, baseEnd_2161133] using wordTrace_append hprefix tailTrace_2161133
  have hstable : (prefixWord ++ tailWord_2161133).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2161133).length < 2 ^ (prefixWord ++ tailWord_2161133).sum := by decide
  have hdescent : baseEnd_2161133 < baseStart_2161133 := by decide
  rcases family_descends (prefixWord ++ tailWord_2161133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2161144 : List Nat := [2, 1, 2, 1, 1, 4, 2, 1, 5, 3]
def baseStart_2161144 : Nat := 118140960795 + 2161144 * 2 ^ 59
def prefixEnd_2161144 : Nat := 4983230072969 + 3 ^ 40 * 2161144 * 2
def baseEnd_2161144 : Nat := 739803757053598498574057

theorem tailTrace_2161144 : CollatzResearch.WordTrace tailWord_2161144 prefixEnd_2161144 739803757053598498574057 := by
  unfold tailWord_2161144
  simp only [CollatzResearch.WordTrace]
  refine ⟨39411698641275928427617243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52548931521701237903489657 39411698641275928427617243)
  ·
    refine ⟨59117547961913892641425865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39411698641275928427617243 59117547961913892641425865)
    ·
      refine ⟨44338160971435419481069399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59117547961913892641425865 44338160971435419481069399)
      ·
        refine ⟨66507241457153129221604099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44338160971435419481069399 66507241457153129221604099)
        ·
          refine ⟨99760862185729693832406149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66507241457153129221604099 99760862185729693832406149)
          ·
            refine ⟨18705161659824317593576153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 99760862185729693832406149 18705161659824317593576153)
            ·
              refine ⟨14028871244868238195182115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18705161659824317593576153 14028871244868238195182115)
              ·
                refine ⟨21043306867302357292773173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14028871244868238195182115 21043306867302357292773173)
                ·
                  refine ⟨1972810018809595996197485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 21043306867302357292773173 1972810018809595996197485)
                  ·
                    refine ⟨739803757053598498574057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1972810018809595996197485 739803757053598498574057)
                    ·
                      rfl

theorem cell22_2161144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 2, 1, 5, 3].length) (baseStart_2161144 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2161144 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2161144 prefixEnd_2161144 := by exact prefixLift 2161144
  have htrace : WordTrace (prefixWord ++ tailWord_2161144) baseStart_2161144 baseEnd_2161144 := by
    simpa [prefixWord, tailWord_2161144, baseEnd_2161144] using wordTrace_append hprefix tailTrace_2161144
  have hstable : (prefixWord ++ tailWord_2161144).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2161144).length < 2 ^ (prefixWord ++ tailWord_2161144).sum := by decide
  have hdescent : baseEnd_2161144 < baseStart_2161144 := by decide
  rcases family_descends (prefixWord ++ tailWord_2161144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2161157 : List Nat := [1, 3, 1, 1, 2, 2, 2, 1, 9]
def baseStart_2161157 : Nat := 118140960795 + 2161157 * 2 ^ 59
def prefixEnd_2161157 : Nat := 4983230072969 + 3 ^ 40 * 2161157 * 2
def baseEnd_2161157 : Nat := 246602735739756932666339

theorem tailTrace_2161157 : CollatzResearch.WordTrace tailWord_2161157 prefixEnd_2161157 246602735739756932666339 := by
  unfold tailWord_2161157
  simp only [CollatzResearch.WordTrace]
  refine ⟨78823871431504760075457725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52549247621003173383638483 78823871431504760075457725)
  ·
    refine ⟨29558951786814285028296647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 78823871431504760075457725 29558951786814285028296647)
    ·
      refine ⟨44338427680221427542444971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29558951786814285028296647 44338427680221427542444971)
      ·
        refine ⟨66507641520332141313667457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44338427680221427542444971 66507641520332141313667457)
        ·
          refine ⟨49880731140249105985250593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66507641520332141313667457 49880731140249105985250593)
          ·
            refine ⟨37410548355186829488937945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49880731140249105985250593 37410548355186829488937945)
            ·
              refine ⟨28057911266390122116703459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37410548355186829488937945 28057911266390122116703459)
              ·
                refine ⟨42086866899585183175055189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28057911266390122116703459 42086866899585183175055189)
                ·
                  refine ⟨246602735739756932666339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 42086866899585183175055189 246602735739756932666339)
                  ·
                    rfl

theorem cell22_2161157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 1, 9].length) (baseStart_2161157 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2161157 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2161157 prefixEnd_2161157 := by exact prefixLift 2161157
  have htrace : WordTrace (prefixWord ++ tailWord_2161157) baseStart_2161157 baseEnd_2161157 := by
    simpa [prefixWord, tailWord_2161157, baseEnd_2161157] using wordTrace_append hprefix tailTrace_2161157
  have hstable : (prefixWord ++ tailWord_2161157).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2161157).length < 2 ^ (prefixWord ++ tailWord_2161157).sum := by decide
  have hdescent : baseEnd_2161157 < baseStart_2161157 := by decide
  rcases family_descends (prefixWord ++ tailWord_2161157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2161221 : List Nat := [1, 3, 1, 1, 1, 6, 1, 3, 1, 4]
def baseStart_2161221 : Nat := 118140960795 + 2161221 * 2 ^ 59
def prefixEnd_2161221 : Nat := 4983230072969 + 3 ^ 40 * 2161221 * 2
def baseEnd_2161221 : Nat := 739830115727195964398821

theorem tailTrace_2161221 : CollatzResearch.WordTrace tailWord_2161221 prefixEnd_2161221 739830115727195964398821 := by
  unfold tailWord_2161221
  simp only [CollatzResearch.WordTrace]
  refine ⟨78826205703272899005787517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52550803802181932670525011 78826205703272899005787517)
  ·
    refine ⟨29559827138727337127170319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 78826205703272899005787517 29559827138727337127170319)
    ·
      refine ⟨44339740708091005690755479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29559827138727337127170319 44339740708091005690755479)
      ·
        refine ⟨66509611062136508536133219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44339740708091005690755479 66509611062136508536133219)
        ·
          refine ⟨99764416593204762804199829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66509611062136508536133219 99764416593204762804199829)
          ·
            refine ⟨4676457027806473256446867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 99764416593204762804199829 4676457027806473256446867)
            ·
              refine ⟨7014685541709709884670301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4676457027806473256446867 7014685541709709884670301)
              ·
                refine ⟨2630507078141141206751363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7014685541709709884670301 2630507078141141206751363)
                ·
                  refine ⟨3945760617211711810127045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2630507078141141206751363 3945760617211711810127045)
                  ·
                    refine ⟨739830115727195964398821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3945760617211711810127045 739830115727195964398821)
                    ·
                      rfl

theorem cell22_2161221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 1, 3, 1, 4].length) (baseStart_2161221 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2161221 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2161221 prefixEnd_2161221 := by exact prefixLift 2161221
  have htrace : WordTrace (prefixWord ++ tailWord_2161221) baseStart_2161221 baseEnd_2161221 := by
    simpa [prefixWord, tailWord_2161221, baseEnd_2161221] using wordTrace_append hprefix tailTrace_2161221
  have hstable : (prefixWord ++ tailWord_2161221).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2161221).length < 2 ^ (prefixWord ++ tailWord_2161221).sum := by decide
  have hdescent : baseEnd_2161221 < baseStart_2161221 := by decide
  rcases family_descends (prefixWord ++ tailWord_2161221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2161236 : List Nat := [2, 4, 1, 1, 1, 4, 2, 1, 6]
def baseStart_2161236 : Nat := 118140960795 + 2161236 * 2 ^ 59
def prefixEnd_2161236 : Nat := 4983230072969 + 3 ^ 40 * 2161236 * 2
def baseEnd_2161236 : Nat := 246611750177913641757925

theorem tailTrace_2161236 : CollatzResearch.WordTrace tailWord_2161236 prefixEnd_2161236 246611750177913641757925 := by
  unfold tailWord_2161236
  simp only [CollatzResearch.WordTrace]
  refine ⟨39413376399109278283791781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52551168532145704378389041 39413376399109278283791781)
  ·
    refine ⟨7390008074832989678210959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 39413376399109278283791781 7390008074832989678210959)
    ·
      refine ⟨11085012112249484517316439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7390008074832989678210959 11085012112249484517316439)
      ·
        refine ⟨16627518168374226775974659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11085012112249484517316439 16627518168374226775974659)
        ·
          refine ⟨24941277252561340163961989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16627518168374226775974659 24941277252561340163961989)
          ·
            refine ⟨4676489484855251280742873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24941277252561340163961989 4676489484855251280742873)
            ·
              refine ⟨3507367113641438460557155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4676489484855251280742873 3507367113641438460557155)
              ·
                refine ⟨5261050670462157690835733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3507367113641438460557155 5261050670462157690835733)
                ·
                  refine ⟨246611750177913641757925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5261050670462157690835733 246611750177913641757925)
                  ·
                    rfl

theorem cell22_2161236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 2, 1, 6].length) (baseStart_2161236 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2161236 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2161236 prefixEnd_2161236 := by exact prefixLift 2161236
  have htrace : WordTrace (prefixWord ++ tailWord_2161236) baseStart_2161236 baseEnd_2161236 := by
    simpa [prefixWord, tailWord_2161236, baseEnd_2161236] using wordTrace_append hprefix tailTrace_2161236
  have hstable : (prefixWord ++ tailWord_2161236).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2161236).length < 2 ^ (prefixWord ++ tailWord_2161236).sum := by decide
  have hdescent : baseEnd_2161236 < baseStart_2161236 := by decide
  rcases family_descends (prefixWord ++ tailWord_2161236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2161249 : List Nat := [1, 2, 3, 1, 1, 4, 1, 2, 1, 6]
def baseStart_2161249 : Nat := 118140960795 + 2161249 * 2 ^ 59
def prefixEnd_2161249 : Nat := 4983230072969 + 3 ^ 40 * 2161249 * 2
def baseEnd_2161249 : Nat := 739839700699413224698735

theorem tailTrace_2161249 : CollatzResearch.WordTrace tailWord_2161249 prefixEnd_2161249 739839700699413224698735 := by
  unfold tailWord_2161249
  simp only [CollatzResearch.WordTrace]
  refine ⟨78827226947171459787806801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52551484631447639858537867 78827226947171459787806801)
  ·
    refine ⟨59120420210378594840855101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78827226947171459787806801 59120420210378594840855101)
    ·
      refine ⟨22170157578891973065320663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 59120420210378594840855101 22170157578891973065320663)
      ·
        refine ⟨33255236368337959597980995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22170157578891973065320663 33255236368337959597980995)
        ·
          refine ⟨49882854552506939396971493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33255236368337959597980995 49882854552506939396971493)
          ·
            refine ⟨9353035228595051136932155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 49882854552506939396971493 9353035228595051136932155)
            ·
              refine ⟨14029552842892576705398233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9353035228595051136932155 14029552842892576705398233)
              ·
                refine ⟨10522164632169432529048675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14029552842892576705398233 10522164632169432529048675)
                ·
                  refine ⟨15783246948254148793573013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10522164632169432529048675 15783246948254148793573013)
                  ·
                    refine ⟨739839700699413224698735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15783246948254148793573013 739839700699413224698735)
                    ·
                      rfl

theorem cell22_2161249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 1, 2, 1, 6].length) (baseStart_2161249 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2161249 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2161249 prefixEnd_2161249 := by exact prefixLift 2161249
  have htrace : WordTrace (prefixWord ++ tailWord_2161249) baseStart_2161249 baseEnd_2161249 := by
    simpa [prefixWord, tailWord_2161249, baseEnd_2161249] using wordTrace_append hprefix tailTrace_2161249
  have hstable : (prefixWord ++ tailWord_2161249).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2161249).length < 2 ^ (prefixWord ++ tailWord_2161249).sum := by decide
  have hdescent : baseEnd_2161249 < baseStart_2161249 := by decide
  rcases family_descends (prefixWord ++ tailWord_2161249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2161390 : List Nat := [4, 1, 2, 1, 1, 3, 4, 1, 1, 4]
def baseStart_2161390 : Nat := 118140960795 + 2161390 * 2 ^ 59
def prefixEnd_2161390 : Nat := 4983230072969 + 3 ^ 40 * 2161390 * 2
def baseEnd_2161390 : Nat := 739887967880935856923303

theorem tailTrace_2161390 : CollatzResearch.WordTrace tailWord_2161390 prefixEnd_2161390 739887967880935856923303 := by
  unfold tailWord_2161390
  simp only [CollatzResearch.WordTrace]
  refine ⟨9854046204957580108586203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 52554913093107093912459749 9854046204957580108586203)
  ·
    refine ⟨14781069307436370162879305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9854046204957580108586203 14781069307436370162879305)
    ·
      refine ⟨11085801980577277622159479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14781069307436370162879305 11085801980577277622159479)
      ·
        refine ⟨16628702970865916433239219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11085801980577277622159479 16628702970865916433239219)
        ·
          refine ⟨24943054456298874649858829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16628702970865916433239219 24943054456298874649858829)
          ·
            refine ⟨9353645421112077993697061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24943054456298874649858829 9353645421112077993697061)
            ·
              refine ⟨1753808516458514623818199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9353645421112077993697061 1753808516458514623818199)
              ·
                refine ⟨2630712774687771935727299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1753808516458514623818199 2630712774687771935727299)
                ·
                  refine ⟨3946069162031657903590949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2630712774687771935727299 3946069162031657903590949)
                  ·
                    refine ⟨739887967880935856923303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3946069162031657903590949 739887967880935856923303)
                    ·
                      rfl

theorem cell22_2161390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 4, 1, 1, 4].length) (baseStart_2161390 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2161390 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2161390 prefixEnd_2161390 := by exact prefixLift 2161390
  have htrace : WordTrace (prefixWord ++ tailWord_2161390) baseStart_2161390 baseEnd_2161390 := by
    simpa [prefixWord, tailWord_2161390, baseEnd_2161390] using wordTrace_append hprefix tailTrace_2161390
  have hstable : (prefixWord ++ tailWord_2161390).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2161390).length < 2 ^ (prefixWord ++ tailWord_2161390).sum := by decide
  have hdescent : baseEnd_2161390 < baseStart_2161390 := by decide
  rcases family_descends (prefixWord ++ tailWord_2161390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2161401 : List Nat := [1, 2, 1, 3, 1, 1, 1, 6, 2, 4]
def baseStart_2161401 : Nat := 118140960795 + 2161401 * 2 ^ 59
def prefixEnd_2161401 : Nat := 4983230072969 + 3 ^ 40 * 2161401 * 2
def baseEnd_2161401 : Nat := 739891733405735494898269

theorem tailTrace_2161401 : CollatzResearch.WordTrace tailWord_2161401 prefixEnd_2161401 739891733405735494898269 := by
  unfold tailWord_2161401
  simp only [CollatzResearch.WordTrace]
  refine ⟨78832770842620789747340057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52555180561747193164893371 78832770842620789747340057)
  ·
    refine ⟨59124578131965592310505043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78832770842620789747340057 59124578131965592310505043)
    ·
      refine ⟨88686867197948388465757565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59124578131965592310505043 88686867197948388465757565)
      ·
        refine ⟨33257575199230645674659087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 88686867197948388465757565 33257575199230645674659087)
        ·
          refine ⟨49886362798845968511988631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33257575199230645674659087 49886362798845968511988631)
          ·
            refine ⟨74829544198268952767982947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49886362798845968511988631 74829544198268952767982947)
            ·
              refine ⟨112244316297403429151974421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 74829544198268952767982947 112244316297403429151974421)
              ·
                refine ⟨5261452326440785741498801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 112244316297403429151974421 5261452326440785741498801)
                ·
                  refine ⟨3946089244830589306124101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5261452326440785741498801 3946089244830589306124101)
                  ·
                    refine ⟨739891733405735494898269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3946089244830589306124101 739891733405735494898269)
                    ·
                      rfl

theorem cell22_2161401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 6, 2, 4].length) (baseStart_2161401 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2161401 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2161401 prefixEnd_2161401 := by exact prefixLift 2161401
  have htrace : WordTrace (prefixWord ++ tailWord_2161401) baseStart_2161401 baseEnd_2161401 := by
    simpa [prefixWord, tailWord_2161401, baseEnd_2161401] using wordTrace_append hprefix tailTrace_2161401
  have hstable : (prefixWord ++ tailWord_2161401).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2161401).length < 2 ^ (prefixWord ++ tailWord_2161401).sum := by decide
  have hdescent : baseEnd_2161401 < baseStart_2161401 := by decide
  rcases family_descends (prefixWord ++ tailWord_2161401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2161450 : List Nat := [3, 1, 4, 3, 1, 2, 8]
def baseStart_2161450 : Nat := 118140960795 + 2161450 * 2 ^ 59
def prefixEnd_2161450 : Nat := 4983230072969 + 3 ^ 40 * 2161450 * 2
def baseEnd_2161450 : Nat := 27404018781745025941597

theorem tailTrace_2161450 : CollatzResearch.WordTrace tailWord_2161450 prefixEnd_2161450 27404018781745025941597 := by
  unfold tailWord_2161450
  simp only [CollatzResearch.WordTrace]
  refine ⟨19708639504860817778968451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52556372012962180743915869 19708639504860817778968451)
  ·
    refine ⟨29562959257291226668452677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19708639504860817778968451 29562959257291226668452677)
    ·
      refine ⟨5543054860742105000334877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 29562959257291226668452677 5543054860742105000334877)
      ·
        refine ⟨2078645572778289375125579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5543054860742105000334877 2078645572778289375125579)
        ·
          refine ⟨3117968359167434062688369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2078645572778289375125579 3117968359167434062688369)
          ·
            refine ⟨2338476269375575547016277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3117968359167434062688369 2338476269375575547016277)
            ·
              refine ⟨27404018781745025941597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2338476269375575547016277 27404018781745025941597)
              ·
                rfl

theorem cell22_2161450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 2, 8].length) (baseStart_2161450 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2161450 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2161450 prefixEnd_2161450 := by exact prefixLift 2161450
  have htrace : WordTrace (prefixWord ++ tailWord_2161450) baseStart_2161450 baseEnd_2161450 := by
    simpa [prefixWord, tailWord_2161450, baseEnd_2161450] using wordTrace_append hprefix tailTrace_2161450
  have hstable : (prefixWord ++ tailWord_2161450).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2161450).length < 2 ^ (prefixWord ++ tailWord_2161450).sum := by decide
  have hdescent : baseEnd_2161450 < baseStart_2161450 := by decide
  rcases family_descends (prefixWord ++ tailWord_2161450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2161600 : List Nat := [2, 1, 1, 2, 3, 3, 2, 2, 3, 3]
def baseStart_2161600 : Nat := 118140960795 + 2161600 * 2 ^ 59
def prefixEnd_2161600 : Nat := 4983230072969 + 3 ^ 40 * 2161600 * 2
def baseEnd_2161600 : Nat := 739959855172565309172659

theorem tailTrace_2161600 : CollatzResearch.WordTrace tailWord_2161600 prefixEnd_2161600 739959855172565309172659 := by
  unfold tailWord_2161600
  simp only [CollatzResearch.WordTrace]
  refine ⟨39420014484449923366917127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52560019312599897822556169 39420014484449923366917127)
  ·
    refine ⟨59130021726674885050375691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39420014484449923366917127 59130021726674885050375691)
    ·
      refine ⟨88695032590012327575563537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59130021726674885050375691 88695032590012327575563537)
      ·
        refine ⟨66521274442509245681672653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 88695032590012327575563537 66521274442509245681672653)
        ·
          refine ⟨24945477915940967130627245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 66521274442509245681672653 24945477915940967130627245)
          ·
            refine ⟨9354554218477862673985217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24945477915940967130627245 9354554218477862673985217)
            ·
              refine ⟨7015915663858397005488913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9354554218477862673985217 7015915663858397005488913)
              ·
                refine ⟨5261936747893797754116685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7015915663858397005488913 5261936747893797754116685)
                ·
                  refine ⟨1973226280460174157793757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5261936747893797754116685 1973226280460174157793757)
                  ·
                    refine ⟨739959855172565309172659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1973226280460174157793757 739959855172565309172659)
                    ·
                      rfl

theorem cell22_2161600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 2, 2, 3, 3].length) (baseStart_2161600 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2161600 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2161600 prefixEnd_2161600 := by exact prefixLift 2161600
  have htrace : WordTrace (prefixWord ++ tailWord_2161600) baseStart_2161600 baseEnd_2161600 := by
    simpa [prefixWord, tailWord_2161600, baseEnd_2161600] using wordTrace_append hprefix tailTrace_2161600
  have hstable : (prefixWord ++ tailWord_2161600).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2161600).length < 2 ^ (prefixWord ++ tailWord_2161600).sum := by decide
  have hdescent : baseEnd_2161600 < baseStart_2161600 := by decide
  rcases family_descends (prefixWord ++ tailWord_2161600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2161634 : List Nat := [3, 3, 3, 1, 1, 1, 3, 1, 3, 3]
def baseStart_2161634 : Nat := 118140960795 + 2161634 * 2 ^ 59
def prefixEnd_2161634 : Nat := 4983230072969 + 3 ^ 40 * 2161634 * 2
def baseEnd_2161634 : Nat := 739971494067400553822555

theorem tailTrace_2161634 : CollatzResearch.WordTrace tailWord_2161634 prefixEnd_2161634 739971494067400553822555 := by
  unfold tailWord_2161634
  simp only [CollatzResearch.WordTrace]
  refine ⟨19710317262694167635142989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52560846033851113693714637 19710317262694167635142989)
  ·
    refine ⟨7391368973510312863178621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19710317262694167635142989 7391368973510312863178621)
    ·
      refine ⟨2771763365066367323691983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7391368973510312863178621 2771763365066367323691983)
      ·
        refine ⟨4157645047599550985537975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2771763365066367323691983 4157645047599550985537975)
        ·
          refine ⟨6236467571399326478306963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4157645047599550985537975 6236467571399326478306963)
          ·
            refine ⟨9354701357098989717460445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6236467571399326478306963 9354701357098989717460445)
            ·
              refine ⟨3508013008912121144047667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9354701357098989717460445 3508013008912121144047667)
              ·
                refine ⟨5262019513368181716071501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3508013008912121144047667 5262019513368181716071501)
                ·
                  refine ⟨1973257317513068143526813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5262019513368181716071501 1973257317513068143526813)
                  ·
                    refine ⟨739971494067400553822555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1973257317513068143526813 739971494067400553822555)
                    ·
                      rfl

theorem cell22_2161634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 3, 1, 3, 3].length) (baseStart_2161634 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2161634 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2161634 prefixEnd_2161634 := by exact prefixLift 2161634
  have htrace : WordTrace (prefixWord ++ tailWord_2161634) baseStart_2161634 baseEnd_2161634 := by
    simpa [prefixWord, tailWord_2161634, baseEnd_2161634] using wordTrace_append hprefix tailTrace_2161634
  have hstable : (prefixWord ++ tailWord_2161634).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2161634).length < 2 ^ (prefixWord ++ tailWord_2161634).sum := by decide
  have hdescent : baseEnd_2161634 < baseStart_2161634 := by decide
  rcases family_descends (prefixWord ++ tailWord_2161634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2161647 : List Nat := [1, 1, 2, 1, 4, 5, 2, 1, 5]
def baseStart_2161647 : Nat := 118140960795 + 2161647 * 2 ^ 59
def prefixEnd_2161647 : Nat := 4983230072969 + 3 ^ 40 * 2161647 * 2
def baseEnd_2161647 : Nat := 246658648077690951082505

theorem tailTrace_2161647 : CollatzResearch.WordTrace tailWord_2161647 prefixEnd_2161647 246658648077690951082505 := by
  unfold tailWord_2161647
  simp only [CollatzResearch.WordTrace]
  refine ⟨78841743199729573760795195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52561162133153049173863463 78841743199729573760795195)
  ·
    refine ⟨118262614799594360641192793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78841743199729573760795195 118262614799594360641192793)
    ·
      refine ⟨88696961099695770480894595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 118262614799594360641192793 88696961099695770480894595)
      ·
        refine ⟨133045441649543655721341893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88696961099695770480894595 133045441649543655721341893)
        ·
          refine ⟨24946020309289435447751605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 133045441649543655721341893 24946020309289435447751605)
          ·
            refine ⟨2338689403995884573226713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 24946020309289435447751605 2338689403995884573226713)
            ·
              refine ⟨1754017052996913429920035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2338689403995884573226713 1754017052996913429920035)
              ·
                refine ⟨2631025579495370144880053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1754017052996913429920035 2631025579495370144880053)
                ·
                  refine ⟨246658648077690951082505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2631025579495370144880053 246658648077690951082505)
                  ·
                    rfl

theorem cell22_2161647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 5, 2, 1, 5].length) (baseStart_2161647 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2161647 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2161647 prefixEnd_2161647 := by exact prefixLift 2161647
  have htrace : WordTrace (prefixWord ++ tailWord_2161647) baseStart_2161647 baseEnd_2161647 := by
    simpa [prefixWord, tailWord_2161647, baseEnd_2161647] using wordTrace_append hprefix tailTrace_2161647
  have hstable : (prefixWord ++ tailWord_2161647).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2161647).length < 2 ^ (prefixWord ++ tailWord_2161647).sum := by decide
  have hdescent : baseEnd_2161647 < baseStart_2161647 := by decide
  rcases family_descends (prefixWord ++ tailWord_2161647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2161658 : List Nat := [3, 1, 1, 1, 1, 2, 1, 6, 6]
def baseStart_2161658 : Nat := 118140960795 + 2161658 * 2 ^ 59
def prefixEnd_2161658 : Nat := 4983230072969 + 3 ^ 40 * 2161658 * 2
def baseEnd_2161658 : Nat := 246659903252624163740827

theorem tailTrace_2161658 : CollatzResearch.WordTrace tailWord_2161658 prefixEnd_2161658 246659903252624163740827 := by
  unfold tailWord_2161658
  simp only [CollatzResearch.WordTrace]
  refine ⟨19710536100672430659861407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52561429601793148426297085 19710536100672430659861407)
  ·
    refine ⟨29565804151008645989792111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19710536100672430659861407 29565804151008645989792111)
    ·
      refine ⟨44348706226512968984688167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29565804151008645989792111 44348706226512968984688167)
      ·
        refine ⟨66523059339769453477032251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44348706226512968984688167 66523059339769453477032251)
        ·
          refine ⟨99784589009654180215548377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66523059339769453477032251 99784589009654180215548377)
          ·
            refine ⟨74838441757240635161661283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 99784589009654180215548377 74838441757240635161661283)
            ·
              refine ⟨112257662635860952742491925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 74838441757240635161661283 112257662635860952742491925)
              ·
                refine ⟨5262077936055982159804309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 112257662635860952742491925 5262077936055982159804309)
                ·
                  refine ⟨246659903252624163740827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5262077936055982159804309 246659903252624163740827)
                  ·
                    rfl

theorem cell22_2161658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 6, 6].length) (baseStart_2161658 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2161658 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2161658 prefixEnd_2161658 := by exact prefixLift 2161658
  have htrace : WordTrace (prefixWord ++ tailWord_2161658) baseStart_2161658 baseEnd_2161658 := by
    simpa [prefixWord, tailWord_2161658, baseEnd_2161658] using wordTrace_append hprefix tailTrace_2161658
  have hstable : (prefixWord ++ tailWord_2161658).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2161658).length < 2 ^ (prefixWord ++ tailWord_2161658).sum := by decide
  have hdescent : baseEnd_2161658 < baseStart_2161658 := by decide
  rcases family_descends (prefixWord ++ tailWord_2161658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2161660 : List Nat := [2, 2, 2, 1, 2, 4, 1, 1, 3, 4]
def baseStart_2161660 : Nat := 118140960795 + 2161660 * 2 ^ 59
def prefixEnd_2161660 : Nat := 4983230072969 + 3 ^ 40 * 2161660 * 2
def baseEnd_2161660 : Nat := 739980394398745152672475

theorem tailTrace_2161660 : CollatzResearch.WordTrace tailWord_2161660 prefixEnd_2161660 739980394398745152672475 := by
  unfold tailWord_2161660
  simp only [CollatzResearch.WordTrace]
  refine ⟨39421108674341238490509217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52561478232454984654012289 39421108674341238490509217)
  ·
    refine ⟨29565831505755928867881913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39421108674341238490509217 29565831505755928867881913)
    ·
      refine ⟨22174373629316946650911435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29565831505755928867881913 22174373629316946650911435)
      ·
        refine ⟨33261560443975419976367153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22174373629316946650911435 33261560443975419976367153)
        ·
          refine ⟨24946170332981564982275365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33261560443975419976367153 24946170332981564982275365)
          ·
            refine ⟨4677406937434043434176631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24946170332981564982275365 4677406937434043434176631)
            ·
              refine ⟨7016110406151065151264947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4677406937434043434176631 7016110406151065151264947)
              ·
                refine ⟨10524165609226597726897421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7016110406151065151264947 10524165609226597726897421)
                ·
                  refine ⟨3946562103459974147586533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10524165609226597726897421 3946562103459974147586533)
                  ·
                    refine ⟨739980394398745152672475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3946562103459974147586533 739980394398745152672475)
                    ·
                      rfl

theorem cell22_2161660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 1, 1, 3, 4].length) (baseStart_2161660 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2161660 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2161660 prefixEnd_2161660 := by exact prefixLift 2161660
  have htrace : WordTrace (prefixWord ++ tailWord_2161660) baseStart_2161660 baseEnd_2161660 := by
    simpa [prefixWord, tailWord_2161660, baseEnd_2161660] using wordTrace_append hprefix tailTrace_2161660
  have hstable : (prefixWord ++ tailWord_2161660).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2161660).length < 2 ^ (prefixWord ++ tailWord_2161660).sum := by decide
  have hdescent : baseEnd_2161660 < baseStart_2161660 := by decide
  rcases family_descends (prefixWord ++ tailWord_2161660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2161741 : List Nat := [1, 6, 1, 1, 1, 4, 1, 2, 2, 3]
def baseStart_2161741 : Nat := 118140960795 + 2161741 * 2 ^ 59
def prefixEnd_2161741 : Nat := 4983230072969 + 3 ^ 40 * 2161741 * 2
def baseEnd_2161741 : Nat := 740008122354087941397227

theorem tailTrace_2161741 : CollatzResearch.WordTrace tailWord_2161741 prefixEnd_2161741 740008122354087941397227 := by
  unfold tailWord_2161741
  simp only [CollatzResearch.WordTrace]
  refine ⟨78845171661389027814717077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52563447774259351876478051 78845171661389027814717077)
  ·
    refine ⟨3695867421627610678814863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 78845171661389027814717077 3695867421627610678814863)
    ·
      refine ⟨5543801132441416018222295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3695867421627610678814863 5543801132441416018222295)
      ·
        refine ⟨8315701698662124027333443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5543801132441416018222295 8315701698662124027333443)
        ·
          refine ⟨12473552547993186041000165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8315701698662124027333443 12473552547993186041000165)
          ·
            refine ⟨2338791102748722382687531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12473552547993186041000165 2338791102748722382687531)
            ·
              refine ⟨3508186654123083574031297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2338791102748722382687531 3508186654123083574031297)
              ·
                refine ⟨2631139990592312680523473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3508186654123083574031297 2631139990592312680523473)
                ·
                  refine ⟨1973354992944234510392605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2631139990592312680523473 1973354992944234510392605)
                  ·
                    refine ⟨740008122354087941397227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1973354992944234510392605 740008122354087941397227)
                    ·
                      rfl

theorem cell22_2161741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 4, 1, 2, 2, 3].length) (baseStart_2161741 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2161741 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2161741 prefixEnd_2161741 := by exact prefixLift 2161741
  have htrace : WordTrace (prefixWord ++ tailWord_2161741) baseStart_2161741 baseEnd_2161741 := by
    simpa [prefixWord, tailWord_2161741, baseEnd_2161741] using wordTrace_append hprefix tailTrace_2161741
  have hstable : (prefixWord ++ tailWord_2161741).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2161741).length < 2 ^ (prefixWord ++ tailWord_2161741).sum := by decide
  have hdescent : baseEnd_2161741 < baseStart_2161741 := by decide
  rcases family_descends (prefixWord ++ tailWord_2161741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2161752 : List Nat := [2, 1, 2, 2, 1, 3, 4, 1, 3, 3]
def baseStart_2161752 : Nat := 118140960795 + 2161752 * 2 ^ 59
def prefixEnd_2161752 : Nat := 4983230072969 + 3 ^ 40 * 2161752 * 2
def baseEnd_2161752 : Nat := 740011887878887579372193

theorem tailTrace_2161752 : CollatzResearch.WordTrace tailWord_2161752 prefixEnd_2161752 740011887878887579372193 := by
  unfold tailWord_2161752
  simp only [CollatzResearch.WordTrace]
  refine ⟨39422786432174588346683755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52563715242899451128911673 39422786432174588346683755)
  ·
    refine ⟨59134179648261882520025633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39422786432174588346683755 59134179648261882520025633)
    ·
      refine ⟨44350634736196411890019225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59134179648261882520025633 44350634736196411890019225)
      ·
        refine ⟨33262976052147308917514419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44350634736196411890019225 33262976052147308917514419)
        ·
          refine ⟨49894464078220963376271629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33262976052147308917514419 49894464078220963376271629)
          ·
            refine ⟨18710424029332861266101861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 49894464078220963376271629 18710424029332861266101861)
            ·
              refine ⟨3508204505499911487394099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18710424029332861266101861 3508204505499911487394099)
              ·
                refine ⟨5262306758249867231091149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3508204505499911487394099 5262306758249867231091149)
                ·
                  refine ⟨1973365034343700211659181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5262306758249867231091149 1973365034343700211659181)
                  ·
                    refine ⟨740011887878887579372193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1973365034343700211659181 740011887878887579372193)
                    ·
                      rfl

theorem cell22_2161752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 4, 1, 3, 3].length) (baseStart_2161752 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2161752 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2161752 prefixEnd_2161752 := by exact prefixLift 2161752
  have htrace : WordTrace (prefixWord ++ tailWord_2161752) baseStart_2161752 baseEnd_2161752 := by
    simpa [prefixWord, tailWord_2161752, baseEnd_2161752] using wordTrace_append hprefix tailTrace_2161752
  have hstable : (prefixWord ++ tailWord_2161752).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2161752).length < 2 ^ (prefixWord ++ tailWord_2161752).sum := by decide
  have hdescent : baseEnd_2161752 < baseStart_2161752 := by decide
  rcases family_descends (prefixWord ++ tailWord_2161752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2161829 : List Nat := [1, 3, 1, 2, 1, 6, 1, 2, 1, 4]
def baseStart_2161829 : Nat := 118140960795 + 2161829 * 2 ^ 59
def prefixEnd_2161829 : Nat := 4983230072969 + 3 ^ 40 * 2161829 * 2
def baseEnd_2161829 : Nat := 740038246552485045196957

theorem tailTrace_2161829 : CollatzResearch.WordTrace tailWord_2161829 prefixEnd_2161829 740038246552485045196957 := by
  unfold tailWord_2161829
  simp only [CollatzResearch.WordTrace]
  refine ⟨78848381285070218843920541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52565587523380145895947027 78848381285070218843920541)
  ·
    refine ⟨29568142981901332066470203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 78848381285070218843920541 29568142981901332066470203)
    ·
      refine ⟨44352214472851998099705305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29568142981901332066470203 44352214472851998099705305)
      ·
        refine ⟨33264160854638998574778979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44352214472851998099705305 33264160854638998574778979)
        ·
          refine ⟨49896241281958497862168469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33264160854638998574778979 49896241281958497862168469)
          ·
            refine ⟨2338886310091804587289147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 49896241281958497862168469 2338886310091804587289147)
            ·
              refine ⟨3508329465137706880933721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2338886310091804587289147 3508329465137706880933721)
              ·
                refine ⟨2631247098853280160700291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3508329465137706880933721 2631247098853280160700291)
                ·
                  refine ⟨3946870648279920241050437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2631247098853280160700291 3946870648279920241050437)
                  ·
                    refine ⟨740038246552485045196957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3946870648279920241050437 740038246552485045196957)
                    ·
                      rfl

theorem cell22_2161829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 6, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 6, 1, 2, 1, 4].length) (baseStart_2161829 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2161829 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2161829 prefixEnd_2161829 := by exact prefixLift 2161829
  have htrace : WordTrace (prefixWord ++ tailWord_2161829) baseStart_2161829 baseEnd_2161829 := by
    simpa [prefixWord, tailWord_2161829, baseEnd_2161829] using wordTrace_append hprefix tailTrace_2161829
  have hstable : (prefixWord ++ tailWord_2161829).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2161829).length < 2 ^ (prefixWord ++ tailWord_2161829).sum := by decide
  have hdescent : baseEnd_2161829 < baseStart_2161829 := by decide
  rcases family_descends (prefixWord ++ tailWord_2161829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2161840 : List Nat := [2, 1, 1, 1, 2, 1, 2, 2, 6, 4]
def baseStart_2161840 : Nat := 118140960795 + 2161840 * 2 ^ 59
def prefixEnd_2161840 : Nat := 4983230072969 + 3 ^ 40 * 2161840 * 2
def baseEnd_2161840 : Nat := 740042012077284683171923

theorem tailTrace_2161840 : CollatzResearch.WordTrace tailWord_2161840 prefixEnd_2161840 740042012077284683171923 := by
  unfold tailWord_2161840
  simp only [CollatzResearch.WordTrace]
  refine ⟨39424391244015183861285487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52565854992020245148380649 39424391244015183861285487)
  ·
    refine ⟨59136586866022775791928231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39424391244015183861285487 59136586866022775791928231)
    ·
      refine ⟨88704880299034163687892347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59136586866022775791928231 88704880299034163687892347)
      ·
        refine ⟨133057320448551245531838521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88704880299034163687892347 133057320448551245531838521)
        ·
          refine ⟨99792990336413434148878891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 133057320448551245531838521 99792990336413434148878891)
          ·
            refine ⟨149689485504620151223318337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 99792990336413434148878891 149689485504620151223318337)
            ·
              refine ⟨112267114128465113417488753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 149689485504620151223318337 112267114128465113417488753)
              ·
                refine ⟨84200335596348835063116565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 112267114128465113417488753 84200335596348835063116565)
                ·
                  refine ⟨3946890731078851643583589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 84200335596348835063116565 3946890731078851643583589)
                  ·
                    refine ⟨740042012077284683171923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3946890731078851643583589 740042012077284683171923)
                    ·
                      rfl

theorem cell22_2161840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 2, 6, 4].length) (baseStart_2161840 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2161840 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2161840 prefixEnd_2161840 := by exact prefixLift 2161840
  have htrace : WordTrace (prefixWord ++ tailWord_2161840) baseStart_2161840 baseEnd_2161840 := by
    simpa [prefixWord, tailWord_2161840, baseEnd_2161840] using wordTrace_append hprefix tailTrace_2161840
  have hstable : (prefixWord ++ tailWord_2161840).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2161840).length < 2 ^ (prefixWord ++ tailWord_2161840).sum := by decide
  have hdescent : baseEnd_2161840 < baseStart_2161840 := by decide
  rcases family_descends (prefixWord ++ tailWord_2161840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2161842 : List Nat := [3, 2, 1, 1, 1, 5, 1, 2, 1, 5]
def baseStart_2161842 : Nat := 118140960795 + 2161842 * 2 ^ 59
def prefixEnd_2161842 : Nat := 4983230072969 + 3 ^ 40 * 2161842 * 2
def baseEnd_2161842 : Nat := 740042696718157344621917

theorem tailTrace_2161842 : CollatzResearch.WordTrace tailWord_2161842 prefixEnd_2161842 740042696718157344621917 := by
  unfold tailWord_2161842
  simp only [CollatzResearch.WordTrace]
  refine ⟨19712213858505780516035945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52565903622682081376095853 19712213858505780516035945)
  ·
    refine ⟨14784160393879335387026959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19712213858505780516035945 14784160393879335387026959)
    ·
      refine ⟨22176240590819003080540439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14784160393879335387026959 22176240590819003080540439)
      ·
        refine ⟨33264360886228504620810659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22176240590819003080540439 33264360886228504620810659)
        ·
          refine ⟨49896541329342756931215989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33264360886228504620810659 49896541329342756931215989)
          ·
            refine ⟨4677800749625883462301499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 49896541329342756931215989 4677800749625883462301499)
            ·
              refine ⟨7016701124438825193452249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4677800749625883462301499 7016701124438825193452249)
              ·
                refine ⟨5262525843329118895089187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7016701124438825193452249 5262525843329118895089187)
                ·
                  refine ⟨7893788764993678342633781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5262525843329118895089187 7893788764993678342633781)
                  ·
                    refine ⟨740042696718157344621917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7893788764993678342633781 740042696718157344621917)
                    ·
                      rfl

theorem cell22_2161842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 1, 2, 1, 5].length) (baseStart_2161842 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2161842 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2161842 prefixEnd_2161842 := by exact prefixLift 2161842
  have htrace : WordTrace (prefixWord ++ tailWord_2161842) baseStart_2161842 baseEnd_2161842 := by
    simpa [prefixWord, tailWord_2161842, baseEnd_2161842] using wordTrace_append hprefix tailTrace_2161842
  have hstable : (prefixWord ++ tailWord_2161842).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2161842).length < 2 ^ (prefixWord ++ tailWord_2161842).sum := by decide
  have hdescent : baseEnd_2161842 < baseStart_2161842 := by decide
  rcases family_descends (prefixWord ++ tailWord_2161842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2161876 : List Nat := [2, 4, 1, 4, 1, 1, 2, 1, 1, 5]
def baseStart_2161876 : Nat := 118140960795 + 2161876 * 2 ^ 59
def prefixEnd_2161876 : Nat := 4983230072969 + 3 ^ 40 * 2161876 * 2
def baseEnd_2161876 : Nat := 740054335612992589271813

theorem tailTrace_2161876 : CollatzResearch.WordTrace tailWord_2161876 prefixEnd_2161876 740054335612992589271813 := by
  unfold tailWord_2161876
  simp only [CollatzResearch.WordTrace]
  refine ⟨39425047757949972935440741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52566730343933297247254321 39425047757949972935440741)
  ·
    refine ⟨7392196454615619925395139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 39425047757949972935440741 7392196454615619925395139)
    ·
      refine ⟨11088294681923429888092709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7392196454615619925395139 11088294681923429888092709)
      ·
        refine ⟨2079055252860643104017383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11088294681923429888092709 2079055252860643104017383)
        ·
          refine ⟨3118582879290964656026075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2079055252860643104017383 3118582879290964656026075)
          ·
            refine ⟨4677874318936446984039113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3118582879290964656026075 4677874318936446984039113)
            ·
              refine ⟨3508405739202335238029335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4677874318936446984039113 3508405739202335238029335)
              ·
                refine ⟨5262608608803502857044003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3508405739202335238029335 5262608608803502857044003)
                ·
                  refine ⟨7893912913205254285566005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5262608608803502857044003 7893912913205254285566005)
                  ·
                    refine ⟨740054335612992589271813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7893912913205254285566005 740054335612992589271813)
                    ·
                      rfl

theorem cell22_2161876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 2, 1, 1, 5].length) (baseStart_2161876 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2161876 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2161876 prefixEnd_2161876 := by exact prefixLift 2161876
  have htrace : WordTrace (prefixWord ++ tailWord_2161876) baseStart_2161876 baseEnd_2161876 := by
    simpa [prefixWord, tailWord_2161876, baseEnd_2161876] using wordTrace_append hprefix tailTrace_2161876
  have hstable : (prefixWord ++ tailWord_2161876).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2161876).length < 2 ^ (prefixWord ++ tailWord_2161876).sum := by decide
  have hdescent : baseEnd_2161876 < baseStart_2161876 := by decide
  rcases family_descends (prefixWord ++ tailWord_2161876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2161887 : List Nat := [1, 1, 2, 3, 2, 1, 3, 1, 5, 3]
def baseStart_2161887 : Nat := 118140960795 + 2161887 * 2 ^ 59
def prefixEnd_2161887 : Nat := 4983230072969 + 3 ^ 40 * 2161887 * 2
def baseEnd_2161887 : Nat := 740058101137792227246779

theorem tailTrace_2161887 : CollatzResearch.WordTrace tailWord_2161887 prefixEnd_2161887 740058101137792227246779 := by
  unfold tailWord_2161887
  simp only [CollatzResearch.WordTrace]
  refine ⟨78850496718860094749531915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52566997812573396499687943 78850496718860094749531915)
  ·
    refine ⟨118275745078290142124297873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78850496718860094749531915 118275745078290142124297873)
    ·
      refine ⟨88706808808717606593223405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 118275745078290142124297873 88706808808717606593223405)
      ·
        refine ⟨33265053303269102472458777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 88706808808717606593223405 33265053303269102472458777)
        ·
          refine ⟨24948789977451826854344083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33265053303269102472458777 24948789977451826854344083)
          ·
            refine ⟨37423184966177740281516125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24948789977451826854344083 37423184966177740281516125)
            ·
              refine ⟨14033694362316652605568547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37423184966177740281516125 14033694362316652605568547)
              ·
                refine ⟨21050541543474978908352821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14033694362316652605568547 21050541543474978908352821)
                ·
                  refine ⟨1973488269700779272658077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 21050541543474978908352821 1973488269700779272658077)
                  ·
                    refine ⟨740058101137792227246779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1973488269700779272658077 740058101137792227246779)
                    ·
                      rfl

theorem cell22_2161887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 3, 1, 5, 3].length) (baseStart_2161887 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2161887 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2161887 prefixEnd_2161887 := by exact prefixLift 2161887
  have htrace : WordTrace (prefixWord ++ tailWord_2161887) baseStart_2161887 baseEnd_2161887 := by
    simpa [prefixWord, tailWord_2161887, baseEnd_2161887] using wordTrace_append hprefix tailTrace_2161887
  have hstable : (prefixWord ++ tailWord_2161887).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2161887).length < 2 ^ (prefixWord ++ tailWord_2161887).sum := by decide
  have hdescent : baseEnd_2161887 < baseStart_2161887 := by decide
  rcases family_descends (prefixWord ++ tailWord_2161887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2161921 : List Nat := [1, 2, 4, 1, 1, 3, 2, 4, 1, 3]
def baseStart_2161921 : Nat := 118140960795 + 2161921 * 2 ^ 59
def prefixEnd_2161921 : Nat := 4983230072969 + 3 ^ 40 * 2161921 * 2
def baseEnd_2161921 : Nat := 740069740032627471896675

theorem tailTrace_2161921 : CollatzResearch.WordTrace tailWord_2161921 prefixEnd_2161921 740069740032627471896675 := by
  unfold tailWord_2161921
  simp only [CollatzResearch.WordTrace]
  refine ⟨78851736800736918556269617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52567824533824612370846411 78851736800736918556269617)
  ·
    refine ⟨59138802600552688917202213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78851736800736918556269617 59138802600552688917202213)
    ·
      refine ⟨11088525487603629171975415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 59138802600552688917202213 11088525487603629171975415)
      ·
        refine ⟨16632788231405443757963123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11088525487603629171975415 16632788231405443757963123)
        ·
          refine ⟨24949182347108165636944685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16632788231405443757963123 24949182347108165636944685)
          ·
            refine ⟨9355943380165562113854257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24949182347108165636944685 9355943380165562113854257)
            ·
              refine ⟨7016957535124171585390693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9355943380165562113854257 7016957535124171585390693)
              ·
                refine ⟨1315679537835782172260755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7016957535124171585390693 1315679537835782172260755)
                ·
                  refine ⟨1973519306753673258391133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1315679537835782172260755 1973519306753673258391133)
                  ·
                    refine ⟨740069740032627471896675, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1973519306753673258391133 740069740032627471896675)
                    ·
                      rfl

theorem cell22_2161921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 2, 4, 1, 3].length) (baseStart_2161921 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2161921 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2161921 prefixEnd_2161921 := by exact prefixLift 2161921
  have htrace : WordTrace (prefixWord ++ tailWord_2161921) baseStart_2161921 baseEnd_2161921 := by
    simpa [prefixWord, tailWord_2161921, baseEnd_2161921] using wordTrace_append hprefix tailTrace_2161921
  have hstable : (prefixWord ++ tailWord_2161921).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2161921).length < 2 ^ (prefixWord ++ tailWord_2161921).sum := by decide
  have hdescent : baseEnd_2161921 < baseStart_2161921 := by decide
  rcases family_descends (prefixWord ++ tailWord_2161921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2161932 : List Nat := [2, 2, 1, 2, 2, 3, 2, 1, 2, 5]
def baseStart_2161932 : Nat := 118140960795 + 2161932 * 2 ^ 59
def prefixEnd_2161932 : Nat := 4983230072969 + 3 ^ 40 * 2161932 * 2
def baseEnd_2161932 : Nat := 740073505557427109871641

theorem tailTrace_2161932 : CollatzResearch.WordTrace tailWord_2161932 prefixEnd_2161932 740073505557427109871641 := by
  unfold tailWord_2161932
  simp only [CollatzResearch.WordTrace]
  refine ⟨39426069001848533717460025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52568092002464711623280033 39426069001848533717460025)
  ·
    refine ⟨29569551751386400288095019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39426069001848533717460025 29569551751386400288095019)
    ·
      refine ⟨44354327627079600432142529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29569551751386400288095019 44354327627079600432142529)
      ·
        refine ⟨33265745720309700324106897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44354327627079600432142529 33265745720309700324106897)
        ·
          refine ⟨24949309290232275243080173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33265745720309700324106897 24949309290232275243080173)
          ·
            refine ⟨9355990983837103216155065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24949309290232275243080173 9355990983837103216155065)
            ·
              refine ⟨7016993237877827412116299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9355990983837103216155065 7016993237877827412116299)
              ·
                refine ⟨10525489856816741118174449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7016993237877827412116299 10525489856816741118174449)
                ·
                  refine ⟨7894117392612555838630837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10525489856816741118174449 7894117392612555838630837)
                  ·
                    refine ⟨740073505557427109871641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7894117392612555838630837 740073505557427109871641)
                    ·
                      rfl

theorem cell22_2161932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 2, 1, 2, 5].length) (baseStart_2161932 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2161932 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2161932 prefixEnd_2161932 := by exact prefixLift 2161932
  have htrace : WordTrace (prefixWord ++ tailWord_2161932) baseStart_2161932 baseEnd_2161932 := by
    simpa [prefixWord, tailWord_2161932, baseEnd_2161932] using wordTrace_append hprefix tailTrace_2161932
  have hstable : (prefixWord ++ tailWord_2161932).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2161932).length < 2 ^ (prefixWord ++ tailWord_2161932).sum := by decide
  have hdescent : baseEnd_2161932 < baseStart_2161932 := by decide
  rcases family_descends (prefixWord ++ tailWord_2161932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2161992 : List Nat := [2, 1, 3, 1, 1, 2, 1, 1, 6, 4]
def baseStart_2161992 : Nat := 118140960795 + 2161992 * 2 ^ 59
def prefixEnd_2161992 : Nat := 4983230072969 + 3 ^ 40 * 2161992 * 2
def baseEnd_2161992 : Nat := 740094044783606953371457

theorem tailTrace_2161992 : CollatzResearch.WordTrace tailWord_2161992 prefixEnd_2161992 740094044783606953371457 := by
  unfold tailWord_2161992
  simp only [CollatzResearch.WordTrace]
  refine ⟨39427163191739848841052115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52569550922319798454736153 39427163191739848841052115)
  ·
    refine ⟨59140744787609773261578173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39427163191739848841052115 59140744787609773261578173)
    ·
      refine ⟨22177779295353664973091815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 59140744787609773261578173 22177779295353664973091815)
      ·
        refine ⟨33266668943030497459637723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22177779295353664973091815 33266668943030497459637723)
        ·
          refine ⟨49900003414545746189456585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33266668943030497459637723 49900003414545746189456585)
          ·
            refine ⟨37425002560909309642092439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49900003414545746189456585 37425002560909309642092439)
            ·
              refine ⟨56137503841363964463138659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37425002560909309642092439 56137503841363964463138659)
              ·
                refine ⟨84206255762045946694707989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 56137503841363964463138659 84206255762045946694707989)
                ·
                  refine ⟨3947168238845903751314437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 84206255762045946694707989 3947168238845903751314437)
                  ·
                    refine ⟨740094044783606953371457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3947168238845903751314437 740094044783606953371457)
                    ·
                      rfl

theorem cell22_2161992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 1, 6, 4].length) (baseStart_2161992 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2161992 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2161992 prefixEnd_2161992 := by exact prefixLift 2161992
  have htrace : WordTrace (prefixWord ++ tailWord_2161992) baseStart_2161992 baseEnd_2161992 := by
    simpa [prefixWord, tailWord_2161992, baseEnd_2161992] using wordTrace_append hprefix tailTrace_2161992
  have hstable : (prefixWord ++ tailWord_2161992).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2161992).length < 2 ^ (prefixWord ++ tailWord_2161992).sum := by decide
  have hdescent : baseEnd_2161992 < baseStart_2161992 := by decide
  rcases family_descends (prefixWord ++ tailWord_2161992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2162007 : List Nat := [1, 1, 3, 2, 3, 2, 2, 8]
def baseStart_2162007 : Nat := 118140960795 + 2162007 * 2 ^ 59
def prefixEnd_2162007 : Nat := 4983230072969 + 3 ^ 40 * 2162007 * 2
def baseEnd_2162007 : Nat := 82233242176683546027379

theorem tailTrace_2162007 : CollatzResearch.WordTrace tailWord_2162007 prefixEnd_2162007 82233242176683546027379 := by
  unfold tailWord_2162007
  simp only [CollatzResearch.WordTrace]
  refine ⟨78854873478425355243900275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52569915652283570162600183 78854873478425355243900275)
  ·
    refine ⟨118282310217638032865850413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78854873478425355243900275 118282310217638032865850413)
    ·
      refine ⟨44355866331614262324693905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 118282310217638032865850413 44355866331614262324693905)
      ·
        refine ⟨33266899748710696743520429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44355866331614262324693905 33266899748710696743520429)
        ·
          refine ⟨12475087405766511278820161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33266899748710696743520429 12475087405766511278820161)
          ·
            refine ⟨9356315554324883459115121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12475087405766511278820161 9356315554324883459115121)
            ·
              refine ⟨7017236665743662594336341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9356315554324883459115121 7017236665743662594336341)
              ·
                refine ⟨82233242176683546027379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7017236665743662594336341 82233242176683546027379)
                ·
                  rfl

theorem cell22_2162007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 2, 8].length) (baseStart_2162007 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2162007 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2162007 prefixEnd_2162007 := by exact prefixLift 2162007
  have htrace : WordTrace (prefixWord ++ tailWord_2162007) baseStart_2162007 baseEnd_2162007 := by
    simpa [prefixWord, tailWord_2162007, baseEnd_2162007] using wordTrace_append hprefix tailTrace_2162007
  have hstable : (prefixWord ++ tailWord_2162007).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2162007).length < 2 ^ (prefixWord ++ tailWord_2162007).sum := by decide
  have hdescent : baseEnd_2162007 < baseStart_2162007 := by decide
  rcases family_descends (prefixWord ++ tailWord_2162007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2162024 : List Nat := [2, 1, 4, 2, 4, 9]
def baseStart_2162024 : Nat := 118140960795 + 2162024 * 2 ^ 59
def prefixEnd_2162024 : Nat := 4983230072969 + 3 ^ 40 * 2162024 * 2
def baseEnd_2162024 : Nat := 9137098753550241192239

theorem tailTrace_2162024 : CollatzResearch.WordTrace tailWord_2162024 prefixEnd_2162024 9137098753550241192239 := by
  unfold tailWord_2162024
  simp only [CollatzResearch.WordTrace]
  refine ⟨39427746759681883573634563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52570329012909178098179417 39427746759681883573634563)
  ·
    refine ⟨59141620139522825360451845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39427746759681883573634563 59141620139522825360451845)
    ·
      refine ⟨11089053776160529755084721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 59141620139522825360451845 11089053776160529755084721)
      ·
        refine ⟨8316790332120397316313541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11089053776160529755084721 8316790332120397316313541)
        ·
          refine ⟨1559398187272574496808789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8316790332120397316313541 1559398187272574496808789)
          ·
            refine ⟨9137098753550241192239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1559398187272574496808789 9137098753550241192239)
            ·
              rfl

theorem cell22_2162024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 4, 9].length) (baseStart_2162024 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2162024 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2162024 prefixEnd_2162024 := by exact prefixLift 2162024
  have htrace : WordTrace (prefixWord ++ tailWord_2162024) baseStart_2162024 baseEnd_2162024 := by
    simpa [prefixWord, tailWord_2162024, baseEnd_2162024] using wordTrace_append hprefix tailTrace_2162024
  have hstable : (prefixWord ++ tailWord_2162024).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2162024).length < 2 ^ (prefixWord ++ tailWord_2162024).sum := by decide
  have hdescent : baseEnd_2162024 < baseStart_2162024 := by decide
  rcases family_descends (prefixWord ++ tailWord_2162024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2162039 : List Nat := [1, 1, 3, 1, 1, 2, 4, 3, 3, 3]
def baseStart_2162039 : Nat := 118140960795 + 2162039 * 2 ^ 59
def prefixEnd_2162039 : Nat := 4983230072969 + 3 ^ 40 * 2162039 * 2
def baseEnd_2162039 : Nat := 740110133844114497446313

theorem tailTrace_2162039 : CollatzResearch.WordTrace tailWord_2162039 prefixEnd_2162039 740110133844114497446313 := by
  unfold tailWord_2162039
  simp only [CollatzResearch.WordTrace]
  refine ⟨78856040614309424709065171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52570693742872949806043447 78856040614309424709065171)
  ·
    refine ⟨118284060921464137063597757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78856040614309424709065171 118284060921464137063597757)
    ·
      refine ⟨44356522845549051398849159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 118284060921464137063597757 44356522845549051398849159)
      ·
        refine ⟨66534784268323577098273739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44356522845549051398849159 66534784268323577098273739)
        ·
          refine ⟨99802176402485365647410609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66534784268323577098273739 99802176402485365647410609)
          ·
            refine ⟨74851632301864024235557957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 99802176402485365647410609 74851632301864024235557957)
            ·
              refine ⟨14034681056599504544167117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 74851632301864024235557957 14034681056599504544167117)
              ·
                refine ⟨5263005396224814204062669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14034681056599504544167117 5263005396224814204062669)
                ·
                  refine ⟨1973627023584305326523501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5263005396224814204062669 1973627023584305326523501)
                  ·
                    refine ⟨740110133844114497446313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1973627023584305326523501 740110133844114497446313)
                    ·
                      rfl

theorem cell22_2162039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 3, 3].length) (baseStart_2162039 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2162039 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2162039 prefixEnd_2162039 := by exact prefixLift 2162039
  have htrace : WordTrace (prefixWord ++ tailWord_2162039) baseStart_2162039 baseEnd_2162039 := by
    simpa [prefixWord, tailWord_2162039, baseEnd_2162039] using wordTrace_append hprefix tailTrace_2162039
  have hstable : (prefixWord ++ tailWord_2162039).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2162039).length < 2 ^ (prefixWord ++ tailWord_2162039).sum := by decide
  have hdescent : baseEnd_2162039 < baseStart_2162039 := by decide
  rcases family_descends (prefixWord ++ tailWord_2162039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2162056 : List Nat := [2, 1, 3, 3, 1, 3, 1, 2, 3, 3]
def baseStart_2162056 : Nat := 118140960795 + 2162056 * 2 ^ 59
def prefixEnd_2162056 : Nat := 4983230072969 + 3 ^ 40 * 2162056 * 2
def baseEnd_2162056 : Nat := 740115953291532119771261

theorem tailTrace_2162056 : CollatzResearch.WordTrace tailWord_2162056 prefixEnd_2162056 740115953291532119771261 := by
  unfold tailWord_2162056
  simp only [CollatzResearch.WordTrace]
  refine ⟨39428330327623918306217011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52571107103498557741622681 39428330327623918306217011)
  ·
    refine ⟨59142495491435877459325517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39428330327623918306217011 59142495491435877459325517)
    ·
      refine ⟨22178435809288454047247069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 59142495491435877459325517 22178435809288454047247069)
      ·
        refine ⟨8316913428483170267717651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22178435809288454047247069 8316913428483170267717651)
        ·
          refine ⟨12475370142724755401576477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8316913428483170267717651 12475370142724755401576477)
          ·
            refine ⟨4678263803521783275591179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12475370142724755401576477 4678263803521783275591179)
            ·
              refine ⟨7017395705282674913386769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4678263803521783275591179 7017395705282674913386769)
              ·
                refine ⟨5263046778962006185040077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7017395705282674913386769 5263046778962006185040077)
                ·
                  refine ⟨1973642542110752319390029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5263046778962006185040077 1973642542110752319390029)
                  ·
                    refine ⟨740115953291532119771261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1973642542110752319390029 740115953291532119771261)
                    ·
                      rfl

theorem cell22_2162056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 1, 2, 3, 3].length) (baseStart_2162056 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2162056 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2162056 prefixEnd_2162056 := by exact prefixLift 2162056
  have htrace : WordTrace (prefixWord ++ tailWord_2162056) baseStart_2162056 baseEnd_2162056 := by
    simpa [prefixWord, tailWord_2162056, baseEnd_2162056] using wordTrace_append hprefix tailTrace_2162056
  have hstable : (prefixWord ++ tailWord_2162056).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2162056).length < 2 ^ (prefixWord ++ tailWord_2162056).sum := by decide
  have hdescent : baseEnd_2162056 < baseStart_2162056 := by decide
  rcases family_descends (prefixWord ++ tailWord_2162056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2162073 : List Nat := [1, 2, 1, 2, 1, 6, 2, 3, 1, 3]
def baseStart_2162073 : Nat := 118140960795 + 2162073 * 2 ^ 59
def prefixEnd_2162073 : Nat := 4983230072969 + 3 ^ 40 * 2162073 * 2
def baseEnd_2162073 : Nat := 740121772738949742096209

theorem tailTrace_2162073 : CollatzResearch.WordTrace tailWord_2162073 prefixEnd_2162073 740121772738949742096209 := by
  unfold tailWord_2162073
  simp only [CollatzResearch.WordTrace]
  refine ⟨78857280696186248515802873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52571520464124165677201915 78857280696186248515802873)
  ·
    refine ⟨59142960522139686386852155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78857280696186248515802873 59142960522139686386852155)
    ·
      refine ⟨88714440783209529580278233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59142960522139686386852155 88714440783209529580278233)
      ·
        refine ⟨66535830587407147185208675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 88714440783209529580278233 66535830587407147185208675)
        ·
          refine ⟨99803745881110720777813013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66535830587407147185208675 99803745881110720777813013)
          ·
            refine ⟨4678300588177065036459985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 99803745881110720777813013 4678300588177065036459985)
            ·
              refine ⟨3508725441132798777344989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4678300588177065036459985 3508725441132798777344989)
              ·
                refine ⟨1315772040424799541504371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3508725441132798777344989 1315772040424799541504371)
                ·
                  refine ⟨1973658060637199312256557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1315772040424799541504371 1973658060637199312256557)
                  ·
                    refine ⟨740121772738949742096209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1973658060637199312256557 740121772738949742096209)
                    ·
                      rfl

theorem cell22_2162073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 2, 3, 1, 3].length) (baseStart_2162073 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2162073 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2162073 prefixEnd_2162073 := by exact prefixLift 2162073
  have htrace : WordTrace (prefixWord ++ tailWord_2162073) baseStart_2162073 baseEnd_2162073 := by
    simpa [prefixWord, tailWord_2162073, baseEnd_2162073] using wordTrace_append hprefix tailTrace_2162073
  have hstable : (prefixWord ++ tailWord_2162073).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2162073).length < 2 ^ (prefixWord ++ tailWord_2162073).sum := by decide
  have hdescent : baseEnd_2162073 < baseStart_2162073 := by decide
  rcases family_descends (prefixWord ++ tailWord_2162073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2162178 : List Nat := [3, 4, 1, 2, 1, 1, 1, 3, 2, 4]
def baseStart_2162178 : Nat := 118140960795 + 2162178 * 2 ^ 59
def prefixEnd_2162178 : Nat := 4983230072969 + 3 ^ 40 * 2162178 * 2
def baseEnd_2162178 : Nat := 740157716384764468220887

theorem tailTrace_2162178 : CollatzResearch.WordTrace tailWord_2162178 prefixEnd_2162178 740157716384764468220887 := by
  unfold tailWord_2162178
  simp only [CollatzResearch.WordTrace]
  refine ⟨19715277590201462862093797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52574073573870567632250125 19715277590201462862093797)
  ·
    refine ⟨3696614548162774286642587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19715277590201462862093797 3696614548162774286642587)
    ·
      refine ⟨5544921822244161429963881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3696614548162774286642587 5544921822244161429963881)
      ·
        refine ⟨4158691366683121072472911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5544921822244161429963881 4158691366683121072472911)
        ·
          refine ⟨6238037050024681608709367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4158691366683121072472911 6238037050024681608709367)
          ·
            refine ⟨9357055575037022413064051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6238037050024681608709367 9357055575037022413064051)
            ·
              refine ⟨14035583362555533619596077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9357055575037022413064051 14035583362555533619596077)
              ·
                refine ⟨5263343760958325107348529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14035583362555533619596077 5263343760958325107348529)
                ·
                  refine ⟨3947507820718743830511397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5263343760958325107348529 3947507820718743830511397)
                  ·
                    refine ⟨740157716384764468220887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3947507820718743830511397 740157716384764468220887)
                    ·
                      rfl

theorem cell22_2162178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 1, 3, 2, 4].length) (baseStart_2162178 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2162178 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2162178 prefixEnd_2162178 := by exact prefixLift 2162178
  have htrace : WordTrace (prefixWord ++ tailWord_2162178) baseStart_2162178 baseEnd_2162178 := by
    simpa [prefixWord, tailWord_2162178, baseEnd_2162178] using wordTrace_append hprefix tailTrace_2162178
  have hstable : (prefixWord ++ tailWord_2162178).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2162178).length < 2 ^ (prefixWord ++ tailWord_2162178).sum := by decide
  have hdescent : baseEnd_2162178 < baseStart_2162178 := by decide
  rcases family_descends (prefixWord ++ tailWord_2162178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2162281 : List Nat := [1, 2, 1, 1, 1, 4, 5, 1, 1, 5]
def baseStart_2162281 : Nat := 118140960795 + 2162281 * 2 ^ 59
def prefixEnd_2162281 : Nat := 4983230072969 + 3 ^ 40 * 2162281 * 2
def baseEnd_2162281 : Nat := 740192975389706532895571

theorem tailTrace_2162281 : CollatzResearch.WordTrace tailWord_2162281 prefixEnd_2162281 740192975389706532895571 := by
  unfold tailWord_2162281
  simp only [CollatzResearch.WordTrace]
  refine ⟨78864867079432700039374697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52576578052955133359583131 78864867079432700039374697)
  ·
    refine ⟨59148650309574525029531023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78864867079432700039374697 59148650309574525029531023)
    ·
      refine ⟨88722975464361787544296535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59148650309574525029531023 88722975464361787544296535)
      ·
        refine ⟨133084463196542681316444803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88722975464361787544296535 133084463196542681316444803)
        ·
          refine ⟨199626694794814021974667205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 133084463196542681316444803 199626694794814021974667205)
          ·
            refine ⟨37430005274027629120250101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 199626694794814021974667205 37430005274027629120250101)
            ·
              refine ⟨3509062994440090230023447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 37430005274027629120250101 3509062994440090230023447)
              ·
                refine ⟨5263594491660135345035171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3509062994440090230023447 5263594491660135345035171)
                ·
                  refine ⟨7895391737490203017552757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5263594491660135345035171 7895391737490203017552757)
                  ·
                    refine ⟨740192975389706532895571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7895391737490203017552757 740192975389706532895571)
                    ·
                      rfl

theorem cell22_2162281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 5, 1, 1, 5].length) (baseStart_2162281 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2162281 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2162281 prefixEnd_2162281 := by exact prefixLift 2162281
  have htrace : WordTrace (prefixWord ++ tailWord_2162281) baseStart_2162281 baseEnd_2162281 := by
    simpa [prefixWord, tailWord_2162281, baseEnd_2162281] using wordTrace_append hprefix tailTrace_2162281
  have hstable : (prefixWord ++ tailWord_2162281).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2162281).length < 2 ^ (prefixWord ++ tailWord_2162281).sum := by decide
  have hdescent : baseEnd_2162281 < baseStart_2162281 := by decide
  rcases family_descends (prefixWord ++ tailWord_2162281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2162285 : List Nat := [1, 5, 1, 1, 4, 1, 2, 2, 1, 4]
def baseStart_2162285 : Nat := 118140960795 + 2162285 * 2 ^ 59
def prefixEnd_2162285 : Nat := 4983230072969 + 3 ^ 40 * 2162285 * 2
def baseEnd_2162285 : Nat := 740194344671451855795559

theorem tailTrace_2162285 : CollatzResearch.WordTrace tailWord_2162285 prefixEnd_2162285 740194344671451855795559 := by
  unfold tailWord_2162285
  simp only [CollatzResearch.WordTrace]
  refine ⟨78865012971418208722520309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52576675314278805815013539 78865012971418208722520309)
  ·
    refine ⟨7393594966070457067736279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 78865012971418208722520309 7393594966070457067736279)
    ·
      refine ⟨11090392449105685601604419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7393594966070457067736279 11090392449105685601604419)
      ·
        refine ⟨16635588673658528402406629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11090392449105685601604419 16635588673658528402406629)
        ·
          refine ⟨3119172876310974075451243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16635588673658528402406629 3119172876310974075451243)
          ·
            refine ⟨4678759314466461113176865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3119172876310974075451243 4678759314466461113176865)
            ·
              refine ⟨3509069485849845834882649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4678759314466461113176865 3509069485849845834882649)
              ·
                refine ⟨2631802114387384376161987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3509069485849845834882649 2631802114387384376161987)
                ·
                  refine ⟨3947703171581076564242981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2631802114387384376161987 3947703171581076564242981)
                  ·
                    refine ⟨740194344671451855795559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3947703171581076564242981 740194344671451855795559)
                    ·
                      rfl

theorem cell22_2162285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 2, 2, 1, 4].length) (baseStart_2162285 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2162285 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2162285 prefixEnd_2162285 := by exact prefixLift 2162285
  have htrace : WordTrace (prefixWord ++ tailWord_2162285) baseStart_2162285 baseEnd_2162285 := by
    simpa [prefixWord, tailWord_2162285, baseEnd_2162285] using wordTrace_append hprefix tailTrace_2162285
  have hstable : (prefixWord ++ tailWord_2162285).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2162285).length < 2 ^ (prefixWord ++ tailWord_2162285).sum := by decide
  have hdescent : baseEnd_2162285 < baseStart_2162285 := by decide
  rcases family_descends (prefixWord ++ tailWord_2162285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2162311 : List Nat := [1, 1, 4, 2, 1, 5, 8]
def baseStart_2162311 : Nat := 118140960795 + 2162311 * 2 ^ 59
def prefixEnd_2162311 : Nat := 4983230072969 + 3 ^ 40 * 2162311 * 2
def baseEnd_2162311 : Nat := 27414935000103572394277

theorem tailTrace_2162311 : CollatzResearch.WordTrace tailWord_2162311 prefixEnd_2162311 27414935000103572394277 := by
  unfold tailWord_2162311
  simp only [CollatzResearch.WordTrace]
  refine ⟨78865961269324015162966787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52577307512882676775311191 78865961269324015162966787)
  ·
    refine ⟨118298941903986022744450181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78865961269324015162966787 118298941903986022744450181)
    ·
      refine ⟨22181051606997379264584409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 118298941903986022744450181 22181051606997379264584409)
      ·
        refine ⟨16635788705248034448438307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22181051606997379264584409 16635788705248034448438307)
        ·
          refine ⟨24953683057872051672657461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16635788705248034448438307 24953683057872051672657461)
          ·
            refine ⟨2339407786675504844311637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 24953683057872051672657461 2339407786675504844311637)
            ·
              refine ⟨27414935000103572394277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2339407786675504844311637 27414935000103572394277)
              ·
                rfl

theorem cell22_2162311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 5, 8].length) (baseStart_2162311 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2162311 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2162311 prefixEnd_2162311 := by exact prefixLift 2162311
  have htrace : WordTrace (prefixWord ++ tailWord_2162311) baseStart_2162311 baseEnd_2162311 := by
    simpa [prefixWord, tailWord_2162311, baseEnd_2162311] using wordTrace_append hprefix tailTrace_2162311
  have hstable : (prefixWord ++ tailWord_2162311).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2162311).length < 2 ^ (prefixWord ++ tailWord_2162311).sum := by decide
  have hdescent : baseEnd_2162311 < baseStart_2162311 := by decide
  rcases family_descends (prefixWord ++ tailWord_2162311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2162388 : List Nat := [2, 4, 1, 3, 1, 1, 1, 1, 1, 7]
def baseStart_2162388 : Nat := 118140960795 + 2162388 * 2 ^ 59
def prefixEnd_2162388 : Nat := 4983230072969 + 3 ^ 40 * 2162388 * 2
def baseEnd_2162388 : Nat := 740229603676393920470243

theorem tailTrace_2162388 : CollatzResearch.WordTrace tailWord_2162388 prefixEnd_2162388 740229603676393920470243 := by
  unfold tailWord_2162388
  simp only [CollatzResearch.WordTrace]
  refine ⟨39434384845022528656759909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52579179793363371542346545 39434384845022528656759909)
  ·
    refine ⟨7393947158441724123142483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 39434384845022528656759909 7393947158441724123142483)
    ·
      refine ⟨11090920737662586184713725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7393947158441724123142483 11090920737662586184713725)
      ·
        refine ⟨4159095276623469819267647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11090920737662586184713725 4159095276623469819267647)
        ·
          refine ⟨6238642914935204728901471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4159095276623469819267647 6238642914935204728901471)
          ·
            refine ⟨9357964372402807093352207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6238642914935204728901471 9357964372402807093352207)
            ·
              refine ⟨14036946558604210640028311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9357964372402807093352207 14036946558604210640028311)
              ·
                refine ⟨21055419837906315960042467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14036946558604210640028311 21055419837906315960042467)
                ·
                  refine ⟨31583129756859473940063701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21055419837906315960042467 31583129756859473940063701)
                  ·
                    refine ⟨740229603676393920470243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 31583129756859473940063701 740229603676393920470243)
                    ·
                      rfl

theorem cell22_2162388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 1, 1, 1, 7].length) (baseStart_2162388 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2162388 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2162388 prefixEnd_2162388 := by exact prefixLift 2162388
  have htrace : WordTrace (prefixWord ++ tailWord_2162388) baseStart_2162388 baseEnd_2162388 := by
    simpa [prefixWord, tailWord_2162388, baseEnd_2162388] using wordTrace_append hprefix tailTrace_2162388
  have hstable : (prefixWord ++ tailWord_2162388).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2162388).length < 2 ^ (prefixWord ++ tailWord_2162388).sum := by decide
  have hdescent : baseEnd_2162388 < baseStart_2162388 := by decide
  rcases family_descends (prefixWord ++ tailWord_2162388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2162416 : List Nat := [2, 1, 1, 1, 3, 1, 2, 3, 3, 5]
def baseStart_2162416 : Nat := 118140960795 + 2162416 * 2 ^ 59
def prefixEnd_2162416 : Nat := 4983230072969 + 3 ^ 40 * 2162416 * 2
def baseEnd_2162416 : Nat := 740239188648611180770157

theorem tailTrace_2162416 : CollatzResearch.WordTrace tailWord_2162416 prefixEnd_2162416 740239188648611180770157 := by
  unfold tailWord_2162416
  simp only [CollatzResearch.WordTrace]
  refine ⟨39434895466971809047769551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52579860622629078730359401 39434895466971809047769551)
  ·
    refine ⟨59152343200457713571654327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39434895466971809047769551 59152343200457713571654327)
    ·
      refine ⟨88728514800686570357481491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59152343200457713571654327 88728514800686570357481491)
      ·
        refine ⟨133092772201029855536222237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88728514800686570357481491 133092772201029855536222237)
        ·
          refine ⟨49909789575386195826083339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 133092772201029855536222237 49909789575386195826083339)
          ·
            refine ⟨74864684363079293739125009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49909789575386195826083339 74864684363079293739125009)
            ·
              refine ⟨56148513272309470304343757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 74864684363079293739125009 56148513272309470304343757)
              ·
                refine ⟨21055692477116051364128909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 56148513272309470304343757 21055692477116051364128909)
                ·
                  refine ⟨7895884678918519261548341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21055692477116051364128909 7895884678918519261548341)
                  ·
                    refine ⟨740239188648611180770157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7895884678918519261548341 740239188648611180770157)
                    ·
                      rfl

theorem cell22_2162416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 3, 3, 5].length) (baseStart_2162416 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2162416 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2162416 prefixEnd_2162416 := by exact prefixLift 2162416
  have htrace : WordTrace (prefixWord ++ tailWord_2162416) baseStart_2162416 baseEnd_2162416 := by
    simpa [prefixWord, tailWord_2162416, baseEnd_2162416] using wordTrace_append hprefix tailTrace_2162416
  have hstable : (prefixWord ++ tailWord_2162416).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2162416).length < 2 ^ (prefixWord ++ tailWord_2162416).sum := by decide
  have hdescent : baseEnd_2162416 < baseStart_2162416 := by decide
  rcases family_descends (prefixWord ++ tailWord_2162416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2162542 : List Nat := [4, 1, 2, 3, 1, 2, 2, 2, 5]
def baseStart_2162542 : Nat := 118140960795 + 2162542 * 2 ^ 59
def prefixEnd_2162542 : Nat := 4983230072969 + 3 ^ 40 * 2162542 * 2
def baseEnd_2162542 : Nat := 246760773674529617373257

theorem tailTrace_2162542 : CollatzResearch.WordTrace tailWord_2162542 prefixEnd_2162542 246760773674529617373257 := by
  unfold tailWord_2162542
  simp only [CollatzResearch.WordTrace]
  refine ⟨9859298316435892701828235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 52582924354324761076417253 9859298316435892701828235)
  ·
    refine ⟨14788947474653839052742353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9859298316435892701828235 14788947474653839052742353)
    ·
      refine ⟨11091710605990379289556765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14788947474653839052742353 11091710605990379289556765)
      ·
        refine ⟨4159391477246392233583787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11091710605990379289556765 4159391477246392233583787)
        ·
          refine ⟨6239087215869588350375681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4159391477246392233583787 6239087215869588350375681)
          ·
            refine ⟨4679315411902191262781761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6239087215869588350375681 4679315411902191262781761)
            ·
              refine ⟨3509486558926643447086321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4679315411902191262781761 3509486558926643447086321)
              ·
                refine ⟨2632114919194982585314741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3509486558926643447086321 2632114919194982585314741)
                ·
                  refine ⟨246760773674529617373257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2632114919194982585314741 246760773674529617373257)
                  ·
                    rfl

theorem cell22_2162542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 2, 2, 5].length) (baseStart_2162542 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2162542 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2162542 prefixEnd_2162542 := by exact prefixLift 2162542
  have htrace : WordTrace (prefixWord ++ tailWord_2162542) baseStart_2162542 baseEnd_2162542 := by
    simpa [prefixWord, tailWord_2162542, baseEnd_2162542] using wordTrace_append hprefix tailTrace_2162542
  have hstable : (prefixWord ++ tailWord_2162542).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2162542).length < 2 ^ (prefixWord ++ tailWord_2162542).sum := by decide
  have hdescent : baseEnd_2162542 < baseStart_2162542 := by decide
  rcases family_descends (prefixWord ++ tailWord_2162542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2162553 : List Nat := [1, 2, 1, 3, 2, 2, 2, 3, 6]
def baseStart_2162553 : Nat := 118140960795 + 2162553 * 2 ^ 59
def prefixEnd_2162553 : Nat := 4983230072969 + 3 ^ 40 * 2162553 * 2
def baseEnd_2162553 : Nat := 246762028849462830031579

theorem tailTrace_2162553 : CollatzResearch.WordTrace tailWord_2162553 prefixEnd_2162553 246762028849462830031579 := by
  unfold tailWord_2162553
  simp only [CollatzResearch.WordTrace]
  refine ⟨78874787734447290493276313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52583191822964860328850875 78874787734447290493276313)
  ·
    refine ⟨59156090800835467869957235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78874787734447290493276313 59156090800835467869957235)
    ·
      refine ⟨88734136201253201804935853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59156090800835467869957235 88734136201253201804935853)
      ·
        refine ⟨33275301075469950676850945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 88734136201253201804935853 33275301075469950676850945)
        ·
          refine ⟨24956475806602463007638209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33275301075469950676850945 24956475806602463007638209)
          ·
            refine ⟨18717356854951847255728657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24956475806602463007638209 18717356854951847255728657)
            ·
              refine ⟨14038017641213885441796493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18717356854951847255728657 14038017641213885441796493)
              ·
                refine ⟨5264256615455207040673685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14038017641213885441796493 5264256615455207040673685)
                ·
                  refine ⟨246762028849462830031579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5264256615455207040673685 246762028849462830031579)
                  ·
                    rfl

theorem cell22_2162553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 2, 3, 6].length) (baseStart_2162553 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2162553 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2162553 prefixEnd_2162553 := by exact prefixLift 2162553
  have htrace : WordTrace (prefixWord ++ tailWord_2162553) baseStart_2162553 baseEnd_2162553 := by
    simpa [prefixWord, tailWord_2162553, baseEnd_2162553] using wordTrace_append hprefix tailTrace_2162553
  have hstable : (prefixWord ++ tailWord_2162553).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2162553).length < 2 ^ (prefixWord ++ tailWord_2162553).sum := by decide
  have hdescent : baseEnd_2162553 < baseStart_2162553 := by decide
  rcases family_descends (prefixWord ++ tailWord_2162553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2162589 : List Nat := [1, 4, 2, 1, 2, 4, 2, 1, 1, 4]
def baseStart_2162589 : Nat := 118140960795 + 2162589 * 2 ^ 59
def prefixEnd_2162589 : Nat := 4983230072969 + 3 ^ 40 * 2162589 * 2
def baseEnd_2162589 : Nat := 740298410084096396194627

theorem tailTrace_2162589 : CollatzResearch.WordTrace tailWord_2162589 prefixEnd_2162589 740298410084096396194627 := by
  unfold tailWord_2162589
  simp only [CollatzResearch.WordTrace]
  refine ⟨78876100762316868641586821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52584067174877912427724547 78876100762316868641586821)
  ·
    refine ⟨14789268892934412870297529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 78876100762316868641586821 14789268892934412870297529)
    ·
      refine ⟨11091951669700809652723147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14789268892934412870297529 11091951669700809652723147)
      ·
        refine ⟨16637927504551214479084721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11091951669700809652723147 16637927504551214479084721)
        ·
          refine ⟨12478445628413410859313541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16637927504551214479084721 12478445628413410859313541)
          ·
            refine ⟨2339708555327514536121289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12478445628413410859313541 2339708555327514536121289)
            ·
              refine ⟨1754781416495635902090967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2339708555327514536121289 1754781416495635902090967)
              ·
                refine ⟨2632172124743453853136451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1754781416495635902090967 2632172124743453853136451)
                ·
                  refine ⟨3948258187115180779704677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2632172124743453853136451 3948258187115180779704677)
                  ·
                    refine ⟨740298410084096396194627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3948258187115180779704677 740298410084096396194627)
                    ·
                      rfl

theorem cell22_2162589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 4, 2, 1, 1, 4].length) (baseStart_2162589 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2162589 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2162589 prefixEnd_2162589 := by exact prefixLift 2162589
  have htrace : WordTrace (prefixWord ++ tailWord_2162589) baseStart_2162589 baseEnd_2162589 := by
    simpa [prefixWord, tailWord_2162589, baseEnd_2162589] using wordTrace_append hprefix tailTrace_2162589
  have hstable : (prefixWord ++ tailWord_2162589).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2162589).length < 2 ^ (prefixWord ++ tailWord_2162589).sum := by decide
  have hdescent : baseEnd_2162589 < baseStart_2162589 := by decide
  rcases family_descends (prefixWord ++ tailWord_2162589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2162632 : List Nat := [2, 1, 3, 1, 4, 3, 2, 6]
def baseStart_2162632 : Nat := 118140960795 + 2162632 * 2 ^ 59
def prefixEnd_2162632 : Nat := 4983230072969 + 3 ^ 40 * 2162632 * 2
def baseEnd_2162632 : Nat := 82257014429206513041055

theorem tailTrace_2162632 : CollatzResearch.WordTrace tailWord_2162632 prefixEnd_2162632 82257014429206513041055 := by
  unfold tailWord_2162632
  simp only [CollatzResearch.WordTrace]
  refine ⟨39438834550580543492701075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52585112734107391323601433 39438834550580543492701075)
  ·
    refine ⟨59158251825870815239051613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39438834550580543492701075 59158251825870815239051613)
    ·
      refine ⟨22184344434701555714644355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 59158251825870815239051613 22184344434701555714644355)
      ·
        refine ⟨33276516652052333571966533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22184344434701555714644355 33276516652052333571966533)
        ·
          refine ⟨6239346872259812544743725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 33276516652052333571966533 6239346872259812544743725)
          ·
            refine ⟨2339755077097429704278897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6239346872259812544743725 2339755077097429704278897)
            ·
              refine ⟨1754816307823072278209173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2339755077097429704278897 1754816307823072278209173)
              ·
                refine ⟨82257014429206513041055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1754816307823072278209173 82257014429206513041055)
                ·
                  rfl

theorem cell22_2162632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 3, 2, 6].length) (baseStart_2162632 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2162632 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2162632 prefixEnd_2162632 := by exact prefixLift 2162632
  have htrace : WordTrace (prefixWord ++ tailWord_2162632) baseStart_2162632 baseEnd_2162632 := by
    simpa [prefixWord, tailWord_2162632, baseEnd_2162632] using wordTrace_append hprefix tailTrace_2162632
  have hstable : (prefixWord ++ tailWord_2162632).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2162632).length < 2 ^ (prefixWord ++ tailWord_2162632).sum := by decide
  have hdescent : baseEnd_2162632 < baseStart_2162632 := by decide
  rcases family_descends (prefixWord ++ tailWord_2162632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2162660 : List Nat := [2, 3, 1, 1, 1, 1, 4, 4, 5]
def baseStart_2162660 : Nat := 118140960795 + 2162660 * 2 ^ 59
def prefixEnd_2162660 : Nat := 4983230072969 + 3 ^ 40 * 2162660 * 2
def baseEnd_2162660 : Nat := 246774238278358625889803

theorem tailTrace_2162660 : CollatzResearch.WordTrace tailWord_2162660 prefixEnd_2162660 246774238278358625889803 := by
  unfold tailWord_2162660
  simp only [CollatzResearch.WordTrace]
  refine ⟨39439345172529823883710717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52585793563373098511614289 39439345172529823883710717)
  ·
    refine ⟨14789754439698683956391519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39439345172529823883710717 14789754439698683956391519)
    ·
      refine ⟨22184631659548025934587279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14789754439698683956391519 22184631659548025934587279)
      ·
        refine ⟨33276947489322038901880919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22184631659548025934587279 33276947489322038901880919)
        ·
          refine ⟨49915421233983058352821379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33276947489322038901880919 49915421233983058352821379)
          ·
            refine ⟨74873131850974587529232069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49915421233983058352821379 74873131850974587529232069)
            ·
              refine ⟨14038712222057735161731013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 74873131850974587529232069 14038712222057735161731013)
              ·
                refine ⟨2632258541635825342824565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14038712222057735161731013 2632258541635825342824565)
                ·
                  refine ⟨246774238278358625889803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2632258541635825342824565 246774238278358625889803)
                  ·
                    rfl

theorem cell22_2162660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 4, 4, 5].length) (baseStart_2162660 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2162660 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2162660 prefixEnd_2162660 := by exact prefixLift 2162660
  have htrace : WordTrace (prefixWord ++ tailWord_2162660) baseStart_2162660 baseEnd_2162660 := by
    simpa [prefixWord, tailWord_2162660, baseEnd_2162660] using wordTrace_append hprefix tailTrace_2162660
  have hstable : (prefixWord ++ tailWord_2162660).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2162660).length < 2 ^ (prefixWord ++ tailWord_2162660).sum := by decide
  have hdescent : baseEnd_2162660 < baseStart_2162660 := by decide
  rcases family_descends (prefixWord ++ tailWord_2162660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2162737 : List Nat := [1, 2, 2, 3, 1, 4, 2, 1, 1, 5]
def baseStart_2162737 : Nat := 118140960795 + 2162737 * 2 ^ 59
def prefixEnd_2162737 : Nat := 4983230072969 + 3 ^ 40 * 2162737 * 2
def baseEnd_2162737 : Nat := 740349073508673343494173

theorem tailTrace_2162737 : CollatzResearch.WordTrace tailWord_2162737 prefixEnd_2162737 740349073508673343494173 := by
  unfold tailWord_2162737
  simp only [CollatzResearch.WordTrace]
  refine ⟨78881498765780689917974465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52587665843853793278649643 78881498765780689917974465)
  ·
    refine ⟨59161124074335517438480849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78881498765780689917974465 59161124074335517438480849)
    ·
      refine ⟨44370843055751638078860637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59161124074335517438480849 44370843055751638078860637)
      ·
        refine ⟨16639066145906864279572739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44370843055751638078860637 16639066145906864279572739)
        ·
          refine ⟨24958599218860296419359109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16639066145906864279572739 24958599218860296419359109)
          ·
            refine ⟨4679737353536305578629833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24958599218860296419359109 4679737353536305578629833)
            ·
              refine ⟨3509803015152229183972375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4679737353536305578629833 3509803015152229183972375)
              ·
                refine ⟨5264704522728343775958563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3509803015152229183972375 5264704522728343775958563)
                ·
                  refine ⟨7897056784092515663937845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5264704522728343775958563 7897056784092515663937845)
                  ·
                    refine ⟨740349073508673343494173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7897056784092515663937845 740349073508673343494173)
                    ·
                      rfl

theorem cell22_2162737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 2, 1, 1, 5].length) (baseStart_2162737 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2162737 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2162737 prefixEnd_2162737 := by exact prefixLift 2162737
  have htrace : WordTrace (prefixWord ++ tailWord_2162737) baseStart_2162737 baseEnd_2162737 := by
    simpa [prefixWord, tailWord_2162737, baseEnd_2162737] using wordTrace_append hprefix tailTrace_2162737
  have hstable : (prefixWord ++ tailWord_2162737).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2162737).length < 2 ^ (prefixWord ++ tailWord_2162737).sum := by decide
  have hdescent : baseEnd_2162737 < baseStart_2162737 := by decide
  rcases family_descends (prefixWord ++ tailWord_2162737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2162752 : List Nat := [2, 1, 1, 2, 2, 4, 3, 1, 2, 4]
def baseStart_2162752 : Nat := 118140960795 + 2162752 * 2 ^ 59
def prefixEnd_2162752 : Nat := 4983230072969 + 3 ^ 40 * 2162752 * 2
def baseEnd_2162752 : Nat := 740354208315218304369127

theorem tailTrace_2162752 : CollatzResearch.WordTrace tailWord_2162752 prefixEnd_2162752 740354208315218304369127 := by
  unfold tailWord_2162752
  simp only [CollatzResearch.WordTrace]
  refine ⟨39441022930363173739885255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52588030573817564986513673 39441022930363173739885255)
  ·
    refine ⟨59161534395544760609827883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39441022930363173739885255 59161534395544760609827883)
    ·
      refine ⟨88742301593317140914741825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59161534395544760609827883 88742301593317140914741825)
      ·
        refine ⟨66556726194987855686056369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 88742301593317140914741825 66556726194987855686056369)
        ·
          refine ⟨49917544646240891764542277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66556726194987855686056369 49917544646240891764542277)
          ·
            refine ⟨9359539621170167205851677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 49917544646240891764542277 9359539621170167205851677)
            ·
              refine ⟨3509827357938812702194379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9359539621170167205851677 3509827357938812702194379)
              ·
                refine ⟨5264741036908219053291569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3509827357938812702194379 5264741036908219053291569)
                ·
                  refine ⟨3948555777681164289968677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5264741036908219053291569 3948555777681164289968677)
                  ·
                    refine ⟨740354208315218304369127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3948555777681164289968677 740354208315218304369127)
                    ·
                      rfl

theorem cell22_2162752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 3, 1, 2, 4].length) (baseStart_2162752 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2162752 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2162752 prefixEnd_2162752 := by exact prefixLift 2162752
  have htrace : WordTrace (prefixWord ++ tailWord_2162752) baseStart_2162752 baseEnd_2162752 := by
    simpa [prefixWord, tailWord_2162752, baseEnd_2162752] using wordTrace_append hprefix tailTrace_2162752
  have hstable : (prefixWord ++ tailWord_2162752).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2162752).length < 2 ^ (prefixWord ++ tailWord_2162752).sum := by decide
  have hdescent : baseEnd_2162752 < baseStart_2162752 := by decide
  rcases family_descends (prefixWord ++ tailWord_2162752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2162846 : List Nat := [4, 3, 1, 1, 3, 1, 1, 3, 5]
def baseStart_2162846 : Nat := 118140960795 + 2162846 * 2 ^ 59
def prefixEnd_2162846 : Nat := 4983230072969 + 3 ^ 40 * 2162846 * 2
def baseEnd_2162846 : Nat := 246795462145411130839613

theorem tailTrace_2162846 : CollatzResearch.WordTrace tailWord_2162846 prefixEnd_2162846 246795462145411130839613 := by
  unfold tailWord_2162846
  simp only [CollatzResearch.WordTrace]
  refine ⟨9860684290298225191711549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 52590316214923867689128261 9860684290298225191711549)
  ·
    refine ⟨3697756608861834446891831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9860684290298225191711549 3697756608861834446891831)
    ·
      refine ⟨5546634913292751670337747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3697756608861834446891831 5546634913292751670337747)
      ·
        refine ⟨8319952369939127505506621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5546634913292751670337747 8319952369939127505506621)
        ·
          refine ⟨3119982138727172814564983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8319952369939127505506621 3119982138727172814564983)
          ·
            refine ⟨4679973208090759221847475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3119982138727172814564983 4679973208090759221847475)
            ·
              refine ⟨7019959812136138832771213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4679973208090759221847475 7019959812136138832771213)
              ·
                refine ⟨2632484929551052062289205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7019959812136138832771213 2632484929551052062289205)
                ·
                  refine ⟨246795462145411130839613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2632484929551052062289205 246795462145411130839613)
                  ·
                    rfl

theorem cell22_2162846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 1, 3, 5].length) (baseStart_2162846 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2162846 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2162846 prefixEnd_2162846 := by exact prefixLift 2162846
  have htrace : WordTrace (prefixWord ++ tailWord_2162846) baseStart_2162846 baseEnd_2162846 := by
    simpa [prefixWord, tailWord_2162846, baseEnd_2162846] using wordTrace_append hprefix tailTrace_2162846
  have hstable : (prefixWord ++ tailWord_2162846).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2162846).length < 2 ^ (prefixWord ++ tailWord_2162846).sum := by decide
  have hdescent : baseEnd_2162846 < baseStart_2162846 := by decide
  rcases family_descends (prefixWord ++ tailWord_2162846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2162872 : List Nat := [2, 1, 2, 1, 2, 1, 5, 2, 1, 5]
def baseStart_2162872 : Nat := 118140960795 + 2162872 * 2 ^ 59
def prefixEnd_2162872 : Nat := 4983230072969 + 3 ^ 40 * 2162872 * 2
def baseEnd_2162872 : Nat := 740395286767577991368759

theorem tailTrace_2162872 : CollatzResearch.WordTrace tailWord_2162872 prefixEnd_2162872 740395286767577991368759 := by
  unfold tailWord_2162872
  simp only [CollatzResearch.WordTrace]
  refine ⟨39443211310145803987069435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52590948413527738649425913 39443211310145803987069435)
  ·
    refine ⟨59164816965218705980604153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39443211310145803987069435 59164816965218705980604153)
    ·
      refine ⟨44373612723914029485453115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59164816965218705980604153 44373612723914029485453115)
      ·
        refine ⟨66560419085871044228179673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44373612723914029485453115 66560419085871044228179673)
        ·
          refine ⟨49920314314403283171134755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66560419085871044228179673 49920314314403283171134755)
          ·
            refine ⟨74880471471604924756702133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49920314314403283171134755 74880471471604924756702133)
            ·
              refine ⟨7020044200462961695940825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 74880471471604924756702133 7020044200462961695940825)
              ·
                refine ⟨5265033150347221271955619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7020044200462961695940825 5265033150347221271955619)
                ·
                  refine ⟨7897549725520831907933429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5265033150347221271955619 7897549725520831907933429)
                  ·
                    refine ⟨740395286767577991368759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7897549725520831907933429 740395286767577991368759)
                    ·
                      rfl

theorem cell22_2162872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 5, 2, 1, 5].length) (baseStart_2162872 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2162872 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2162872 prefixEnd_2162872 := by exact prefixLift 2162872
  have htrace : WordTrace (prefixWord ++ tailWord_2162872) baseStart_2162872 baseEnd_2162872 := by
    simpa [prefixWord, tailWord_2162872, baseEnd_2162872] using wordTrace_append hprefix tailTrace_2162872
  have hstable : (prefixWord ++ tailWord_2162872).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2162872).length < 2 ^ (prefixWord ++ tailWord_2162872).sum := by decide
  have hdescent : baseEnd_2162872 < baseStart_2162872 := by decide
  rcases family_descends (prefixWord ++ tailWord_2162872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2162947 : List Nat := [1, 1, 1, 3, 2, 3, 3, 1, 7]
def baseStart_2162947 : Nat := 118140960795 + 2162947 * 2 ^ 59
def prefixEnd_2162947 : Nat := 4983230072969 + 3 ^ 40 * 2162947 * 2
def baseEnd_2162947 : Nat := 246806986933434265247843

theorem tailTrace_2162947 : CollatzResearch.WordTrace tailWord_2162947 prefixEnd_2162947 246806986933434265247843 := by
  unfold tailWord_2162947
  simp only [CollatzResearch.WordTrace]
  refine ⟨78889158095019895783119095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52592772063346597188746063 78889158095019895783119095)
  ·
    refine ⟨118333737142529843674678643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78889158095019895783119095 118333737142529843674678643)
    ·
      refine ⟨177500605713794765512017965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118333737142529843674678643 177500605713794765512017965)
      ·
        refine ⟨66562727142673037067006737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 177500605713794765512017965 66562727142673037067006737)
        ·
          refine ⟨49922045357004777800255053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66562727142673037067006737 49922045357004777800255053)
          ·
            refine ⟨18720767008876791675095645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 49922045357004777800255053 18720767008876791675095645)
            ·
              refine ⟨7020287628328796878160867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18720767008876791675095645 7020287628328796878160867)
              ·
                refine ⟨10530431442493195317241301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7020287628328796878160867 10530431442493195317241301)
                ·
                  refine ⟨246806986933434265247843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10530431442493195317241301 246806986933434265247843)
                  ·
                    rfl

theorem cell22_2162947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 3, 1, 7].length) (baseStart_2162947 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2162947 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2162947 prefixEnd_2162947 := by exact prefixLift 2162947
  have htrace : WordTrace (prefixWord ++ tailWord_2162947) baseStart_2162947 baseEnd_2162947 := by
    simpa [prefixWord, tailWord_2162947, baseEnd_2162947] using wordTrace_append hprefix tailTrace_2162947
  have hstable : (prefixWord ++ tailWord_2162947).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2162947).length < 2 ^ (prefixWord ++ tailWord_2162947).sum := by decide
  have hdescent : baseEnd_2162947 < baseStart_2162947 := by decide
  rcases family_descends (prefixWord ++ tailWord_2162947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2163028 : List Nat := [2, 4, 1, 1, 2, 4, 1, 2, 1, 4]
def baseStart_2163028 : Nat := 118140960795 + 2163028 * 2 ^ 59
def prefixEnd_2163028 : Nat := 4983230072969 + 3 ^ 40 * 2163028 * 2
def baseEnd_2163028 : Nat := 740448688755645584468281

theorem tailTrace_2163028 : CollatzResearch.WordTrace tailWord_2163028 prefixEnd_2163028 740448688755645584468281 := by
  unfold tailWord_2163028
  simp only [CollatzResearch.WordTrace]
  refine ⟨39446056203863223308408869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52594741605150964411211825 39446056203863223308408869)
  ·
    refine ⟨7396135538224354370326663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 39446056203863223308408869 7396135538224354370326663)
    ·
      refine ⟨11094203307336531555489995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7396135538224354370326663 11094203307336531555489995)
      ·
        refine ⟨16641304961004797333234993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11094203307336531555489995 16641304961004797333234993)
        ·
          refine ⟨12480978720753597999926245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16641304961004797333234993 12480978720753597999926245)
          ·
            refine ⟨2340183510141299624986171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12480978720753597999926245 2340183510141299624986171)
            ·
              refine ⟨3510275265211949437479257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2340183510141299624986171 3510275265211949437479257)
              ·
                refine ⟨2632706448908962078109443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3510275265211949437479257 2632706448908962078109443)
                ·
                  refine ⟨3949059673363443117164165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2632706448908962078109443 3949059673363443117164165)
                  ·
                    refine ⟨740448688755645584468281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3949059673363443117164165 740448688755645584468281)
                    ·
                      rfl

theorem cell22_2163028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 4, 1, 2, 1, 4].length) (baseStart_2163028 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2163028 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2163028 prefixEnd_2163028 := by exact prefixLift 2163028
  have htrace : WordTrace (prefixWord ++ tailWord_2163028) baseStart_2163028 baseEnd_2163028 := by
    simpa [prefixWord, tailWord_2163028, baseEnd_2163028] using wordTrace_append hprefix tailTrace_2163028
  have hstable : (prefixWord ++ tailWord_2163028).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2163028).length < 2 ^ (prefixWord ++ tailWord_2163028).sum := by decide
  have hdescent : baseEnd_2163028 < baseStart_2163028 := by decide
  rcases family_descends (prefixWord ++ tailWord_2163028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2163039 : List Nat := [1, 1, 2, 3, 1, 2, 3, 3, 2, 4]
def baseStart_2163039 : Nat := 118140960795 + 2163039 * 2 ^ 59
def prefixEnd_2163039 : Nat := 4983230072969 + 3 ^ 40 * 2163039 * 2
def baseEnd_2163039 : Nat := 740452454280445222443247

theorem tailTrace_2163039 : CollatzResearch.WordTrace tailWord_2163039 prefixEnd_2163039 740452454280445222443247 := by
  unfold tailWord_2163039
  simp only [CollatzResearch.WordTrace]
  refine ⟨78892513610686595495468171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52595009073791063663645447 78892513610686595495468171)
  ·
    refine ⟨118338770416029893243202257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78892513610686595495468171 118338770416029893243202257)
    ·
      refine ⟨88754077812022419932401693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 118338770416029893243202257 88754077812022419932401693)
      ·
        refine ⟨33282779179508407474650635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 88754077812022419932401693 33282779179508407474650635)
        ·
          refine ⟨49924168769262611211975953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33282779179508407474650635 49924168769262611211975953)
          ·
            refine ⟨37443126576946958408981965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49924168769262611211975953 37443126576946958408981965)
            ·
              refine ⟨14041172466355109403368237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37443126576946958408981965 14041172466355109403368237)
              ·
                refine ⟨5265439674883166026263089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14041172466355109403368237 5265439674883166026263089)
                ·
                  refine ⟨3949079756162374519697317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5265439674883166026263089 3949079756162374519697317)
                  ·
                    refine ⟨740452454280445222443247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3949079756162374519697317 740452454280445222443247)
                    ·
                      rfl

theorem cell22_2163039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 3, 3, 2, 4].length) (baseStart_2163039 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2163039 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2163039 prefixEnd_2163039 := by exact prefixLift 2163039
  have htrace : WordTrace (prefixWord ++ tailWord_2163039) baseStart_2163039 baseEnd_2163039 := by
    simpa [prefixWord, tailWord_2163039, baseEnd_2163039] using wordTrace_append hprefix tailTrace_2163039
  have hstable : (prefixWord ++ tailWord_2163039).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2163039).length < 2 ^ (prefixWord ++ tailWord_2163039).sum := by decide
  have hdescent : baseEnd_2163039 < baseStart_2163039 := by decide
  rcases family_descends (prefixWord ++ tailWord_2163039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2163058 : List Nat := [3, 2, 1, 2, 1, 4, 2, 2, 2, 3]
def baseStart_2163058 : Nat := 118140960795 + 2163058 * 2 ^ 59
def prefixEnd_2163058 : Nat := 4983230072969 + 3 ^ 40 * 2163058 * 2
def baseEnd_2163058 : Nat := 740458958368735506218189

theorem tailTrace_2163058 : CollatzResearch.WordTrace tailWord_2163058 prefixEnd_2163058 740458958368735506218189 := by
  unfold tailWord_2163058
  simp only [CollatzResearch.WordTrace]
  refine ⟨19723301649404440435102457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52595471065078507826939885 19723301649404440435102457)
  ·
    refine ⟨14792476237053330326326843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19723301649404440435102457 14792476237053330326326843)
    ·
      refine ⟨22188714355579995489490265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14792476237053330326326843 22188714355579995489490265)
      ·
        refine ⟨16641535766684996617117699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22188714355579995489490265 16641535766684996617117699)
        ·
          refine ⟨24962303650027494925676549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16641535766684996617117699 24962303650027494925676549)
          ·
            refine ⟨4680431934380155298564353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24962303650027494925676549 4680431934380155298564353)
            ·
              refine ⟨3510323950785116473923265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4680431934380155298564353 3510323950785116473923265)
              ·
                refine ⟨2632742963088837355442449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3510323950785116473923265 2632742963088837355442449)
                ·
                  refine ⟨1974557222316628016581837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2632742963088837355442449 1974557222316628016581837)
                  ·
                    refine ⟨740458958368735506218189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1974557222316628016581837 740458958368735506218189)
                    ·
                      rfl

theorem cell22_2163058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 2, 2, 2, 3].length) (baseStart_2163058 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2163058 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2163058 prefixEnd_2163058 := by exact prefixLift 2163058
  have htrace : WordTrace (prefixWord ++ tailWord_2163058) baseStart_2163058 baseEnd_2163058 := by
    simpa [prefixWord, tailWord_2163058, baseEnd_2163058] using wordTrace_append hprefix tailTrace_2163058
  have hstable : (prefixWord ++ tailWord_2163058).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2163058).length < 2 ^ (prefixWord ++ tailWord_2163058).sum := by decide
  have hdescent : baseEnd_2163058 < baseStart_2163058 := by decide
  rcases family_descends (prefixWord ++ tailWord_2163058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2163094 : List Nat := [5, 3, 1, 2, 1, 1, 2, 3, 4]
def baseStart_2163094 : Nat := 118140960795 + 2163094 * 2 ^ 59
def prefixEnd_2163094 : Nat := 4983230072969 + 3 ^ 40 * 2163094 * 2
def baseEnd_2163094 : Nat := 246823760634814470772693

theorem tailTrace_2163094 : CollatzResearch.WordTrace tailWord_2163094 prefixEnd_2163094 246823760634814470772693 := by
  unfold tailWord_2163094
  simp only [CollatzResearch.WordTrace]
  refine ⟨4930907476592958743045021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 52596346416991559925813557 4930907476592958743045021)
  ·
    refine ⟨1849090303722359528641883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4930907476592958743045021 1849090303722359528641883)
    ·
      refine ⟨2773635455583539292962825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1849090303722359528641883 2773635455583539292962825)
      ·
        refine ⟨2080226591687654469722119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2773635455583539292962825 2080226591687654469722119)
        ·
          refine ⟨3120339887531481704583179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2080226591687654469722119 3120339887531481704583179)
          ·
            refine ⟨4680509831297222556874769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3120339887531481704583179 4680509831297222556874769)
            ·
              refine ⟨3510382373472916917656077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4680509831297222556874769 3510382373472916917656077)
              ·
                refine ⟨1316393390052343844121029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3510382373472916917656077 1316393390052343844121029)
                ·
                  refine ⟨246823760634814470772693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1316393390052343844121029 246823760634814470772693)
                  ·
                    rfl

theorem cell22_2163094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 2, 3, 4].length) (baseStart_2163094 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2163094 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2163094 prefixEnd_2163094 := by exact prefixLift 2163094
  have htrace : WordTrace (prefixWord ++ tailWord_2163094) baseStart_2163094 baseEnd_2163094 := by
    simpa [prefixWord, tailWord_2163094, baseEnd_2163094] using wordTrace_append hprefix tailTrace_2163094
  have hstable : (prefixWord ++ tailWord_2163094).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2163094).length < 2 ^ (prefixWord ++ tailWord_2163094).sum := by decide
  have hdescent : baseEnd_2163094 < baseStart_2163094 := by decide
  rcases family_descends (prefixWord ++ tailWord_2163094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2163133 : List Nat := [1, 4, 1, 2, 2, 3, 3, 1, 5]
def baseStart_2163133 : Nat := 118140960795 + 2163133 * 2 ^ 59
def prefixEnd_2163133 : Nat := 4983230072969 + 3 ^ 40 * 2163133 * 2
def baseEnd_2163133 : Nat := 246828210800486770197653

theorem tailTrace_2163133 : CollatzResearch.WordTrace tailWord_2163133 prefixEnd_2163133 246828210800486770197653 := by
  unfold tailWord_2163133
  simp only [CollatzResearch.WordTrace]
  refine ⟨78895942072346049549390053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52597294714897366366260035 78895942072346049549390053)
  ·
    refine ⟨14792989138564884290510635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 78895942072346049549390053 14792989138564884290510635)
    ·
      refine ⟨22189483707847326435765953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14792989138564884290510635 22189483707847326435765953)
      ·
        refine ⟨16642112780885494826824465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22189483707847326435765953 16642112780885494826824465)
        ·
          refine ⟨12481584585664121120118349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16642112780885494826824465 12481584585664121120118349)
          ·
            refine ⟨4680594219624045420044381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12481584585664121120118349 4680594219624045420044381)
            ·
              refine ⟨1755222832359017032516643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4680594219624045420044381 1755222832359017032516643)
              ·
                refine ⟨2632834248538525548774965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1755222832359017032516643 2632834248538525548774965)
                ·
                  refine ⟨246828210800486770197653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2632834248538525548774965 246828210800486770197653)
                  ·
                    rfl

theorem cell22_2163133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 3, 1, 5].length) (baseStart_2163133 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2163133 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2163133 prefixEnd_2163133 := by exact prefixLift 2163133
  have htrace : WordTrace (prefixWord ++ tailWord_2163133) baseStart_2163133 baseEnd_2163133 := by
    simpa [prefixWord, tailWord_2163133, baseEnd_2163133] using wordTrace_append hprefix tailTrace_2163133
  have hstable : (prefixWord ++ tailWord_2163133).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2163133).length < 2 ^ (prefixWord ++ tailWord_2163133).sum := by decide
  have hdescent : baseEnd_2163133 < baseStart_2163133 := by decide
  rcases family_descends (prefixWord ++ tailWord_2163133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2163154 : List Nat := [3, 2, 2, 4, 1, 2, 1, 3, 1, 3]
def baseStart_2163154 : Nat := 118140960795 + 2163154 * 2 ^ 59
def prefixEnd_2163154 : Nat := 4983230072969 + 3 ^ 40 * 2163154 * 2
def baseEnd_2163154 : Nat := 740491821130623255817895

theorem tailTrace_2163154 : CollatzResearch.WordTrace tailWord_2163154 prefixEnd_2163154 740491821130623255817895 := by
  unfold tailWord_2163154
  simp only [CollatzResearch.WordTrace]
  refine ⟨19724177001317492533976129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52597805336846646757269677 19724177001317492533976129)
  ·
    refine ⟨14793132750988119400482097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19724177001317492533976129 14793132750988119400482097)
    ·
      refine ⟨11094849563241089550361573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14793132750988119400482097 11094849563241089550361573)
      ·
        refine ⟨2080284293107704290692795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11094849563241089550361573 2080284293107704290692795)
        ·
          refine ⟨3120426439661556436039193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2080284293107704290692795 3120426439661556436039193)
          ·
            refine ⟨2340319829746167327029395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3120426439661556436039193 2340319829746167327029395)
            ·
              refine ⟨3510479744619250990544093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2340319829746167327029395 3510479744619250990544093)
              ·
                refine ⟨1316429904232219121454035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3510479744619250990544093 1316429904232219121454035)
                ·
                  refine ⟨1974644856348328682181053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1316429904232219121454035 1974644856348328682181053)
                  ·
                    refine ⟨740491821130623255817895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1974644856348328682181053 740491821130623255817895)
                    ·
                      rfl

theorem cell22_2163154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 2, 1, 3, 1, 3].length) (baseStart_2163154 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2163154 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2163154 prefixEnd_2163154 := by exact prefixLift 2163154
  have htrace : WordTrace (prefixWord ++ tailWord_2163154) baseStart_2163154 baseEnd_2163154 := by
    simpa [prefixWord, tailWord_2163154, baseEnd_2163154] using wordTrace_append hprefix tailTrace_2163154
  have hstable : (prefixWord ++ tailWord_2163154).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2163154).length < 2 ^ (prefixWord ++ tailWord_2163154).sum := by decide
  have hdescent : baseEnd_2163154 < baseStart_2163154 := by decide
  rcases family_descends (prefixWord ++ tailWord_2163154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2163178 : List Nat := [3, 1, 3, 1, 3, 3, 1, 1, 6]
def baseStart_2163178 : Nat := 118140960795 + 2163178 * 2 ^ 59
def prefixEnd_2163178 : Nat := 4983230072969 + 3 ^ 40 * 2163178 * 2
def baseEnd_2163178 : Nat := 246833345607031731072607

theorem tailTrace_2163178 : CollatzResearch.WordTrace tailWord_2163178 prefixEnd_2163178 246833345607031731072607 := by
  unfold tailWord_2163178
  simp only [CollatzResearch.WordTrace]
  refine ⟨19724395839295755558694547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52598388904788681489852125 19724395839295755558694547)
  ·
    refine ⟨29586593758943633338041821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19724395839295755558694547 29586593758943633338041821)
    ·
      refine ⟨11094972659603862501765683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29586593758943633338041821 11094972659603862501765683)
      ·
        refine ⟨16642458989405793752648525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11094972659603862501765683 16642458989405793752648525)
        ·
          refine ⟨6240922121027172657243197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16642458989405793752648525 6240922121027172657243197)
          ·
            refine ⟨2340345795385189746466199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6240922121027172657243197 2340345795385189746466199)
            ·
              refine ⟨3510518693077784619699299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2340345795385189746466199 3510518693077784619699299)
              ·
                refine ⟨5265778039616676929548949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3510518693077784619699299 5265778039616676929548949)
                ·
                  refine ⟨246833345607031731072607, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5265778039616676929548949 246833345607031731072607)
                  ·
                    rfl

theorem cell22_2163178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 3, 1, 1, 6].length) (baseStart_2163178 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2163178 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2163178 prefixEnd_2163178 := by exact prefixLift 2163178
  have htrace : WordTrace (prefixWord ++ tailWord_2163178) baseStart_2163178 baseEnd_2163178 := by
    simpa [prefixWord, tailWord_2163178, baseEnd_2163178] using wordTrace_append hprefix tailTrace_2163178
  have hstable : (prefixWord ++ tailWord_2163178).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2163178).length < 2 ^ (prefixWord ++ tailWord_2163178).sum := by decide
  have hdescent : baseEnd_2163178 < baseStart_2163178 := by decide
  rcases family_descends (prefixWord ++ tailWord_2163178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2163223 : List Nat := [1, 1, 3, 6, 2, 9]
def baseStart_2163223 : Nat := 118140960795 + 2163223 * 2 ^ 59
def prefixEnd_2163223 : Nat := 4983230072969 + 3 ^ 40 * 2163223 * 2
def baseEnd_2163223 : Nat := 9142165941243581183243

theorem tailTrace_2163223 : CollatzResearch.WordTrace tailWord_2163223 prefixEnd_2163223 9142165941243581183243 := by
  unfold tailWord_2163223
  simp only [CollatzResearch.WordTrace]
  refine ⟨78899224642019994920166323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52599483094679996613444215 78899224642019994920166323)
  ·
    refine ⟨118348836963029992380249485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78899224642019994920166323 118348836963029992380249485)
    ·
      refine ⟨44380813861136247142593557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 118348836963029992380249485 44380813861136247142593557)
      ·
        refine ⟨2080350649740761584809073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 44380813861136247142593557 2080350649740761584809073)
        ·
          refine ⟨1560262987305571188606805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2080350649740761584809073 1560262987305571188606805)
          ·
            refine ⟨9142165941243581183243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1560262987305571188606805 9142165941243581183243)
            ·
              rfl

theorem cell22_2163223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 2, 9].length) (baseStart_2163223 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2163223 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2163223 prefixEnd_2163223 := by exact prefixLift 2163223
  have htrace : WordTrace (prefixWord ++ tailWord_2163223) baseStart_2163223 baseEnd_2163223 := by
    simpa [prefixWord, tailWord_2163223, baseEnd_2163223] using wordTrace_append hprefix tailTrace_2163223
  have hstable : (prefixWord ++ tailWord_2163223).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2163223).length < 2 ^ (prefixWord ++ tailWord_2163223).sum := by decide
  have hdescent : baseEnd_2163223 < baseStart_2163223 := by decide
  rcases family_descends (prefixWord ++ tailWord_2163223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2163251 : List Nat := [1, 1, 1, 2, 4, 2, 1, 5, 5]
def baseStart_2163251 : Nat := 118140960795 + 2163251 * 2 ^ 59
def prefixEnd_2163251 : Nat := 4983230072969 + 3 ^ 40 * 2163251 * 2
def baseEnd_2163251 : Nat := 246841675404315778714199

theorem tailTrace_2163251 : CollatzResearch.WordTrace tailWord_2163251 prefixEnd_2163251 246841675404315778714199 := by
  unfold tailWord_2163251
  simp only [CollatzResearch.WordTrace]
  refine ⟨78900245885918555702185607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52600163923945703801457071 78900245885918555702185607)
  ·
    refine ⟨118350368828877833553278411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78900245885918555702185607 118350368828877833553278411)
    ·
      refine ⟨177525553243316750329917617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118350368828877833553278411 177525553243316750329917617)
      ·
        refine ⟨133144164932487562747438213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 177525553243316750329917617 133144164932487562747438213)
        ·
          refine ⟨24964530924841418015144665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 133144164932487562747438213 24964530924841418015144665)
          ·
            refine ⟨18723398193631063511358499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24964530924841418015144665 18723398193631063511358499)
            ·
              refine ⟨28085097290446595267037749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18723398193631063511358499 28085097290446595267037749)
              ·
                refine ⟨2632977870979368306284789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 28085097290446595267037749 2632977870979368306284789)
                ·
                  refine ⟨246841675404315778714199, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2632977870979368306284789 246841675404315778714199)
                  ·
                    rfl

theorem cell22_2163251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 5, 5].length) (baseStart_2163251 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2163251 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2163251 prefixEnd_2163251 := by exact prefixLift 2163251
  have htrace : WordTrace (prefixWord ++ tailWord_2163251) baseStart_2163251 baseEnd_2163251 := by
    simpa [prefixWord, tailWord_2163251, baseEnd_2163251] using wordTrace_append hprefix tailTrace_2163251
  have hstable : (prefixWord ++ tailWord_2163251).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2163251).length < 2 ^ (prefixWord ++ tailWord_2163251).sum := by decide
  have hdescent : baseEnd_2163251 < baseStart_2163251 := by decide
  rcases family_descends (prefixWord ++ tailWord_2163251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2163296 : List Nat := [2, 1, 1, 3, 2, 1, 3, 3, 6]
def baseStart_2163296 : Nat := 118140960795 + 2163296 * 2 ^ 59
def prefixEnd_2163296 : Nat := 4983230072969 + 3 ^ 40 * 2163296 * 2
def baseEnd_2163296 : Nat := 246846810210860739589153

theorem tailTrace_2163296 : CollatzResearch.WordTrace tailWord_2163296 prefixEnd_2163296 246846810210860739589153 := by
  unfold tailWord_2163296
  simp only [CollatzResearch.WordTrace]
  refine ⟨39450943585377764193786871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52601258113837018925049161 39450943585377764193786871)
  ·
    refine ⟨59176415378066646290680307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39450943585377764193786871 59176415378066646290680307)
    ·
      refine ⟨88764623067099969436020461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59176415378066646290680307 88764623067099969436020461)
      ·
        refine ⟨33286733650162488538507673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 88764623067099969436020461 33286733650162488538507673)
        ·
          refine ⟨24965050237621866403880755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33286733650162488538507673 24965050237621866403880755)
          ·
            refine ⟨37447575356432799605821133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24965050237621866403880755 37447575356432799605821133)
            ·
              refine ⟨14042840758662299852182925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37447575356432799605821133 14042840758662299852182925)
              ·
                refine ⟨5266065284498362444568597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14042840758662299852182925 5266065284498362444568597)
                ·
                  refine ⟨246846810210860739589153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5266065284498362444568597 246846810210860739589153)
                  ·
                    rfl

theorem cell22_2163296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 3, 3, 6].length) (baseStart_2163296 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2163296 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2163296 prefixEnd_2163296 := by exact prefixLift 2163296
  have htrace : WordTrace (prefixWord ++ tailWord_2163296) baseStart_2163296 baseEnd_2163296 := by
    simpa [prefixWord, tailWord_2163296, baseEnd_2163296] using wordTrace_append hprefix tailTrace_2163296
  have hstable : (prefixWord ++ tailWord_2163296).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2163296).length < 2 ^ (prefixWord ++ tailWord_2163296).sum := by decide
  have hdescent : baseEnd_2163296 < baseStart_2163296 := by decide
  rcases family_descends (prefixWord ++ tailWord_2163296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2163328 : List Nat := [2, 1, 1, 2, 1, 5, 1, 2, 4, 3]
def baseStart_2163328 : Nat := 118140960795 + 2163328 * 2 ^ 59
def prefixEnd_2163328 : Nat := 4983230072969 + 3 ^ 40 * 2163328 * 2
def baseEnd_2163328 : Nat := 740551384886544801967361

theorem tailTrace_2163328 : CollatzResearch.WordTrace tailWord_2163328 prefixEnd_2163328 740551384886544801967361 := by
  unfold tailWord_2163328
  simp only [CollatzResearch.WordTrace]
  refine ⟨39451527153319798926369319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52602036204426398568492425 39451527153319798926369319)
  ·
    refine ⟨59177290729979698389553979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39451527153319798926369319 59177290729979698389553979)
    ·
      refine ⟨88765936094969547584330969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59177290729979698389553979 88765936094969547584330969)
      ·
        refine ⟨66574452071227160688248227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 88765936094969547584330969 66574452071227160688248227)
        ·
          refine ⟨99861678106840741032372341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66574452071227160688248227 99861678106840741032372341)
          ·
            refine ⟨9362032322516319471784907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 99861678106840741032372341 9362032322516319471784907)
            ·
              refine ⟨14043048483774479207677361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9362032322516319471784907 14043048483774479207677361)
              ·
                refine ⟨10532286362830859405758021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14043048483774479207677361 10532286362830859405758021)
                ·
                  refine ⟨1974803693030786138579629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10532286362830859405758021 1974803693030786138579629)
                  ·
                    refine ⟨740551384886544801967361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1974803693030786138579629 740551384886544801967361)
                    ·
                      rfl

theorem cell22_2163328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 1, 2, 4, 3].length) (baseStart_2163328 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2163328 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2163328 prefixEnd_2163328 := by exact prefixLift 2163328
  have htrace : WordTrace (prefixWord ++ tailWord_2163328) baseStart_2163328 baseEnd_2163328 := by
    simpa [prefixWord, tailWord_2163328, baseEnd_2163328] using wordTrace_append hprefix tailTrace_2163328
  have hstable : (prefixWord ++ tailWord_2163328).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2163328).length < 2 ^ (prefixWord ++ tailWord_2163328).sum := by decide
  have hdescent : baseEnd_2163328 < baseStart_2163328 := by decide
  rcases family_descends (prefixWord ++ tailWord_2163328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2163377 : List Nat := [1, 2, 2, 6, 1, 1, 2, 1, 2, 4]
def baseStart_2163377 : Nat := 118140960795 + 2163377 * 2 ^ 59
def prefixEnd_2163377 : Nat := 4983230072969 + 3 ^ 40 * 2163377 * 2
def baseEnd_2163377 : Nat := 740568158587925007492211

theorem tailTrace_2163377 : CollatzResearch.WordTrace tailWord_2163377 prefixEnd_2163377 740568158587925007492211 := by
  unfold tailWord_2163377
  simp only [CollatzResearch.WordTrace]
  refine ⟨78904841483462079221272385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52603227655641386147514923 78904841483462079221272385)
  ·
    refine ⟨59178631112596559415954289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78904841483462079221272385 59178631112596559415954289)
    ·
      refine ⟨44383973334447419561965717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59178631112596559415954289 44383973334447419561965717)
      ·
        refine ⟨2080498750052222791967143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 44383973334447419561965717 2080498750052222791967143)
        ·
          refine ⟨3120748125078334187950715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2080498750052222791967143 3120748125078334187950715)
          ·
            refine ⟨4681122187617501281926073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3120748125078334187950715 4681122187617501281926073)
            ·
              refine ⟨3510841640713125961444555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4681122187617501281926073 3510841640713125961444555)
              ·
                refine ⟨5266262461069688942166833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3510841640713125961444555 5266262461069688942166833)
                ·
                  refine ⟨3949696845802266706625125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5266262461069688942166833 3949696845802266706625125)
                  ·
                    refine ⟨740568158587925007492211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3949696845802266706625125 740568158587925007492211)
                    ·
                      rfl

theorem cell22_2163377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 2, 1, 2, 4].length) (baseStart_2163377 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2163377 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2163377 prefixEnd_2163377 := by exact prefixLift 2163377
  have htrace : WordTrace (prefixWord ++ tailWord_2163377) baseStart_2163377 baseEnd_2163377 := by
    simpa [prefixWord, tailWord_2163377, baseEnd_2163377] using wordTrace_append hprefix tailTrace_2163377
  have hstable : (prefixWord ++ tailWord_2163377).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2163377).length < 2 ^ (prefixWord ++ tailWord_2163377).sum := by decide
  have hdescent : baseEnd_2163377 < baseStart_2163377 := by decide
  rcases family_descends (prefixWord ++ tailWord_2163377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2163398 : List Nat := [6, 1, 2, 1, 2, 2, 2, 2, 4]
def baseStart_2163398 : Nat := 118140960795 + 2163398 * 2 ^ 59
def prefixEnd_2163398 : Nat := 4983230072969 + 3 ^ 40 * 2163398 * 2
def baseEnd_2163398 : Nat := 246858449105695984239049

theorem tailTrace_2163398 : CollatzResearch.WordTrace tailWord_2163398 prefixEnd_2163398 246858449105695984239049 := by
  unfold tailWord_2163398
  simp only [CollatzResearch.WordTrace]
  refine ⟨2465800231762062493993339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 52603738277590666538524565 2465800231762062493993339)
  ·
    refine ⟨3698700347643093740990009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2465800231762062493993339 3698700347643093740990009)
    ·
      refine ⟨2774025260732320305742507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3698700347643093740990009 2774025260732320305742507)
      ·
        refine ⟨4161037891098480458613761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2774025260732320305742507 4161037891098480458613761)
        ·
          refine ⟨3120778418323860343960321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4161037891098480458613761 3120778418323860343960321)
          ·
            refine ⟨2340583813742895257970241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3120778418323860343960321 2340583813742895257970241)
            ·
              refine ⟨1755437860307171443477681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2340583813742895257970241 1755437860307171443477681)
              ·
                refine ⟨1316578395230378582608261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1755437860307171443477681 1316578395230378582608261)
                ·
                  refine ⟨246858449105695984239049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1316578395230378582608261 246858449105695984239049)
                  ·
                    rfl

theorem cell22_2163398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 2, 2, 2, 4].length) (baseStart_2163398 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2163398 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2163398 prefixEnd_2163398 := by exact prefixLift 2163398
  have htrace : WordTrace (prefixWord ++ tailWord_2163398) baseStart_2163398 baseEnd_2163398 := by
    simpa [prefixWord, tailWord_2163398, baseEnd_2163398] using wordTrace_append hprefix tailTrace_2163398
  have hstable : (prefixWord ++ tailWord_2163398).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2163398).length < 2 ^ (prefixWord ++ tailWord_2163398).sum := by decide
  have hdescent : baseEnd_2163398 < baseStart_2163398 := by decide
  rcases family_descends (prefixWord ++ tailWord_2163398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2163401 : List Nat := [1, 2, 1, 1, 2, 1, 1, 1, 5, 7]
def baseStart_2163401 : Nat := 118140960795 + 2163401 * 2 ^ 59
def prefixEnd_2163401 : Nat := 4983230072969 + 3 ^ 40 * 2163401 * 2
def baseEnd_2163401 : Nat := 740576374278396944892137

theorem tailTrace_2163401 : CollatzResearch.WordTrace tailWord_2163401 prefixEnd_2163401 740576374278396944892137 := by
  unfold tailWord_2163401
  simp only [CollatzResearch.WordTrace]
  refine ⟨78905716835375131320146057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52603811223583420880097371 78905716835375131320146057)
  ·
    refine ⟨59179287626531348490109543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78905716835375131320146057 59179287626531348490109543)
    ·
      refine ⟨88768931439797022735164315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59179287626531348490109543 88768931439797022735164315)
      ·
        refine ⟨133153397159695534102746473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88768931439797022735164315 133153397159695534102746473)
        ·
          refine ⟨99865047869771650577059855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 133153397159695534102746473 99865047869771650577059855)
          ·
            refine ⟨149797571804657475865589783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 99865047869771650577059855 149797571804657475865589783)
            ·
              refine ⟨224696357706986213798384675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 149797571804657475865589783 224696357706986213798384675)
              ·
                refine ⟨337044536560479320697577013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 224696357706986213798384675 337044536560479320697577013)
                ·
                  refine ⟨31597925302544936315397845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 337044536560479320697577013 31597925302544936315397845)
                  ·
                    refine ⟨740576374278396944892137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 31597925302544936315397845 740576374278396944892137)
                    ·
                      rfl

theorem cell22_2163401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 1, 5, 7].length) (baseStart_2163401 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2163401 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2163401 prefixEnd_2163401 := by exact prefixLift 2163401
  have htrace : WordTrace (prefixWord ++ tailWord_2163401) baseStart_2163401 baseEnd_2163401 := by
    simpa [prefixWord, tailWord_2163401, baseEnd_2163401] using wordTrace_append hprefix tailTrace_2163401
  have hstable : (prefixWord ++ tailWord_2163401).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2163401).length < 2 ^ (prefixWord ++ tailWord_2163401).sum := by decide
  have hdescent : baseEnd_2163401 < baseStart_2163401 := by decide
  rcases family_descends (prefixWord ++ tailWord_2163401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2163418 : List Nat := [3, 1, 1, 2, 2, 2, 3, 1, 2, 5]
def baseStart_2163418 : Nat := 118140960795 + 2163418 * 2 ^ 59
def prefixEnd_2163418 : Nat := 4983230072969 + 3 ^ 40 * 2163418 * 2
def baseEnd_2163418 : Nat := 740582193725814567217085

theorem tailTrace_2163418 : CollatzResearch.WordTrace tailWord_2163418 prefixEnd_2163418 740582193725814567217085 := by
  unfold tailWord_2163418
  simp only [CollatzResearch.WordTrace]
  refine ⟨19726584219078385805878727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52604224584209028815676605 19726584219078385805878727)
  ·
    refine ⟨29589876328617578708818091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19726584219078385805878727 29589876328617578708818091)
    ·
      refine ⟨44384814492926368063227137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29589876328617578708818091 44384814492926368063227137)
      ·
        refine ⟨33288610869694776047420353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44384814492926368063227137 33288610869694776047420353)
        ·
          refine ⟨24966458152271082035565265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33288610869694776047420353 24966458152271082035565265)
          ·
            refine ⟨18724843614203311526673949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24966458152271082035565265 18724843614203311526673949)
            ·
              refine ⟨7021816355326241822502731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18724843614203311526673949 7021816355326241822502731)
              ·
                refine ⟨10532724532989362733754097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7021816355326241822502731 10532724532989362733754097)
                ·
                  refine ⟨7899543399742022050315573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10532724532989362733754097 7899543399742022050315573)
                  ·
                    refine ⟨740582193725814567217085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7899543399742022050315573 740582193725814567217085)
                    ·
                      rfl

theorem cell22_2163418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 3, 1, 2, 5].length) (baseStart_2163418 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2163418 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2163418 prefixEnd_2163418 := by exact prefixLift 2163418
  have htrace : WordTrace (prefixWord ++ tailWord_2163418) baseStart_2163418 baseEnd_2163418 := by
    simpa [prefixWord, tailWord_2163418, baseEnd_2163418] using wordTrace_append hprefix tailTrace_2163418
  have hstable : (prefixWord ++ tailWord_2163418).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2163418).length < 2 ^ (prefixWord ++ tailWord_2163418).sum := by decide
  have hdescent : baseEnd_2163418 < baseStart_2163418 := by decide
  rcases family_descends (prefixWord ++ tailWord_2163418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2163433 : List Nat := [1, 2, 1, 1, 1, 2, 6, 1, 3, 4]
def baseStart_2163433 : Nat := 118140960795 + 2163433 * 2 ^ 59
def prefixEnd_2163433 : Nat := 4983230072969 + 3 ^ 40 * 2163433 * 2
def baseEnd_2163433 : Nat := 740587328532359528092039

theorem tailTrace_2163433 : CollatzResearch.WordTrace tailWord_2163433 prefixEnd_2163433 740587328532359528092039 := by
  unfold tailWord_2163433
  simp only [CollatzResearch.WordTrace]
  refine ⟨78906883971259200785310953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52604589314172800523540635 78906883971259200785310953)
  ·
    refine ⟨59180162978444400588983215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78906883971259200785310953 59180162978444400588983215)
    ·
      refine ⟨88770244467666600883474823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59180162978444400588983215 88770244467666600883474823)
      ·
        refine ⟨133155366701499901325212235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88770244467666600883474823 133155366701499901325212235)
        ·
          refine ⟨199733050052249851987818353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 133155366701499901325212235 199733050052249851987818353)
          ·
            refine ⟨149799787539187388990863765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 199733050052249851987818353 149799787539187388990863765)
            ·
              refine ⟨7021865040899408858946739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 149799787539187388990863765 7021865040899408858946739)
              ·
                refine ⟨10532797561349113288420109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7021865040899408858946739 10532797561349113288420109)
                ·
                  refine ⟨3949799085505917483157541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10532797561349113288420109 3949799085505917483157541)
                  ·
                    refine ⟨740587328532359528092039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3949799085505917483157541 740587328532359528092039)
                    ·
                      rfl

theorem cell22_2163433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 6, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 6, 1, 3, 4].length) (baseStart_2163433 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2163433 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2163433 prefixEnd_2163433 := by exact prefixLift 2163433
  have htrace : WordTrace (prefixWord ++ tailWord_2163433) baseStart_2163433 baseEnd_2163433 := by
    simpa [prefixWord, tailWord_2163433, baseEnd_2163433] using wordTrace_append hprefix tailTrace_2163433
  have hstable : (prefixWord ++ tailWord_2163433).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2163433).length < 2 ^ (prefixWord ++ tailWord_2163433).sum := by decide
  have hdescent : baseEnd_2163433 < baseStart_2163433 := by decide
  rcases family_descends (prefixWord ++ tailWord_2163433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2163465 : List Nat := [1, 2, 1, 1, 3, 2, 4, 4, 4]
def baseStart_2163465 : Nat := 118140960795 + 2163465 * 2 ^ 59
def prefixEnd_2163465 : Nat := 4983230072969 + 3 ^ 40 * 2163465 * 2
def baseEnd_2163465 : Nat := 246866094262107370430647

theorem tailTrace_2163465 : CollatzResearch.WordTrace tailWord_2163465 prefixEnd_2163465 246866094262107370430647 := by
  unfold tailWord_2163465
  simp only [CollatzResearch.WordTrace]
  refine ⟨78908051107143270250475849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52605367404762180166983899 78908051107143270250475849)
  ·
    refine ⟨59181038330357452687856887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78908051107143270250475849 59181038330357452687856887)
    ·
      refine ⟨88771557495536179031785331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59181038330357452687856887 88771557495536179031785331)
      ·
        refine ⟨133157336243304268547677997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88771557495536179031785331 133157336243304268547677997)
        ·
          refine ⟨49934001091239100705379249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 133157336243304268547677997 49934001091239100705379249)
          ·
            refine ⟨37450500818429325529034437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49934001091239100705379249 37450500818429325529034437)
            ·
              refine ⟨7021968903455498536693957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 37450500818429325529034437 7021968903455498536693957)
              ·
                refine ⟨1316619169397905975630117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7021968903455498536693957 1316619169397905975630117)
                ·
                  refine ⟨246866094262107370430647, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1316619169397905975630117 246866094262107370430647)
                  ·
                    rfl

theorem cell22_2163465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 4, 4, 4].length) (baseStart_2163465 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2163465 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2163465 prefixEnd_2163465 := by exact prefixLift 2163465
  have htrace : WordTrace (prefixWord ++ tailWord_2163465) baseStart_2163465 baseEnd_2163465 := by
    simpa [prefixWord, tailWord_2163465, baseEnd_2163465] using wordTrace_append hprefix tailTrace_2163465
  have hstable : (prefixWord ++ tailWord_2163465).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2163465).length < 2 ^ (prefixWord ++ tailWord_2163465).sum := by decide
  have hdescent : baseEnd_2163465 < baseStart_2163465 := by decide
  rcases family_descends (prefixWord ++ tailWord_2163465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2163493 : List Nat := [1, 3, 1, 2, 3, 1, 3, 8]
def baseStart_2163493 : Nat := 118140960795 + 2163493 * 2 ^ 59
def prefixEnd_2163493 : Nat := 4983230072969 + 3 ^ 40 * 2163493 * 2
def baseEnd_2163493 : Nat := 82289763084282152399095

theorem tailTrace_2163493 : CollatzResearch.WordTrace tailWord_2163493 prefixEnd_2163493 82289763084282152399095 := by
  unfold tailWord_2163493
  simp only [CollatzResearch.WordTrace]
  refine ⟨78909072351041831032495133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52606048234027887354996755 78909072351041831032495133)
  ·
    refine ⟨29590902131640686637185675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 78909072351041831032495133 29590902131640686637185675)
    ·
      refine ⟨44386353197461029955778513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29590902131640686637185675 44386353197461029955778513)
      ·
        refine ⟨33289764898095772466833885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44386353197461029955778513 33289764898095772466833885)
        ·
          refine ⟨12483661836785914675062707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33289764898095772466833885 12483661836785914675062707)
          ·
            refine ⟨18725492755178872012594061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12483661836785914675062707 18725492755178872012594061)
            ·
              refine ⟨7022059783192077004722773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18725492755178872012594061 7022059783192077004722773)
              ·
                refine ⟨82289763084282152399095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7022059783192077004722773 82289763084282152399095)
                ·
                  rfl

theorem cell22_2163493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 3, 8].length) (baseStart_2163493 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2163493 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2163493 prefixEnd_2163493 := by exact prefixLift 2163493
  have htrace : WordTrace (prefixWord ++ tailWord_2163493) baseStart_2163493 baseEnd_2163493 := by
    simpa [prefixWord, tailWord_2163493, baseEnd_2163493] using wordTrace_append hprefix tailTrace_2163493
  have hstable : (prefixWord ++ tailWord_2163493).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2163493).length < 2 ^ (prefixWord ++ tailWord_2163493).sum := by decide
  have hdescent : baseEnd_2163493 < baseStart_2163493 := by decide
  rcases family_descends (prefixWord ++ tailWord_2163493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2163523 : List Nat := [1, 1, 1, 3, 1, 4, 2, 1, 2, 6]
def baseStart_2163523 : Nat := 118140960795 + 2163523 * 2 ^ 59
def prefixEnd_2163523 : Nat := 4983230072969 + 3 ^ 40 * 2163523 * 2
def baseEnd_2163523 : Nat := 740618137371629293341763

theorem tailTrace_2163523 : CollatzResearch.WordTrace tailWord_2163523 prefixEnd_2163523 740618137371629293341763 := by
  unfold tailWord_2163523
  simp only [CollatzResearch.WordTrace]
  refine ⟨78910166540933146156087223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52606777693955430770724815 78910166540933146156087223)
  ·
    refine ⟨118365249811399719234130835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78910166540933146156087223 118365249811399719234130835)
    ·
      refine ⟨177547874717099578851196253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118365249811399719234130835 177547874717099578851196253)
      ·
        refine ⟨66580453018912342069198595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 177547874717099578851196253 66580453018912342069198595)
        ·
          refine ⟨99870679528368513103797893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66580453018912342069198595 99870679528368513103797893)
          ·
            refine ⟨18725752411569096206962105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 99870679528368513103797893 18725752411569096206962105)
            ·
              refine ⟨14044314308676822155221579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18725752411569096206962105 14044314308676822155221579)
              ·
                refine ⟨21066471463015233232832369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14044314308676822155221579 21066471463015233232832369)
                ·
                  refine ⟨15799853597261424924624277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21066471463015233232832369 15799853597261424924624277)
                  ·
                    refine ⟨740618137371629293341763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15799853597261424924624277 740618137371629293341763)
                    ·
                      rfl

theorem cell22_2163523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 2, 1, 2, 6].length) (baseStart_2163523 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2163523 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2163523 prefixEnd_2163523 := by exact prefixLift 2163523
  have htrace : WordTrace (prefixWord ++ tailWord_2163523) baseStart_2163523 baseEnd_2163523 := by
    simpa [prefixWord, tailWord_2163523, baseEnd_2163523] using wordTrace_append hprefix tailTrace_2163523
  have hstable : (prefixWord ++ tailWord_2163523).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2163523).length < 2 ^ (prefixWord ++ tailWord_2163523).sum := by decide
  have hdescent : baseEnd_2163523 < baseStart_2163523 := by decide
  rcases family_descends (prefixWord ++ tailWord_2163523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2163525 : List Nat := [1, 3, 1, 1, 1, 2, 2, 5, 3, 3]
def baseStart_2163525 : Nat := 118140960795 + 2163525 * 2 ^ 59
def prefixEnd_2163525 : Nat := 4983230072969 + 3 ^ 40 * 2163525 * 2
def baseEnd_2163525 : Nat := 740618822012501954791757

theorem tailTrace_2163525 : CollatzResearch.WordTrace tailWord_2163525 prefixEnd_2163525 740618822012501954791757 := by
  unfold tailWord_2163525
  simp only [CollatzResearch.WordTrace]
  refine ⟨78910239486925900497660029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52606826324617266998440019 78910239486925900497660029)
  ·
    refine ⟨29591339807597212686622511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 78910239486925900497660029 29591339807597212686622511)
    ·
      refine ⟨44387009711395819029933767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29591339807597212686622511 44387009711395819029933767)
      ·
        refine ⟨66580514567093728544900651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44387009711395819029933767 66580514567093728544900651)
        ·
          refine ⟨99870771850640592817350977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66580514567093728544900651 99870771850640592817350977)
          ·
            refine ⟨74903078887980444613013233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 99870771850640592817350977 74903078887980444613013233)
            ·
              refine ⟨56177309165985333459759925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 74903078887980444613013233 56177309165985333459759925)
              ·
                refine ⟨5266622734311125011852493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 56177309165985333459759925 5266622734311125011852493)
                ·
                  refine ⟨1974983525366671879444685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5266622734311125011852493 1974983525366671879444685)
                  ·
                    refine ⟨740618822012501954791757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1974983525366671879444685 740618822012501954791757)
                    ·
                      rfl

theorem cell22_2163525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 5, 3, 3].length) (baseStart_2163525 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2163525 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2163525 prefixEnd_2163525 := by exact prefixLift 2163525
  have htrace : WordTrace (prefixWord ++ tailWord_2163525) baseStart_2163525 baseEnd_2163525 := by
    simpa [prefixWord, tailWord_2163525, baseEnd_2163525] using wordTrace_append hprefix tailTrace_2163525
  have hstable : (prefixWord ++ tailWord_2163525).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2163525).length < 2 ^ (prefixWord ++ tailWord_2163525).sum := by decide
  have hdescent : baseEnd_2163525 < baseStart_2163525 := by decide
  rcases family_descends (prefixWord ++ tailWord_2163525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2163553 : List Nat := [1, 2, 3, 1, 1, 1, 2, 1, 3, 7]
def baseStart_2163553 : Nat := 118140960795 + 2163553 * 2 ^ 59
def prefixEnd_2163553 : Nat := 4983230072969 + 3 ^ 40 * 2163553 * 2
def baseEnd_2163553 : Nat := 740628406984719215091671

theorem tailTrace_2163553 : CollatzResearch.WordTrace tailWord_2163553 prefixEnd_2163553 740628406984719215091671 := by
  unfold tailWord_2163553
  simp only [CollatzResearch.WordTrace]
  refine ⟨78911260730824461279679313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52607507153882974186452875 78911260730824461279679313)
  ·
    refine ⟨59183445548118345959759485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78911260730824461279679313 59183445548118345959759485)
    ·
      refine ⟨22193792080544379734909807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 59183445548118345959759485 22193792080544379734909807)
      ·
        refine ⟨33290688120816569602364711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22193792080544379734909807 33290688120816569602364711)
        ·
          refine ⟨49936032181224854403547067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33290688120816569602364711 49936032181224854403547067)
          ·
            refine ⟨74904048271837281605320601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49936032181224854403547067 74904048271837281605320601)
            ·
              refine ⟨56178036203877961203990451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 74904048271837281605320601 56178036203877961203990451)
              ·
                refine ⟨84267054305816941805985677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 56178036203877961203990451 84267054305816941805985677)
                ·
                  refine ⟨31600145364681353177244629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 84267054305816941805985677 31600145364681353177244629)
                  ·
                    refine ⟨740628406984719215091671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 31600145364681353177244629 740628406984719215091671)
                    ·
                      rfl

theorem cell22_2163553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 1, 3, 7].length) (baseStart_2163553 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2163553 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2163553 prefixEnd_2163553 := by exact prefixLift 2163553
  have htrace : WordTrace (prefixWord ++ tailWord_2163553) baseStart_2163553 baseEnd_2163553 := by
    simpa [prefixWord, tailWord_2163553, baseEnd_2163553] using wordTrace_append hprefix tailTrace_2163553
  have hstable : (prefixWord ++ tailWord_2163553).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2163553).length < 2 ^ (prefixWord ++ tailWord_2163553).sum := by decide
  have hdescent : baseEnd_2163553 < baseStart_2163553 := by decide
  rcases family_descends (prefixWord ++ tailWord_2163553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2163660 : List Nat := [2, 2, 1, 4, 1, 1, 1, 1, 2, 7]
def baseStart_2163660 : Nat := 118140960795 + 2163660 * 2 ^ 59
def prefixEnd_2163660 : Nat := 4983230072969 + 3 ^ 40 * 2163660 * 2
def baseEnd_2163660 : Nat := 740665035271406602666343

theorem tailTrace_2163660 : CollatzResearch.WordTrace tailWord_2163660 prefixEnd_2163660 740665035271406602666343 := by
  unfold tailWord_2163660
  simp only [CollatzResearch.WordTrace]
  refine ⟨39457581670718409276912217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52610108894291212369216289 39457581670718409276912217)
  ·
    refine ⟨29593186253038806957684163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39457581670718409276912217 29593186253038806957684163)
    ·
      refine ⟨44389779379558210436526245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29593186253038806957684163 44389779379558210436526245)
      ·
        refine ⟨8323083633667164456848671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 44389779379558210436526245 8323083633667164456848671)
        ·
          refine ⟨12484625450500746685273007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8323083633667164456848671 12484625450500746685273007)
          ·
            refine ⟨18726938175751120027909511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12484625450500746685273007 18726938175751120027909511)
            ·
              refine ⟨28090407263626680041864267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18726938175751120027909511 28090407263626680041864267)
              ·
                refine ⟨42135610895440020062796401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28090407263626680041864267 42135610895440020062796401)
                ·
                  refine ⟨31601708171580015047097301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 42135610895440020062796401 31601708171580015047097301)
                  ·
                    refine ⟨740665035271406602666343, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 31601708171580015047097301 740665035271406602666343)
                    ·
                      rfl

theorem cell22_2163660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 1, 2, 7].length) (baseStart_2163660 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2163660 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2163660 prefixEnd_2163660 := by exact prefixLift 2163660
  have htrace : WordTrace (prefixWord ++ tailWord_2163660) baseStart_2163660 baseEnd_2163660 := by
    simpa [prefixWord, tailWord_2163660, baseEnd_2163660] using wordTrace_append hprefix tailTrace_2163660
  have hstable : (prefixWord ++ tailWord_2163660).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2163660).length < 2 ^ (prefixWord ++ tailWord_2163660).sum := by decide
  have hdescent : baseEnd_2163660 < baseStart_2163660 := by decide
  rcases family_descends (prefixWord ++ tailWord_2163660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2163662 : List Nat := [4, 1, 1, 1, 2, 3, 4, 6]
def baseStart_2163662 : Nat := 118140960795 + 2163662 * 2 ^ 59
def prefixEnd_2163662 : Nat := 4983230072969 + 3 ^ 40 * 2163662 * 2
def baseEnd_2163662 : Nat := 82296191101364362679593

theorem tailTrace_2163662 : CollatzResearch.WordTrace tailWord_2163662 prefixEnd_2163662 82296191101364362679593 := by
  unfold tailWord_2163662
  simp only [CollatzResearch.WordTrace]
  refine ⟨9864404535928696611924655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 52610157524953048596931493 9864404535928696611924655)
  ·
    refine ⟨14796606803893044917886983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9864404535928696611924655 14796606803893044917886983)
    ·
      refine ⟨22194910205839567376830475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14796606803893044917886983 22194910205839567376830475)
      ·
        refine ⟨33292365308759351065245713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22194910205839567376830475 33292365308759351065245713)
        ·
          refine ⟨24969273981569513298934285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33292365308759351065245713 24969273981569513298934285)
          ·
            refine ⟨9363477743088567487100357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24969273981569513298934285 9363477743088567487100357)
            ·
              refine ⟨1755652076829106403831317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9363477743088567487100357 1755652076829106403831317)
              ·
                refine ⟨82296191101364362679593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1755652076829106403831317 82296191101364362679593)
                ·
                  rfl

theorem cell22_2163662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 4, 6].length) (baseStart_2163662 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2163662 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2163662 prefixEnd_2163662 := by exact prefixLift 2163662
  have htrace : WordTrace (prefixWord ++ tailWord_2163662) baseStart_2163662 baseEnd_2163662 := by
    simpa [prefixWord, tailWord_2163662, baseEnd_2163662] using wordTrace_append hprefix tailTrace_2163662
  have hstable : (prefixWord ++ tailWord_2163662).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2163662).length < 2 ^ (prefixWord ++ tailWord_2163662).sum := by decide
  have hdescent : baseEnd_2163662 < baseStart_2163662 := by decide
  rcases family_descends (prefixWord ++ tailWord_2163662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2163705 : List Nat := [1, 2, 1, 3, 1, 3, 2, 1, 1, 7]
def baseStart_2163705 : Nat := 118140960795 + 2163705 * 2 ^ 59
def prefixEnd_2163705 : Nat := 4983230072969 + 3 ^ 40 * 2163705 * 2
def baseEnd_2163705 : Nat := 740680439691041485291205

theorem tailTrace_2163705 : CollatzResearch.WordTrace tailWord_2163705 prefixEnd_2163705 740680439691041485291205 := by
  unfold tailWord_2163705
  simp only [CollatzResearch.WordTrace]
  refine ⟨78916804626273791239212569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52611203084182527492808379 78916804626273791239212569)
  ·
    refine ⟨59187603469705343429409427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78916804626273791239212569 59187603469705343429409427)
    ·
      refine ⟨88781405204558015144114141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59187603469705343429409427 88781405204558015144114141)
      ·
        refine ⟨33293026951709255679042803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 88781405204558015144114141 33293026951709255679042803)
        ·
          refine ⟨49939540427563883518564205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33293026951709255679042803 49939540427563883518564205)
          ·
            refine ⟨18727327660336456319461577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 49939540427563883518564205 18727327660336456319461577)
            ·
              refine ⟨14045495745252342239596183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18727327660336456319461577 14045495745252342239596183)
              ·
                refine ⟨21068243617878513359394275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14045495745252342239596183 21068243617878513359394275)
                ·
                  refine ⟨31602365426817770039091413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21068243617878513359394275 31602365426817770039091413)
                  ·
                    refine ⟨740680439691041485291205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 31602365426817770039091413 740680439691041485291205)
                    ·
                      rfl

theorem cell22_2163705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 2, 1, 1, 7].length) (baseStart_2163705 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2163705 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2163705 prefixEnd_2163705 := by exact prefixLift 2163705
  have htrace : WordTrace (prefixWord ++ tailWord_2163705) baseStart_2163705 baseEnd_2163705 := by
    simpa [prefixWord, tailWord_2163705, baseEnd_2163705] using wordTrace_append hprefix tailTrace_2163705
  have hstable : (prefixWord ++ tailWord_2163705).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2163705).length < 2 ^ (prefixWord ++ tailWord_2163705).sum := by decide
  have hdescent : baseEnd_2163705 < baseStart_2163705 := by decide
  rcases family_descends (prefixWord ++ tailWord_2163705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2163737 : List Nat := [1, 2, 1, 2, 1, 1, 4, 5, 1, 4]
def baseStart_2163737 : Nat := 118140960795 + 2163737 * 2 ^ 59
def prefixEnd_2163737 : Nat := 4983230072969 + 3 ^ 40 * 2163737 * 2
def baseEnd_2163737 : Nat := 740691393945004068491107

theorem tailTrace_2163737 : CollatzResearch.WordTrace tailWord_2163737 prefixEnd_2163737 740691393945004068491107 := by
  unfold tailWord_2163737
  simp only [CollatzResearch.WordTrace]
  refine ⟨78917971762157860704377465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52611981174771907136251643 78917971762157860704377465)
  ·
    refine ⟨59188478821618395528283099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78917971762157860704377465 59188478821618395528283099)
    ·
      refine ⟨88782718232427593292424649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59188478821618395528283099 88782718232427593292424649)
      ·
        refine ⟨66587038674320694969318487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 88782718232427593292424649 66587038674320694969318487)
        ·
          refine ⟨99880558011481042453977731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66587038674320694969318487 99880558011481042453977731)
          ·
            refine ⟨149820837017221563680966597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 99880558011481042453977731 149820837017221563680966597)
            ·
              refine ⟨28091406940729043190181237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 149820837017221563680966597 28091406940729043190181237)
              ·
                refine ⟨2633569400693347799079491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 28091406940729043190181237 2633569400693347799079491)
                ·
                  refine ⟨3950354101040021698619237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2633569400693347799079491 3950354101040021698619237)
                  ·
                    refine ⟨740691393945004068491107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3950354101040021698619237 740691393945004068491107)
                    ·
                      rfl

theorem cell22_2163737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 5, 1, 4].length) (baseStart_2163737 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2163737 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2163737 prefixEnd_2163737 := by exact prefixLift 2163737
  have htrace : WordTrace (prefixWord ++ tailWord_2163737) baseStart_2163737 baseEnd_2163737 := by
    simpa [prefixWord, tailWord_2163737, baseEnd_2163737] using wordTrace_append hprefix tailTrace_2163737
  have hstable : (prefixWord ++ tailWord_2163737).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2163737).length < 2 ^ (prefixWord ++ tailWord_2163737).sum := by decide
  have hdescent : baseEnd_2163737 < baseStart_2163737 := by decide
  rcases family_descends (prefixWord ++ tailWord_2163737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2163767 : List Nat := [1, 1, 3, 1, 2, 2, 1, 2, 6, 3]
def baseStart_2163767 : Nat := 118140960795 + 2163767 * 2 ^ 59
def prefixEnd_2163767 : Nat := 4983230072969 + 3 ^ 40 * 2163767 * 2
def baseEnd_2163767 : Nat := 740701663558093990241015

theorem tailTrace_2163767 : CollatzResearch.WordTrace tailWord_2163767 prefixEnd_2163767 740701663558093990241015 := by
  unfold tailWord_2163767
  simp only [CollatzResearch.WordTrace]
  refine ⟨78919065952049175827969555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52612710634699450551979703 78919065952049175827969555)
  ·
    refine ⟨118378598928073763741954333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78919065952049175827969555 118378598928073763741954333)
    ·
      refine ⟨44391974598027661403232875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 118378598928073763741954333 44391974598027661403232875)
      ·
        refine ⟨66587961897041492104849313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44391974598027661403232875 66587961897041492104849313)
        ·
          refine ⟨49940971422781119078636985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66587961897041492104849313 49940971422781119078636985)
          ·
            refine ⟨37455728567085839308977739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49940971422781119078636985 37455728567085839308977739)
            ·
              refine ⟨56183592850628758963466609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37455728567085839308977739 56183592850628758963466609)
              ·
                refine ⟨42137694637971569222599957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 56183592850628758963466609 42137694637971569222599957)
                ·
                  refine ⟨1975204436154917307309373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 42137694637971569222599957 1975204436154917307309373)
                  ·
                    refine ⟨740701663558093990241015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1975204436154917307309373 740701663558093990241015)
                    ·
                      rfl

theorem cell22_2163767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 2, 6, 3].length) (baseStart_2163767 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2163767 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2163767 prefixEnd_2163767 := by exact prefixLift 2163767
  have htrace : WordTrace (prefixWord ++ tailWord_2163767) baseStart_2163767 baseEnd_2163767 := by
    simpa [prefixWord, tailWord_2163767, baseEnd_2163767] using wordTrace_append hprefix tailTrace_2163767
  have hstable : (prefixWord ++ tailWord_2163767).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2163767).length < 2 ^ (prefixWord ++ tailWord_2163767).sum := by decide
  have hdescent : baseEnd_2163767 < baseStart_2163767 := by decide
  rcases family_descends (prefixWord ++ tailWord_2163767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2163818 : List Nat := [3, 1, 3, 2, 2, 2, 3, 1, 2, 3]
def baseStart_2163818 : Nat := 118140960795 + 2163818 * 2 ^ 59
def prefixEnd_2163818 : Nat := 4983230072969 + 3 ^ 40 * 2163818 * 2
def baseEnd_2163818 : Nat := 740719121900346857215859

theorem tailTrace_2163818 : CollatzResearch.WordTrace tailWord_2163818 prefixEnd_2163818 740719121900346857215859 := by
  unfold tailWord_2163818
  simp only [CollatzResearch.WordTrace]
  refine ⟨19730231518716102884519027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52613950716576274358717405 19730231518716102884519027)
  ·
    refine ⟨29595347278074154326778541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19730231518716102884519027 29595347278074154326778541)
    ·
      refine ⟨11098255229277807872541953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29595347278074154326778541 11098255229277807872541953)
      ·
        refine ⟨8323691421958355904406465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11098255229277807872541953 8323691421958355904406465)
        ·
          refine ⟨6242768566468766928304849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8323691421958355904406465 6242768566468766928304849)
          ·
            refine ⟨4682076424851575196228637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6242768566468766928304849 4682076424851575196228637)
            ·
              refine ⟨1755778659319340698585739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4682076424851575196228637 1755778659319340698585739)
              ·
                refine ⟨2633667988979011047878609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1755778659319340698585739 2633667988979011047878609)
                ·
                  refine ⟨1975250991734258285908957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2633667988979011047878609 1975250991734258285908957)
                  ·
                    refine ⟨740719121900346857215859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1975250991734258285908957 740719121900346857215859)
                    ·
                      rfl

theorem cell22_2163818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 3, 1, 2, 3].length) (baseStart_2163818 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2163818 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2163818 prefixEnd_2163818 := by exact prefixLift 2163818
  have htrace : WordTrace (prefixWord ++ tailWord_2163818) baseStart_2163818 baseEnd_2163818 := by
    simpa [prefixWord, tailWord_2163818, baseEnd_2163818] using wordTrace_append hprefix tailTrace_2163818
  have hstable : (prefixWord ++ tailWord_2163818).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2163818).length < 2 ^ (prefixWord ++ tailWord_2163818).sum := by decide
  have hdescent : baseEnd_2163818 < baseStart_2163818 := by decide
  rcases family_descends (prefixWord ++ tailWord_2163818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2163876 : List Nat := [2, 3, 1, 2, 3, 1, 4, 1, 5]
def baseStart_2163876 : Nat := 118140960795 + 2163876 * 2 ^ 59
def prefixEnd_2163876 : Nat := 4983230072969 + 3 ^ 40 * 2163876 * 2
def baseEnd_2163876 : Nat := 246912992161884679755227

theorem tailTrace_2163876 : CollatzResearch.WordTrace tailWord_2163876 prefixEnd_2163876 246912992161884679755227 := by
  unfold tailWord_2163876
  simp only [CollatzResearch.WordTrace]
  refine ⟨39461520754327143721843741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52615361005769524962458321 39461520754327143721843741)
  ·
    refine ⟨14798070282872678895691403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39461520754327143721843741 14798070282872678895691403)
    ·
      refine ⟨22197105424309018343537105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14798070282872678895691403 22197105424309018343537105)
      ·
        refine ⟨16647829068231763757652829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22197105424309018343537105 16647829068231763757652829)
        ·
          refine ⟨6242935900586911409119811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16647829068231763757652829 6242935900586911409119811)
          ·
            refine ⟨9364403850880367113679717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6242935900586911409119811 9364403850880367113679717)
            ·
              refine ⟨1755825722040068833814947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9364403850880367113679717 1755825722040068833814947)
              ·
                refine ⟨2633738583060103250722421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1755825722040068833814947 2633738583060103250722421)
                ·
                  refine ⟨246912992161884679755227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2633738583060103250722421 246912992161884679755227)
                  ·
                    rfl

theorem cell22_2163876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 4, 1, 5].length) (baseStart_2163876 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2163876 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2163876 prefixEnd_2163876 := by exact prefixLift 2163876
  have htrace : WordTrace (prefixWord ++ tailWord_2163876) baseStart_2163876 baseEnd_2163876 := by
    simpa [prefixWord, tailWord_2163876, baseEnd_2163876] using wordTrace_append hprefix tailTrace_2163876
  have hstable : (prefixWord ++ tailWord_2163876).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2163876).length < 2 ^ (prefixWord ++ tailWord_2163876).sum := by decide
  have hdescent : baseEnd_2163876 < baseStart_2163876 := by decide
  rcases family_descends (prefixWord ++ tailWord_2163876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2163887 : List Nat := [1, 1, 2, 1, 2, 3, 2, 4, 6]
def baseStart_2163887 : Nat := 118140960795 + 2163887 * 2 ^ 59
def prefixEnd_2163887 : Nat := 4983230072969 + 3 ^ 40 * 2163887 * 2
def baseEnd_2163887 : Nat := 246914247336817892413549

theorem tailTrace_2163887 : CollatzResearch.WordTrace tailWord_2163887 prefixEnd_2163887 246914247336817892413549 := by
  unfold tailWord_2163887
  simp only [CollatzResearch.WordTrace]
  refine ⟨78923442711614436322337915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52615628474409624214891943 78923442711614436322337915)
  ·
    refine ⟨118385164067421654483506873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78923442711614436322337915 118385164067421654483506873)
    ·
      refine ⟨88788873050566240862630155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 118385164067421654483506873 88788873050566240862630155)
      ·
        refine ⟨133183309575849361293945233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88788873050566240862630155 133183309575849361293945233)
        ·
          refine ⟨99887482181887020970458925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 133183309575849361293945233 99887482181887020970458925)
          ·
            refine ⟨37457805818207632863922097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 99887482181887020970458925 37457805818207632863922097)
            ·
              refine ⟨28093354363655724647941573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37457805818207632863922097 28093354363655724647941573)
              ·
                refine ⟨5267503943185448371489045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 28093354363655724647941573 5267503943185448371489045)
                ·
                  refine ⟨246914247336817892413549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5267503943185448371489045 246914247336817892413549)
                  ·
                    rfl

theorem cell22_2163887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 4, 6].length) (baseStart_2163887 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2163887 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2163887 prefixEnd_2163887 := by exact prefixLift 2163887
  have htrace : WordTrace (prefixWord ++ tailWord_2163887) baseStart_2163887 baseEnd_2163887 := by
    simpa [prefixWord, tailWord_2163887, baseEnd_2163887] using wordTrace_append hprefix tailTrace_2163887
  have hstable : (prefixWord ++ tailWord_2163887).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2163887).length < 2 ^ (prefixWord ++ tailWord_2163887).sum := by decide
  have hdescent : baseEnd_2163887 < baseStart_2163887 := by decide
  rcases family_descends (prefixWord ++ tailWord_2163887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2163936 : List Nat := [2, 1, 1, 3, 1, 4, 2, 3, 2, 3]
def baseStart_2163936 : Nat := 118140960795 + 2163936 * 2 ^ 59
def prefixEnd_2163936 : Nat := 4983230072969 + 3 ^ 40 * 2163936 * 2
def baseEnd_2163936 : Nat := 740759515711833882765497

theorem tailTrace_2163936 : CollatzResearch.WordTrace tailWord_2163936 prefixEnd_2163936 740759515711833882765497 := by
  unfold tailWord_2163936
  simp only [CollatzResearch.WordTrace]
  refine ⟨39462614944218458845435831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52616819925624611793914441 39462614944218458845435831)
  ·
    refine ⟨59193922416327688268153747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39462614944218458845435831 59193922416327688268153747)
    ·
      refine ⟨88790883624491532402230621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59193922416327688268153747 88790883624491532402230621)
      ·
        refine ⟨33296581359184324650836483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 88790883624491532402230621 33296581359184324650836483)
        ·
          refine ⟨49944872038776486976254725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33296581359184324650836483 49944872038776486976254725)
          ·
            refine ⟨9364663507270591308047761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 49944872038776486976254725 9364663507270591308047761)
            ·
              refine ⟨7023497630452943481035821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9364663507270591308047761 7023497630452943481035821)
              ·
                refine ⟨2633811611419853805388433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7023497630452943481035821 2633811611419853805388433)
                ·
                  refine ⟨1975358708564890354041325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2633811611419853805388433 1975358708564890354041325)
                  ·
                    refine ⟨740759515711833882765497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1975358708564890354041325 740759515711833882765497)
                    ·
                      rfl

theorem cell22_2163936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 2, 3, 2, 3].length) (baseStart_2163936 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2163936 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2163936 prefixEnd_2163936 := by exact prefixLift 2163936
  have htrace : WordTrace (prefixWord ++ tailWord_2163936) baseStart_2163936 baseEnd_2163936 := by
    simpa [prefixWord, tailWord_2163936, baseEnd_2163936] using wordTrace_append hprefix tailTrace_2163936
  have hstable : (prefixWord ++ tailWord_2163936).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2163936).length < 2 ^ (prefixWord ++ tailWord_2163936).sum := by decide
  have hdescent : baseEnd_2163936 < baseStart_2163936 := by decide
  rcases family_descends (prefixWord ++ tailWord_2163936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2164024 : List Nat := [2, 1, 2, 1, 3, 1, 1, 2, 5, 4]
def baseStart_2164024 : Nat := 118140960795 + 2164024 * 2 ^ 59
def prefixEnd_2164024 : Nat := 4983230072969 + 3 ^ 40 * 2164024 * 2
def baseEnd_2164024 : Nat := 740789639910230986565227

theorem tailTrace_2164024 : CollatzResearch.WordTrace tailWord_2164024 prefixEnd_2164024 740789639910230986565227 := by
  unfold tailWord_2164024
  simp only [CollatzResearch.WordTrace]
  refine ⟨39464219756059054360037563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52618959674745405813383417 39464219756059054360037563)
  ·
    refine ⟨59196329634088581540056345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39464219756059054360037563 59196329634088581540056345)
    ·
      refine ⟨44397247225566436155042259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59196329634088581540056345 44397247225566436155042259)
      ·
        refine ⟨66595870838349654232563389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44397247225566436155042259 66595870838349654232563389)
        ·
          refine ⟨24973451564381120337211271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 66595870838349654232563389 24973451564381120337211271)
          ·
            refine ⟨37460177346571680505816907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24973451564381120337211271 37460177346571680505816907)
            ·
              refine ⟨56190266019857520758725361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37460177346571680505816907 56190266019857520758725361)
              ·
                refine ⟨42142699514893140569044021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 56190266019857520758725361 42142699514893140569044021)
                ·
                  refine ⟨3950878079521231928347877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 42142699514893140569044021 3950878079521231928347877)
                  ·
                    refine ⟨740789639910230986565227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3950878079521231928347877 740789639910230986565227)
                    ·
                      rfl

theorem cell22_2164024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 2, 5, 4].length) (baseStart_2164024 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2164024 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2164024 prefixEnd_2164024 := by exact prefixLift 2164024
  have htrace : WordTrace (prefixWord ++ tailWord_2164024) baseStart_2164024 baseEnd_2164024 := by
    simpa [prefixWord, tailWord_2164024, baseEnd_2164024] using wordTrace_append hprefix tailTrace_2164024
  have hstable : (prefixWord ++ tailWord_2164024).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2164024).length < 2 ^ (prefixWord ++ tailWord_2164024).sum := by decide
  have hdescent : baseEnd_2164024 < baseStart_2164024 := by decide
  rcases family_descends (prefixWord ++ tailWord_2164024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2164045 : List Nat := [1, 6, 1, 3, 1, 1, 1, 3, 5]
def baseStart_2164045 : Nat := 118140960795 + 2164045 * 2 ^ 59
def prefixEnd_2164045 : Nat := 4983230072969 + 3 ^ 40 * 2164045 * 2
def baseEnd_2164045 : Nat := 246932276213131310596721

theorem tailTrace_2164045 : CollatzResearch.WordTrace tailWord_2164045 prefixEnd_2164045 246932276213131310596721 := by
  unfold tailWord_2164045
  simp only [CollatzResearch.WordTrace]
  refine ⟨78929205445042029306589589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52619470296694686204393059 78929205445042029306589589)
  ·
    refine ⟨3699806505236345123746387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 78929205445042029306589589 3699806505236345123746387)
    ·
      refine ⟨5549709757854517685619581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3699806505236345123746387 5549709757854517685619581)
      ·
        refine ⟨2081141159195444132107343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5549709757854517685619581 2081141159195444132107343)
        ·
          refine ⟨3121711738793166198161015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2081141159195444132107343 3121711738793166198161015)
          ·
            refine ⟨4682567608189749297241523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3121711738793166198161015 4682567608189749297241523)
            ·
              refine ⟨7023851412284623945862285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4682567608189749297241523 7023851412284623945862285)
              ·
                refine ⟨2633944279606733979698357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7023851412284623945862285 2633944279606733979698357)
                ·
                  refine ⟨246932276213131310596721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2633944279606733979698357 246932276213131310596721)
                  ·
                    rfl

theorem cell22_2164045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 1, 3, 5].length) (baseStart_2164045 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2164045 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2164045 prefixEnd_2164045 := by exact prefixLift 2164045
  have htrace : WordTrace (prefixWord ++ tailWord_2164045) baseStart_2164045 baseEnd_2164045 := by
    simpa [prefixWord, tailWord_2164045, baseEnd_2164045] using wordTrace_append hprefix tailTrace_2164045
  have hstable : (prefixWord ++ tailWord_2164045).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2164045).length < 2 ^ (prefixWord ++ tailWord_2164045).sum := by decide
  have hdescent : baseEnd_2164045 < baseStart_2164045 := by decide
  rcases family_descends (prefixWord ++ tailWord_2164045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2164120 : List Nat := [2, 1, 2, 5, 2, 2, 1, 1, 2, 4]
def baseStart_2164120 : Nat := 118140960795 + 2164120 * 2 ^ 59
def prefixEnd_2164120 : Nat := 4983230072969 + 3 ^ 40 * 2164120 * 2
def baseEnd_2164120 : Nat := 740822502672118736164933

theorem tailTrace_2164120 : CollatzResearch.WordTrace tailWord_2164120 prefixEnd_2164120 740822502672118736164933 := by
  unfold tailWord_2164120
  simp only [CollatzResearch.WordTrace]
  refine ⟨39465970459885158557784907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52621293946513544743713209 39465970459885158557784907)
  ·
    refine ⟨59198955689827737836677361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39465970459885158557784907 59198955689827737836677361)
    ·
      refine ⟨44399216767370803377508021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59198955689827737836677361 44399216767370803377508021)
      ·
        refine ⟨4162426571941012816641377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 44399216767370803377508021 4162426571941012816641377)
        ·
          refine ⟨3121819928955759612481033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4162426571941012816641377 3121819928955759612481033)
          ·
            refine ⟨2341364946716819709360775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3121819928955759612481033 2341364946716819709360775)
            ·
              refine ⟨3512047420075229564041163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2341364946716819709360775 3512047420075229564041163)
              ·
                refine ⟨5268071130112844346061745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3512047420075229564041163 5268071130112844346061745)
                ·
                  refine ⟨3951053347584633259546309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5268071130112844346061745 3951053347584633259546309)
                  ·
                    refine ⟨740822502672118736164933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3951053347584633259546309 740822502672118736164933)
                    ·
                      rfl

theorem cell22_2164120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 2, 1, 1, 2, 4].length) (baseStart_2164120 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2164120 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2164120 prefixEnd_2164120 := by exact prefixLift 2164120
  have htrace : WordTrace (prefixWord ++ tailWord_2164120) baseStart_2164120 baseEnd_2164120 := by
    simpa [prefixWord, tailWord_2164120, baseEnd_2164120] using wordTrace_append hprefix tailTrace_2164120
  have hstable : (prefixWord ++ tailWord_2164120).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2164120).length < 2 ^ (prefixWord ++ tailWord_2164120).sum := by decide
  have hdescent : baseEnd_2164120 < baseStart_2164120 := by decide
  rcases family_descends (prefixWord ++ tailWord_2164120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2164146 : List Nat := [3, 2, 1, 1, 1, 1, 2, 6, 5]
def baseStart_2164146 : Nat := 118140960795 + 2164146 * 2 ^ 59
def prefixEnd_2164146 : Nat := 4983230072969 + 3 ^ 40 * 2164146 * 2
def baseEnd_2164146 : Nat := 246943801001154445004951

theorem tailTrace_2164146 : CollatzResearch.WordTrace tailWord_2164146 prefixEnd_2164146 246943801001154445004951 := by
  unfold tailWord_2164146
  simp only [CollatzResearch.WordTrace]
  refine ⟨19733222304419030889004073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52621926145117415704010861 19733222304419030889004073)
  ·
    refine ⟨14799916728314273166753055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19733222304419030889004073 14799916728314273166753055)
    ·
      refine ⟨22199875092471409750129583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14799916728314273166753055 22199875092471409750129583)
      ·
        refine ⟨33299812638707114625194375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22199875092471409750129583 33299812638707114625194375)
        ·
          refine ⟨49949718958060671937791563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33299812638707114625194375 49949718958060671937791563)
          ·
            refine ⟨74924578437091007906687345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49949718958060671937791563 74924578437091007906687345)
            ·
              refine ⟨56193433827818255930015509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 74924578437091007906687345 56193433827818255930015509)
              ·
                refine ⟨2634067210678980746719477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 56193433827818255930015509 2634067210678980746719477)
                ·
                  refine ⟨246943801001154445004951, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2634067210678980746719477 246943801001154445004951)
                  ·
                    rfl

theorem cell22_2164146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 6, 5].length) (baseStart_2164146 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2164146 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2164146 prefixEnd_2164146 := by exact prefixLift 2164146
  have htrace : WordTrace (prefixWord ++ tailWord_2164146) baseStart_2164146 baseEnd_2164146 := by
    simpa [prefixWord, tailWord_2164146, baseEnd_2164146] using wordTrace_append hprefix tailTrace_2164146
  have hstable : (prefixWord ++ tailWord_2164146).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2164146).length < 2 ^ (prefixWord ++ tailWord_2164146).sum := by decide
  have hdescent : baseEnd_2164146 < baseStart_2164146 := by decide
  rcases family_descends (prefixWord ++ tailWord_2164146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2164193 : List Nat := [1, 2, 3, 1, 2, 3, 2, 3, 1, 4]
def baseStart_2164193 : Nat := 118140960795 + 2164193 * 2 ^ 59
def prefixEnd_2164193 : Nat := 4983230072969 + 3 ^ 40 * 2164193 * 2
def baseEnd_2164193 : Nat := 740847492063970879089709

theorem tailTrace_2164193 : CollatzResearch.WordTrace tailWord_2164193 prefixEnd_2164193 740847492063970879089709 := by
  unfold tailWord_2164193
  simp only [CollatzResearch.WordTrace]
  refine ⟨78934603448505850582977233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52623068965670567055318155 78934603448505850582977233)
  ·
    refine ⟨59200952586379387937232925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78934603448505850582977233 59200952586379387937232925)
    ·
      refine ⟨22200357219892270476462347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 59200952586379387937232925 22200357219892270476462347)
      ·
        refine ⟨33300535829838405714693521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22200357219892270476462347 33300535829838405714693521)
        ·
          refine ⟨24975401872378804286020141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33300535829838405714693521 24975401872378804286020141)
          ·
            refine ⟨9365775702142051607257553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24975401872378804286020141 9365775702142051607257553)
            ·
              refine ⟨7024331776606538705443165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9365775702142051607257553 7024331776606538705443165)
              ·
                refine ⟨2634124416227452014541187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7024331776606538705443165 2634124416227452014541187)
                ·
                  refine ⟨3951186624341178021811781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2634124416227452014541187 3951186624341178021811781)
                  ·
                    refine ⟨740847492063970879089709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3951186624341178021811781 740847492063970879089709)
                    ·
                      rfl

theorem cell22_2164193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 2, 3, 1, 4].length) (baseStart_2164193 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2164193 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2164193 prefixEnd_2164193 := by exact prefixLift 2164193
  have htrace : WordTrace (prefixWord ++ tailWord_2164193) baseStart_2164193 baseEnd_2164193 := by
    simpa [prefixWord, tailWord_2164193, baseEnd_2164193] using wordTrace_append hprefix tailTrace_2164193
  have hstable : (prefixWord ++ tailWord_2164193).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2164193).length < 2 ^ (prefixWord ++ tailWord_2164193).sum := by decide
  have hdescent : baseEnd_2164193 < baseStart_2164193 := by decide
  rcases family_descends (prefixWord ++ tailWord_2164193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2164208 : List Nat := [2, 1, 1, 1, 3, 6, 1, 1, 6]
def baseStart_2164208 : Nat := 118140960795 + 2164208 * 2 ^ 59
def prefixEnd_2164208 : Nat := 4983230072969 + 3 ^ 40 * 2164208 * 2
def baseEnd_2164208 : Nat := 246950875623505279988221

theorem tailTrace_2164208 : CollatzResearch.WordTrace tailWord_2164208 prefixEnd_2164208 246950875623505279988221 := by
  unfold tailWord_2164208
  simp only [CollatzResearch.WordTrace]
  refine ⟨39467575271725754072386639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52623433695634338763182185 39467575271725754072386639)
  ·
    refine ⟨59201362907588631108579959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39467575271725754072386639 59201362907588631108579959)
    ·
      refine ⟨88802044361382946662869939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59201362907588631108579959 88802044361382946662869939)
      ·
        refine ⟨133203066542074419994304909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88802044361382946662869939 133203066542074419994304909)
        ·
          refine ⟨49951149953277907497864341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 133203066542074419994304909 49951149953277907497864341)
          ·
            refine ⟨2341460154059901913962391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 49951149953277907497864341 2341460154059901913962391)
            ·
              refine ⟨3512190231089852870943587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2341460154059901913962391 3512190231089852870943587)
              ·
                refine ⟨5268285346634779306415381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3512190231089852870943587 5268285346634779306415381)
                ·
                  refine ⟨246950875623505279988221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5268285346634779306415381 246950875623505279988221)
                  ·
                    rfl

theorem cell22_2164208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 6, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 6, 1, 1, 6].length) (baseStart_2164208 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2164208 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2164208 prefixEnd_2164208 := by exact prefixLift 2164208
  have htrace : WordTrace (prefixWord ++ tailWord_2164208) baseStart_2164208 baseEnd_2164208 := by
    simpa [prefixWord, tailWord_2164208, baseEnd_2164208] using wordTrace_append hprefix tailTrace_2164208
  have hstable : (prefixWord ++ tailWord_2164208).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2164208).length < 2 ^ (prefixWord ++ tailWord_2164208).sum := by decide
  have hdescent : baseEnd_2164208 < baseStart_2164208 := by decide
  rcases family_descends (prefixWord ++ tailWord_2164208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2164244 : List Nat := [2, 4, 3, 1, 2, 1, 3, 1, 1, 4]
def baseStart_2164244 : Nat := 118140960795 + 2164244 * 2 ^ 59
def prefixEnd_2164244 : Nat := 4983230072969 + 3 ^ 40 * 2164244 * 2
def baseEnd_2164244 : Nat := 740864950406223746064553

theorem tailTrace_2164244 : CollatzResearch.WordTrace tailWord_2164244 prefixEnd_2164244 740864950406223746064553 := by
  unfold tailWord_2164244
  simp only [CollatzResearch.WordTrace]
  refine ⟨39468231785660543146541893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52624309047547390862055857 39468231785660543146541893)
  ·
    refine ⟨7400293459811351839976605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 39468231785660543146541893 7400293459811351839976605)
    ·
      refine ⟨2775110047429256939991227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7400293459811351839976605 2775110047429256939991227)
      ·
        refine ⟨4162665071143885409986841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2775110047429256939991227 4162665071143885409986841)
        ·
          refine ⟨3121998803357914057490131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4162665071143885409986841 3121998803357914057490131)
          ·
            refine ⟨4682998205036871086235197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3121998803357914057490131 4682998205036871086235197)
            ·
              refine ⟨1756124326888826657338199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4682998205036871086235197 1756124326888826657338199)
              ·
                refine ⟨2634186490333239986007299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1756124326888826657338199 2634186490333239986007299)
                ·
                  refine ⟨3951279735499859979010949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2634186490333239986007299 3951279735499859979010949)
                  ·
                    refine ⟨740864950406223746064553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3951279735499859979010949 740864950406223746064553)
                    ·
                      rfl

theorem cell22_2164244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 3, 1, 1, 4].length) (baseStart_2164244 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2164244 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2164244 prefixEnd_2164244 := by exact prefixLift 2164244
  have htrace : WordTrace (prefixWord ++ tailWord_2164244) baseStart_2164244 baseEnd_2164244 := by
    simpa [prefixWord, tailWord_2164244, baseEnd_2164244] using wordTrace_append hprefix tailTrace_2164244
  have hstable : (prefixWord ++ tailWord_2164244).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2164244).length < 2 ^ (prefixWord ++ tailWord_2164244).sum := by decide
  have hdescent : baseEnd_2164244 < baseStart_2164244 := by decide
  rcases family_descends (prefixWord ++ tailWord_2164244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2164259 : List Nat := [1, 1, 1, 4, 6, 1, 2, 2, 4]
def baseStart_2164259 : Nat := 118140960795 + 2164259 * 2 ^ 59
def prefixEnd_2164259 : Nat := 4983230072969 + 3 ^ 40 * 2164259 * 2
def baseEnd_2164259 : Nat := 246956695070922902313169

theorem tailTrace_2164259 : CollatzResearch.WordTrace tailWord_2164259 prefixEnd_2164259 246956695070922902313169 := by
  unfold tailWord_2164259
  simp only [CollatzResearch.WordTrace]
  refine ⟨78937010666266743854879831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52624673777511162569919887 78937010666266743854879831)
  ·
    refine ⟨118405515999400115782319747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78937010666266743854879831 118405515999400115782319747)
    ·
      refine ⟨177608273999100173673479621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118405515999400115782319747 177608273999100173673479621)
      ·
        refine ⟨33301551374831282563777429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 177608273999100173673479621 33301551374831282563777429)
        ·
          refine ⟨1561010220695216370177067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 33301551374831282563777429 1561010220695216370177067)
          ·
            refine ⟨2341515331042824555265601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1561010220695216370177067 2341515331042824555265601)
            ·
              refine ⟨1756136498282118416449201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2341515331042824555265601 1756136498282118416449201)
              ·
                refine ⟨1317102373711588812336901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1756136498282118416449201 1317102373711588812336901)
                ·
                  refine ⟨246956695070922902313169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1317102373711588812336901 246956695070922902313169)
                  ·
                    rfl

theorem cell22_2164259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 6, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 6, 1, 2, 2, 4].length) (baseStart_2164259 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2164259 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2164259 prefixEnd_2164259 := by exact prefixLift 2164259
  have htrace : WordTrace (prefixWord ++ tailWord_2164259) baseStart_2164259 baseEnd_2164259 := by
    simpa [prefixWord, tailWord_2164259, baseEnd_2164259] using wordTrace_append hprefix tailTrace_2164259
  have hstable : (prefixWord ++ tailWord_2164259).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2164259).length < 2 ^ (prefixWord ++ tailWord_2164259).sum := by decide
  have hdescent : baseEnd_2164259 < baseStart_2164259 := by decide
  rcases family_descends (prefixWord ++ tailWord_2164259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2164270 : List Nat := [4, 1, 3, 1, 2, 3, 1, 7]
def baseStart_2164270 : Nat := 118140960795 + 2164270 * 2 ^ 59
def prefixEnd_2164270 : Nat := 4983230072969 + 3 ^ 40 * 2164270 * 2
def baseEnd_2164270 : Nat := 82319316748618704990497

theorem tailTrace_2164270 : CollatzResearch.WordTrace tailWord_2164270 prefixEnd_2164270 82319316748618704990497 := by
  unfold tailWord_2164270
  simp only [CollatzResearch.WordTrace]
  refine ⟨9867176483653361591691283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 52624941246151261822353509 9867176483653361591691283)
  ·
    refine ⟨14800764725480042387536925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9867176483653361591691283 14800764725480042387536925)
    ·
      refine ⟨5550286772055015895326347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14800764725480042387536925 5550286772055015895326347)
      ·
        refine ⟨8325430158082523842989521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5550286772055015895326347 8325430158082523842989521)
        ·
          refine ⟨6244072618561892882242141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8325430158082523842989521 6244072618561892882242141)
          ·
            refine ⟨2341527231960709830840803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6244072618561892882242141 2341527231960709830840803)
            ·
              refine ⟨3512290847941064746261205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2341527231960709830840803 3512290847941064746261205)
              ·
                refine ⟨82319316748618704990497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3512290847941064746261205 82319316748618704990497)
                ·
                  rfl

theorem cell22_2164270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 3, 1, 7].length) (baseStart_2164270 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2164270 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2164270 prefixEnd_2164270 := by exact prefixLift 2164270
  have htrace : WordTrace (prefixWord ++ tailWord_2164270) baseStart_2164270 baseEnd_2164270 := by
    simpa [prefixWord, tailWord_2164270, baseEnd_2164270] using wordTrace_append hprefix tailTrace_2164270
  have hstable : (prefixWord ++ tailWord_2164270).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2164270).length < 2 ^ (prefixWord ++ tailWord_2164270).sum := by decide
  have hdescent : baseEnd_2164270 < baseStart_2164270 := by decide
  rcases family_descends (prefixWord ++ tailWord_2164270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2164345 : List Nat := [1, 2, 1, 3, 3, 1, 4, 2, 1, 4]
def baseStart_2164345 : Nat := 118140960795 + 2164345 * 2 ^ 59
def prefixEnd_2164345 : Nat := 4983230072969 + 3 ^ 40 * 2164345 * 2
def baseEnd_2164345 : Nat := 740899524770293149289243

theorem tailTrace_2164345 : CollatzResearch.WordTrace tailWord_2164345 prefixEnd_2164345 740899524770293149289243 := by
  unfold tailWord_2164345
  simp only [CollatzResearch.WordTrace]
  refine ⟨78940147343955180542510489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52626764895970120361673659 78940147343955180542510489)
  ·
    refine ⟨59205110507966385406882867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78940147343955180542510489 59205110507966385406882867)
    ·
      refine ⟨88807665761949578110324301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59205110507966385406882867 88807665761949578110324301)
      ·
        refine ⟨33302874660731091791371613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 88807665761949578110324301 33302874660731091791371613)
        ·
          refine ⟨12488577997774159421764355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33302874660731091791371613 12488577997774159421764355)
          ·
            refine ⟨18732866996661239132646533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12488577997774159421764355 18732866996661239132646533)
            ·
              refine ⟨3512412561873982337371225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18732866996661239132646533 3512412561873982337371225)
              ·
                refine ⟨2634309421405486753028419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3512412561873982337371225 2634309421405486753028419)
                ·
                  refine ⟨3951464132108230129542629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2634309421405486753028419 3951464132108230129542629)
                  ·
                    refine ⟨740899524770293149289243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3951464132108230129542629 740899524770293149289243)
                    ·
                      rfl

theorem cell22_2164345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 4, 2, 1, 4].length) (baseStart_2164345 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2164345 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2164345 prefixEnd_2164345 := by exact prefixLift 2164345
  have htrace : WordTrace (prefixWord ++ tailWord_2164345) baseStart_2164345 baseEnd_2164345 := by
    simpa [prefixWord, tailWord_2164345, baseEnd_2164345] using wordTrace_append hprefix tailTrace_2164345
  have hstable : (prefixWord ++ tailWord_2164345).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2164345).length < 2 ^ (prefixWord ++ tailWord_2164345).sum := by decide
  have hdescent : baseEnd_2164345 < baseStart_2164345 := by decide
  rcases family_descends (prefixWord ++ tailWord_2164345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2164375 : List Nat := [1, 1, 3, 3, 2, 2, 2, 1, 4, 3]
def baseStart_2164375 : Nat := 118140960795 + 2164375 * 2 ^ 59
def prefixEnd_2164375 : Nat := 4983230072969 + 3 ^ 40 * 2164375 * 2
def baseEnd_2164375 : Nat := 740909794383383071039151

theorem tailTrace_2164375 : CollatzResearch.WordTrace tailWord_2164375 prefixEnd_2164375 740909794383383071039151 := by
  unfold tailWord_2164375
  simp only [CollatzResearch.WordTrace]
  refine ⟨78941241533846495666102579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52627494355897663777401719 78941241533846495666102579)
  ·
    refine ⟨118411862300769743499153869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78941241533846495666102579 118411862300769743499153869)
    ·
      refine ⟨44404448362788653812182701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 118411862300769743499153869 44404448362788653812182701)
      ·
        refine ⟨16651668136045745179568513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44404448362788653812182701 16651668136045745179568513)
        ·
          refine ⟨12488751102034308884676385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16651668136045745179568513 12488751102034308884676385)
          ·
            refine ⟨9366563326525731663507289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12488751102034308884676385 9366563326525731663507289)
            ·
              refine ⟨7024922494894298747630467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9366563326525731663507289 7024922494894298747630467)
              ·
                refine ⟨10537383742341448121445701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7024922494894298747630467 10537383742341448121445701)
                ·
                  refine ⟨1975759451689021522771069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10537383742341448121445701 1975759451689021522771069)
                  ·
                    refine ⟨740909794383383071039151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1975759451689021522771069 740909794383383071039151)
                    ·
                      rfl

theorem cell22_2164375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 2, 1, 4, 3].length) (baseStart_2164375 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2164375 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2164375 prefixEnd_2164375 := by exact prefixLift 2164375
  have htrace : WordTrace (prefixWord ++ tailWord_2164375) baseStart_2164375 baseEnd_2164375 := by
    simpa [prefixWord, tailWord_2164375, baseEnd_2164375] using wordTrace_append hprefix tailTrace_2164375
  have hstable : (prefixWord ++ tailWord_2164375).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2164375).length < 2 ^ (prefixWord ++ tailWord_2164375).sum := by decide
  have hdescent : baseEnd_2164375 < baseStart_2164375 := by decide
  rcases family_descends (prefixWord ++ tailWord_2164375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2164388 : List Nat := [2, 3, 1, 2, 2, 2, 1, 9]
def baseStart_2164388 : Nat := 118140960795 + 2164388 * 2 ^ 59
def prefixEnd_2164388 : Nat := 4983230072969 + 3 ^ 40 * 2164388 * 2
def baseEnd_2164388 : Nat := 82323804949895041162679

theorem tailTrace_2164388 : CollatzResearch.WordTrace tailWord_2164388 prefixEnd_2164388 82323804949895041162679 := by
  unfold tailWord_2164388
  simp only [CollatzResearch.WordTrace]
  refine ⟨39470857841399699443162909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52627810455199599257550545 39470857841399699443162909)
  ·
    refine ⟨14801571690524887291186091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39470857841399699443162909 14801571690524887291186091)
    ·
      refine ⟨22202357535787330936779137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14801571690524887291186091 22202357535787330936779137)
      ·
        refine ⟨16651768151840498202584353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22202357535787330936779137 16651768151840498202584353)
        ·
          refine ⟨12488826113880373651938265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16651768151840498202584353 12488826113880373651938265)
          ·
            refine ⟨9366619585410280238953699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12488826113880373651938265 9366619585410280238953699)
            ·
              refine ⟨14049929378115420358430549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9366619585410280238953699 14049929378115420358430549)
              ·
                refine ⟨82323804949895041162679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 14049929378115420358430549 82323804949895041162679)
                ·
                  rfl

theorem cell22_2164388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 1, 9].length) (baseStart_2164388 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2164388 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2164388 prefixEnd_2164388 := by exact prefixLift 2164388
  have htrace : WordTrace (prefixWord ++ tailWord_2164388) baseStart_2164388 baseEnd_2164388 := by
    simpa [prefixWord, tailWord_2164388, baseEnd_2164388] using wordTrace_append hprefix tailTrace_2164388
  have hstable : (prefixWord ++ tailWord_2164388).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2164388).length < 2 ^ (prefixWord ++ tailWord_2164388).sum := by decide
  have hdescent : baseEnd_2164388 < baseStart_2164388 := by decide
  rcases family_descends (prefixWord ++ tailWord_2164388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2164422 : List Nat := [6, 1, 2, 1, 1, 11]
def baseStart_2164422 : Nat := 118140960795 + 2164422 * 2 ^ 59
def prefixEnd_2164422 : Nat := 4983230072969 + 3 ^ 40 * 2164422 * 2
def baseEnd_2164422 : Nat := 9147233128936921174247

theorem tailTrace_2164422 : CollatzResearch.WordTrace tailWord_2164422 prefixEnd_2164422 9147233128936921174247 := by
  unfold tailWord_2164422
  simp only [CollatzResearch.WordTrace]
  refine ⟨2466967367646131959158235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 52628637176450815128709013 2466967367646131959158235)
  ·
    refine ⟨3700451051469197938737353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2466967367646131959158235 3700451051469197938737353)
    ·
      refine ⟨2775338288601898454053015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3700451051469197938737353 2775338288601898454053015)
      ·
        refine ⟨4163007432902847681079523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2775338288601898454053015 4163007432902847681079523)
        ·
          refine ⟨6244511149354271521619285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4163007432902847681079523 6244511149354271521619285)
          ·
            refine ⟨9147233128936921174247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 6244511149354271521619285 9147233128936921174247)
            ·
              rfl

theorem cell22_2164422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 11].length) (baseStart_2164422 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2164422 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2164422 prefixEnd_2164422 := by exact prefixLift 2164422
  have htrace : WordTrace (prefixWord ++ tailWord_2164422) baseStart_2164422 baseEnd_2164422 := by
    simpa [prefixWord, tailWord_2164422, baseEnd_2164422] using wordTrace_append hprefix tailTrace_2164422
  have hstable : (prefixWord ++ tailWord_2164422).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2164422).length < 2 ^ (prefixWord ++ tailWord_2164422).sum := by decide
  have hdescent : baseEnd_2164422 < baseStart_2164422 := by decide
  rcases family_descends (prefixWord ++ tailWord_2164422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2164448 : List Nat := [2, 1, 1, 3, 1, 2, 3, 1, 1, 7]
def baseStart_2164448 : Nat := 118140960795 + 2164448 * 2 ^ 59
def prefixEnd_2164448 : Nat := 4983230072969 + 3 ^ 40 * 2164448 * 2
def baseEnd_2164448 : Nat := 740934783775235213963927

theorem tailTrace_2164448 : CollatzResearch.WordTrace tailWord_2164448 prefixEnd_2164448 740934783775235213963927 := by
  unfold tailWord_2164448
  simp only [CollatzResearch.WordTrace]
  refine ⟨39471952031291014566754999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52629269375054686089006665 39471952031291014566754999)
  ·
    refine ⟨59207928046936521850132499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39471952031291014566754999 59207928046936521850132499)
    ·
      refine ⟨88811892070404782775198749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59207928046936521850132499 88811892070404782775198749)
      ·
        refine ⟨33304459526401793540699531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 88811892070404782775198749 33304459526401793540699531)
        ·
          refine ⟨49956689289602690311049297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33304459526401793540699531 49956689289602690311049297)
          ·
            refine ⟨37467516967202017733286973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49956689289602690311049297 37467516967202017733286973)
            ·
              refine ⟨14050318862700756649982615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37467516967202017733286973 14050318862700756649982615)
              ·
                refine ⟨21075478294051134974973923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14050318862700756649982615 21075478294051134974973923)
                ·
                  refine ⟨31613217441076702462460885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21075478294051134974973923 31613217441076702462460885)
                  ·
                    refine ⟨740934783775235213963927, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 31613217441076702462460885 740934783775235213963927)
                    ·
                      rfl

theorem cell22_2164448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 3, 1, 1, 7].length) (baseStart_2164448 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2164448 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2164448 prefixEnd_2164448 := by exact prefixLift 2164448
  have htrace : WordTrace (prefixWord ++ tailWord_2164448) baseStart_2164448 baseEnd_2164448 := by
    simpa [prefixWord, tailWord_2164448, baseEnd_2164448] using wordTrace_append hprefix tailTrace_2164448
  have hstable : (prefixWord ++ tailWord_2164448).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2164448).length < 2 ^ (prefixWord ++ tailWord_2164448).sum := by decide
  have hdescent : baseEnd_2164448 < baseStart_2164448 := by decide
  rcases family_descends (prefixWord ++ tailWord_2164448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2164480 : List Nat := [2, 1, 1, 2, 1, 1, 2, 7, 1, 4]
def baseStart_2164480 : Nat := 118140960795 + 2164480 * 2 ^ 59
def prefixEnd_2164480 : Nat := 4983230072969 + 3 ^ 40 * 2164480 * 2
def baseEnd_2164480 : Nat := 740945738029197797163829

theorem tailTrace_2164480 : CollatzResearch.WordTrace tailWord_2164480 prefixEnd_2164480 740945738029197797163829 := by
  unfold tailWord_2164480
  simp only [CollatzResearch.WordTrace]
  refine ⟨39472535599233049299337447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52630047465644065732449929 39472535599233049299337447)
  ·
    refine ⟨59208803398849573949006171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39472535599233049299337447 59208803398849573949006171)
    ·
      refine ⟨88813205098274360923509257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59208803398849573949006171 88813205098274360923509257)
      ·
        refine ⟨66609903823705770692631943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 88813205098274360923509257 66609903823705770692631943)
        ·
          refine ⟨99914855735558656038947915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66609903823705770692631943 99914855735558656038947915)
          ·
            refine ⟨149872283603337984058421873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 99914855735558656038947915 149872283603337984058421873)
            ·
              refine ⟨112404212702503488043816405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 149872283603337984058421873 112404212702503488043816405)
              ·
                refine ⟨2634473735214925501026947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 112404212702503488043816405 2634473735214925501026947)
                ·
                  refine ⟨3951710602822388251540421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2634473735214925501026947 3951710602822388251540421)
                  ·
                    refine ⟨740945738029197797163829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3951710602822388251540421 740945738029197797163829)
                    ·
                      rfl

theorem cell22_2164480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 7, 1, 4].length) (baseStart_2164480 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2164480 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2164480 prefixEnd_2164480 := by exact prefixLift 2164480
  have htrace : WordTrace (prefixWord ++ tailWord_2164480) baseStart_2164480 baseEnd_2164480 := by
    simpa [prefixWord, tailWord_2164480, baseEnd_2164480] using wordTrace_append hprefix tailTrace_2164480
  have hstable : (prefixWord ++ tailWord_2164480).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2164480).length < 2 ^ (prefixWord ++ tailWord_2164480).sum := by decide
  have hdescent : baseEnd_2164480 < baseStart_2164480 := by decide
  rcases family_descends (prefixWord ++ tailWord_2164480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2164529 : List Nat := [1, 2, 2, 3, 2, 4, 1, 3, 4]
def baseStart_2164529 : Nat := 118140960795 + 2164529 * 2 ^ 59
def prefixEnd_2164529 : Nat := 4983230072969 + 3 ^ 40 * 2164529 * 2
def baseEnd_2164529 : Nat := 246987503910192667562893

theorem tailTrace_2164529 : CollatzResearch.WordTrace tailWord_2164529 prefixEnd_2164529 246987503910192667562893 := by
  unfold tailWord_2164529
  simp only [CollatzResearch.WordTrace]
  refine ⟨78946858375288579967208641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52631238916859053311472427 78946858375288579967208641)
  ·
    refine ⟨59210143781466434975406481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78946858375288579967208641 59210143781466434975406481)
    ·
      refine ⟨44407607836099826231554861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59210143781466434975406481 44407607836099826231554861)
      ·
        refine ⟨16652852938537434836833073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44407607836099826231554861 16652852938537434836833073)
        ·
          refine ⟨12489639703903076127624805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16652852938537434836833073 12489639703903076127624805)
          ·
            refine ⟨2341807444481826773929651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12489639703903076127624805 2341807444481826773929651)
            ·
              refine ⟨3512711166722740160894477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2341807444481826773929651 3512711166722740160894477)
              ·
                refine ⟨1317266687521027560335429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3512711166722740160894477 1317266687521027560335429)
                ·
                  refine ⟨246987503910192667562893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1317266687521027560335429 246987503910192667562893)
                  ·
                    rfl

theorem cell22_2164529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 4, 1, 3, 4].length) (baseStart_2164529 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2164529 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2164529 prefixEnd_2164529 := by exact prefixLift 2164529
  have htrace : WordTrace (prefixWord ++ tailWord_2164529) baseStart_2164529 baseEnd_2164529 := by
    simpa [prefixWord, tailWord_2164529, baseEnd_2164529] using wordTrace_append hprefix tailTrace_2164529
  have hstable : (prefixWord ++ tailWord_2164529).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2164529).length < 2 ^ (prefixWord ++ tailWord_2164529).sum := by decide
  have hdescent : baseEnd_2164529 < baseStart_2164529 := by decide
  rcases family_descends (prefixWord ++ tailWord_2164529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2164542 : List Nat := [4, 2, 1, 2, 2, 1, 1, 1, 4, 4]
def baseStart_2164542 : Nat := 118140960795 + 2164542 * 2 ^ 59
def prefixEnd_2164542 : Nat := 4983230072969 + 3 ^ 40 * 2164542 * 2
def baseEnd_2164542 : Nat := 740966961896250302113639

theorem tailTrace_2164542 : CollatzResearch.WordTrace tailWord_2164542 prefixEnd_2164542 740966961896250302113639 := by
  unfold tailWord_2164542
  simp only [CollatzResearch.WordTrace]
  refine ⟨9868416565530185398428985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 52631555016160988791621253 9868416565530185398428985)
  ·
    refine ⟨7401312424147639048821739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9868416565530185398428985 7401312424147639048821739)
    ·
      refine ⟨11101968636221458573232609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7401312424147639048821739 11101968636221458573232609)
      ·
        refine ⟨8326476477166093929924457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11101968636221458573232609 8326476477166093929924457)
        ·
          refine ⟨6244857357874570447443343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8326476477166093929924457 6244857357874570447443343)
          ·
            refine ⟨9367286036811855671165015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6244857357874570447443343 9367286036811855671165015)
            ·
              refine ⟨14050929055217783506747523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9367286036811855671165015 14050929055217783506747523)
              ·
                refine ⟨21076393582826675260121285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14050929055217783506747523 21076393582826675260121285)
                ·
                  refine ⟨3951823796780001611272741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21076393582826675260121285 3951823796780001611272741)
                  ·
                    refine ⟨740966961896250302113639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3951823796780001611272741 740966961896250302113639)
                    ·
                      rfl

theorem cell22_2164542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 1, 1, 4, 4].length) (baseStart_2164542 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2164542 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2164542 prefixEnd_2164542 := by exact prefixLift 2164542
  have htrace : WordTrace (prefixWord ++ tailWord_2164542) baseStart_2164542 baseEnd_2164542 := by
    simpa [prefixWord, tailWord_2164542, baseEnd_2164542] using wordTrace_append hprefix tailTrace_2164542
  have hstable : (prefixWord ++ tailWord_2164542).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2164542).length < 2 ^ (prefixWord ++ tailWord_2164542).sum := by decide
  have hdescent : baseEnd_2164542 < baseStart_2164542 := by decide
  rcases family_descends (prefixWord ++ tailWord_2164542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2164557 : List Nat := [1, 6, 1, 2, 1, 1, 1, 9]
def baseStart_2164557 : Nat := 118140960795 + 2164557 * 2 ^ 59
def prefixEnd_2164557 : Nat := 4983230072969 + 3 ^ 40 * 2164557 * 2
def baseEnd_2164557 : Nat := 82330232966977251443177

theorem tailTrace_2164557 : CollatzResearch.WordTrace tailWord_2164557 prefixEnd_2164557 82330232966977251443177 := by
  unfold tailWord_2164557
  simp only [CollatzResearch.WordTrace]
  refine ⟨78947879619187140749227925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52631919746124760499485283 78947879619187140749227925)
  ·
    refine ⟨3700681857149397222620059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 78947879619187140749227925 3700681857149397222620059)
    ·
      refine ⟨5551022785724095833930089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3700681857149397222620059 5551022785724095833930089)
      ·
        refine ⟨4163267089293071875447567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5551022785724095833930089 4163267089293071875447567)
        ·
          refine ⟨6244900633939607813171351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4163267089293071875447567 6244900633939607813171351)
          ·
            refine ⟨9367350950909411719757027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6244900633939607813171351 9367350950909411719757027)
            ·
              refine ⟨14051026426364117579635541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9367350950909411719757027 14051026426364117579635541)
              ·
                refine ⟨82330232966977251443177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 14051026426364117579635541 82330232966977251443177)
                ·
                  rfl

theorem cell22_2164557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 1, 9].length) (baseStart_2164557 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2164557 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2164557 prefixEnd_2164557 := by exact prefixLift 2164557
  have htrace : WordTrace (prefixWord ++ tailWord_2164557) baseStart_2164557 baseEnd_2164557 := by
    simpa [prefixWord, tailWord_2164557, baseEnd_2164557] using wordTrace_append hprefix tailTrace_2164557
  have hstable : (prefixWord ++ tailWord_2164557).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2164557).length < 2 ^ (prefixWord ++ tailWord_2164557).sum := by decide
  have hdescent : baseEnd_2164557 < baseStart_2164557 := by decide
  rcases family_descends (prefixWord ++ tailWord_2164557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2164561 : List Nat := [1, 2, 2, 1, 5, 3, 2, 1, 2, 3]
def baseStart_2164561 : Nat := 118140960795 + 2164561 * 2 ^ 59
def prefixEnd_2164561 : Nat := 4983230072969 + 3 ^ 40 * 2164561 * 2
def baseEnd_2164561 : Nat := 740973465984540585888581

theorem tailTrace_2164561 : CollatzResearch.WordTrace tailWord_2164561 prefixEnd_2164561 740973465984540585888581 := by
  unfold tailWord_2164561
  simp only [CollatzResearch.WordTrace]
  refine ⟨78948025511172649432373537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52632017007448432954915691 78948025511172649432373537)
  ·
    refine ⟨59211019133379487074280153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78948025511172649432373537 59211019133379487074280153)
    ·
      refine ⟨44408264350034615305710115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59211019133379487074280153 44408264350034615305710115)
      ·
        refine ⟨66612396525051922958565173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44408264350034615305710115 66612396525051922958565173)
        ·
          refine ⟨6244912174223617777365485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 66612396525051922958565173 6244912174223617777365485)
          ·
            refine ⟨2341842065333856666512057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6244912174223617777365485 2341842065333856666512057)
            ·
              refine ⟨1756381549000392499884043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2341842065333856666512057 1756381549000392499884043)
              ·
                refine ⟨2634572323500588749826065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1756381549000392499884043 2634572323500588749826065)
                ·
                  refine ⟨1975929242625441562369549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2634572323500588749826065 1975929242625441562369549)
                  ·
                    refine ⟨740973465984540585888581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1975929242625441562369549 740973465984540585888581)
                    ·
                      rfl

theorem cell22_2164561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 3, 2, 1, 2, 3].length) (baseStart_2164561 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2164561 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2164561 prefixEnd_2164561 := by exact prefixLift 2164561
  have htrace : WordTrace (prefixWord ++ tailWord_2164561) baseStart_2164561 baseEnd_2164561 := by
    simpa [prefixWord, tailWord_2164561, baseEnd_2164561] using wordTrace_append hprefix tailTrace_2164561
  have hstable : (prefixWord ++ tailWord_2164561).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2164561).length < 2 ^ (prefixWord ++ tailWord_2164561).sum := by decide
  have hdescent : baseEnd_2164561 < baseStart_2164561 := by decide
  rcases family_descends (prefixWord ++ tailWord_2164561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2164692 : List Nat := [2, 4, 1, 2, 1, 1, 3, 8]
def baseStart_2164692 : Nat := 118140960795 + 2164692 * 2 ^ 59
def prefixEnd_2164692 : Nat := 4983230072969 + 3 ^ 40 * 2164692 * 2
def baseEnd_2164692 : Nat := 82335367773522212318131

theorem tailTrace_2164692 : CollatzResearch.WordTrace tailWord_2164692 prefixEnd_2164692 82335367773522212318131 := by
  unfold tailWord_2164692
  simp only [CollatzResearch.WordTrace]
  refine ⟨39476401736849029402696165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52635202315798705870261553 39476401736849029402696165)
  ·
    refine ⟨7401825325659193013005531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 39476401736849029402696165 7401825325659193013005531)
    ·
      refine ⟨11102737988488789519508297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7401825325659193013005531 11102737988488789519508297)
      ·
        refine ⟨8327053491366592139631223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11102737988488789519508297 8327053491366592139631223)
        ·
          refine ⟨12490580237049888209446835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8327053491366592139631223 12490580237049888209446835)
          ·
            refine ⟨18735870355574832314170253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12490580237049888209446835 18735870355574832314170253)
            ·
              refine ⟨7025951383340562117813845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18735870355574832314170253 7025951383340562117813845)
              ·
                refine ⟨82335367773522212318131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7025951383340562117813845 82335367773522212318131)
                ·
                  rfl

theorem cell22_2164692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 3, 8].length) (baseStart_2164692 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2164692 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2164692 prefixEnd_2164692 := by exact prefixLift 2164692
  have htrace : WordTrace (prefixWord ++ tailWord_2164692) baseStart_2164692 baseEnd_2164692 := by
    simpa [prefixWord, tailWord_2164692, baseEnd_2164692] using wordTrace_append hprefix tailTrace_2164692
  have hstable : (prefixWord ++ tailWord_2164692).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2164692).length < 2 ^ (prefixWord ++ tailWord_2164692).sum := by decide
  have hdescent : baseEnd_2164692 < baseStart_2164692 := by decide
  rcases family_descends (prefixWord ++ tailWord_2164692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2164698 : List Nat := [3, 1, 1, 2, 6, 1, 1, 3, 4]
def baseStart_2164698 : Nat := 118140960795 + 2164698 * 2 ^ 59
def prefixEnd_2164698 : Nat := 4983230072969 + 3 ^ 40 * 2164698 * 2
def baseEnd_2164698 : Nat := 247006787961439298404387

theorem tailTrace_2164698 : CollatzResearch.WordTrace tailWord_2164698 prefixEnd_2164698 247006787961439298404387 := by
  unfold tailWord_2164698
  simp only [CollatzResearch.WordTrace]
  refine ⟨19738255577919080457527687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52635348207784214553407165 19738255577919080457527687)
  ·
    refine ⟨29607383366878620686291531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19738255577919080457527687 29607383366878620686291531)
    ·
      refine ⟨44411075050317931029437297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29607383366878620686291531 44411075050317931029437297)
      ·
        refine ⟨33308306287738448272077973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44411075050317931029437297 33308306287738448272077973)
        ·
          refine ⟨1561326857237739762753655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 33308306287738448272077973 1561326857237739762753655)
          ·
            refine ⟨2341990285856609644130483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1561326857237739762753655 2341990285856609644130483)
            ·
              refine ⟨3512985428784914466195725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2341990285856609644130483 3512985428784914466195725)
              ·
                refine ⟨1317369535794342924823397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3512985428784914466195725 1317369535794342924823397)
                ·
                  refine ⟨247006787961439298404387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1317369535794342924823397 247006787961439298404387)
                  ·
                    rfl

theorem cell22_2164698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 6, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 6, 1, 1, 3, 4].length) (baseStart_2164698 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2164698 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2164698 prefixEnd_2164698 := by exact prefixLift 2164698
  have htrace : WordTrace (prefixWord ++ tailWord_2164698) baseStart_2164698 baseEnd_2164698 := by
    simpa [prefixWord, tailWord_2164698, baseEnd_2164698] using wordTrace_append hprefix tailTrace_2164698
  have hstable : (prefixWord ++ tailWord_2164698).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2164698).length < 2 ^ (prefixWord ++ tailWord_2164698).sum := by decide
  have hdescent : baseEnd_2164698 < baseStart_2164698 := by decide
  rcases family_descends (prefixWord ++ tailWord_2164698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2164775 : List Nat := [1, 1, 7, 1, 2, 1, 1, 4, 1, 3]
def baseStart_2164775 : Nat := 118140960795 + 2164775 * 2 ^ 59
def prefixEnd_2164775 : Nat := 4983230072969 + 3 ^ 40 * 2164775 * 2
def baseEnd_2164775 : Nat := 741046722557915361037925

theorem tailTrace_2164775 : CollatzResearch.WordTrace tailWord_2164775 prefixEnd_2164775 741046722557915361037925 := by
  unfold tailWord_2164775
  simp only [CollatzResearch.WordTrace]
  refine ⟨78955830732397363980663779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52637220488264909320442519 78955830732397363980663779)
  ·
    refine ⟨118433746098596045970995669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78955830732397363980663779 118433746098596045970995669)
    ·
      refine ⟨2775790924185844827445211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 118433746098596045970995669 2775790924185844827445211)
      ·
        refine ⟨4163686386278767241167817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2775790924185844827445211 4163686386278767241167817)
        ·
          refine ⟨3122764789709075430875863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4163686386278767241167817 3122764789709075430875863)
          ·
            refine ⟨4684147184563613146313795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3122764789709075430875863 4684147184563613146313795)
            ·
              refine ⟨7026220776845419719470693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4684147184563613146313795 7026220776845419719470693)
              ·
                refine ⟨1317416395658516197400755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7026220776845419719470693 1317416395658516197400755)
                ·
                  refine ⟨1976124593487774296101133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1317416395658516197400755 1976124593487774296101133)
                  ·
                    refine ⟨741046722557915361037925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1976124593487774296101133 741046722557915361037925)
                    ·
                      rfl

theorem cell22_2164775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 1, 4, 1, 3].length) (baseStart_2164775 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2164775 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2164775 prefixEnd_2164775 := by exact prefixLift 2164775
  have htrace : WordTrace (prefixWord ++ tailWord_2164775) baseStart_2164775 baseEnd_2164775 := by
    simpa [prefixWord, tailWord_2164775, baseEnd_2164775] using wordTrace_append hprefix tailTrace_2164775
  have hstable : (prefixWord ++ tailWord_2164775).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2164775).length < 2 ^ (prefixWord ++ tailWord_2164775).sum := by decide
  have hdescent : baseEnd_2164775 < baseStart_2164775 := by decide
  rcases family_descends (prefixWord ++ tailWord_2164775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2164814 : List Nat := [4, 1, 1, 1, 1, 4, 2, 2, 1, 5]
def baseStart_2164814 : Nat := 118140960795 + 2164814 * 2 ^ 59
def prefixEnd_2164814 : Nat := 4983230072969 + 3 ^ 40 * 2164814 * 2
def baseEnd_2164814 : Nat := 741060073054932259312805

theorem tailTrace_2164814 : CollatzResearch.WordTrace tailWord_2164814 prefixEnd_2164814 741060073054932259312805 := by
  unfold tailWord_2164814
  simp only [CollatzResearch.WordTrace]
  refine ⟨9869656647407009205166687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 52638168786170715760888997 9869656647407009205166687)
  ·
    refine ⟨14804484971110513807750031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9869656647407009205166687 14804484971110513807750031)
    ·
      refine ⟨22206727456665770711625047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14804484971110513807750031 22206727456665770711625047)
      ·
        refine ⟨33310091184998656067437571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22206727456665770711625047 33310091184998656067437571)
        ·
          refine ⟨49965136777497984101156357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33310091184998656067437571 49965136777497984101156357)
          ·
            refine ⟨9368463145780872018966817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 49965136777497984101156357 9368463145780872018966817)
            ·
              refine ⟨7026347359335654014225113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9368463145780872018966817 7026347359335654014225113)
              ·
                refine ⟨5269760519501740510668835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7026347359335654014225113 5269760519501740510668835)
                ·
                  refine ⟨7904640779252610766003253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5269760519501740510668835 7904640779252610766003253)
                  ·
                    refine ⟨741060073054932259312805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7904640779252610766003253 741060073054932259312805)
                    ·
                      rfl

theorem cell22_2164814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 2, 2, 1, 5].length) (baseStart_2164814 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2164814 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2164814 prefixEnd_2164814 := by exact prefixLift 2164814
  have htrace : WordTrace (prefixWord ++ tailWord_2164814) baseStart_2164814 baseEnd_2164814 := by
    simpa [prefixWord, tailWord_2164814, baseEnd_2164814] using wordTrace_append hprefix tailTrace_2164814
  have hstable : (prefixWord ++ tailWord_2164814).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2164814).length < 2 ^ (prefixWord ++ tailWord_2164814).sum := by decide
  have hdescent : baseEnd_2164814 < baseStart_2164814 := by decide
  rcases family_descends (prefixWord ++ tailWord_2164814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2164848 : List Nat := [2, 1, 1, 1, 5, 3, 3, 1, 2, 3]
def baseStart_2164848 : Nat := 118140960795 + 2164848 * 2 ^ 59
def prefixEnd_2164848 : Nat := 4983230072969 + 3 ^ 40 * 2164848 * 2
def baseEnd_2164848 : Nat := 741071711949767503962701

theorem tailTrace_2164848 : CollatzResearch.WordTrace tailWord_2164848 prefixEnd_2164848 741071711949767503962701 := by
  unfold tailWord_2164848
  simp only [CollatzResearch.WordTrace]
  refine ⟨39479246630566448724035599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52638995507421931632047465 39479246630566448724035599)
  ·
    refine ⟨59218869945849673086053399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39479246630566448724035599 59218869945849673086053399)
    ·
      refine ⟨88828304918774509629080099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59218869945849673086053399 88828304918774509629080099)
      ·
        refine ⟨133242457378161764443620149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88828304918774509629080099 133242457378161764443620149)
        ·
          refine ⟨12491480379202665416589389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 133242457378161764443620149 12491480379202665416589389)
          ·
            refine ⟨4684305142200999531221021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12491480379202665416589389 4684305142200999531221021)
            ·
              refine ⟨1756614428325374824207883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4684305142200999531221021 1756614428325374824207883)
              ·
                refine ⟨2634921642488062236311825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1756614428325374824207883 2634921642488062236311825)
                ·
                  refine ⟨1976191231866046677233869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2634921642488062236311825 1976191231866046677233869)
                  ·
                    refine ⟨741071711949767503962701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1976191231866046677233869 741071711949767503962701)
                    ·
                      rfl

theorem cell22_2164848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 3, 1, 2, 3].length) (baseStart_2164848 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2164848 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2164848 prefixEnd_2164848 := by exact prefixLift 2164848
  have htrace : WordTrace (prefixWord ++ tailWord_2164848) baseStart_2164848 baseEnd_2164848 := by
    simpa [prefixWord, tailWord_2164848, baseEnd_2164848] using wordTrace_append hprefix tailTrace_2164848
  have hstable : (prefixWord ++ tailWord_2164848).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2164848).length < 2 ^ (prefixWord ++ tailWord_2164848).sum := by decide
  have hdescent : baseEnd_2164848 < baseStart_2164848 := by decide
  rcases family_descends (prefixWord ++ tailWord_2164848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2164861 : List Nat := [1, 4, 1, 1, 3, 4, 2, 6]
def baseStart_2164861 : Nat := 118140960795 + 2164861 * 2 ^ 59
def prefixEnd_2164861 : Nat := 4983230072969 + 3 ^ 40 * 2164861 * 2
def baseEnd_2164861 : Nat := 82341795790604422598629

theorem tailTrace_2164861 : CollatzResearch.WordTrace tailWord_2164861 prefixEnd_2164861 82341795790604422598629 := by
  unfold tailWord_2164861
  simp only [CollatzResearch.WordTrace]
  refine ⟨78958967410085800668294437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52639311606723867112196291 78958967410085800668294437)
  ·
    refine ⟨14804806389391087625305207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 78958967410085800668294437 14804806389391087625305207)
    ·
      refine ⟨22207209584086631437957811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14804806389391087625305207 22207209584086631437957811)
      ·
        refine ⟨33310814376129947156936717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22207209584086631437957811 33310814376129947156936717)
        ·
          refine ⟨12491555391048730183851269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33310814376129947156936717 12491555391048730183851269)
          ·
            refine ⟨2342166635821636909472113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12491555391048730183851269 2342166635821636909472113)
            ·
              refine ⟨1756624976866227682104085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2342166635821636909472113 1756624976866227682104085)
              ·
                refine ⟨82341795790604422598629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1756624976866227682104085 82341795790604422598629)
                ·
                  rfl

theorem cell22_2164861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 4, 2, 6].length) (baseStart_2164861 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2164861 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2164861 prefixEnd_2164861 := by exact prefixLift 2164861
  have htrace : WordTrace (prefixWord ++ tailWord_2164861) baseStart_2164861 baseEnd_2164861 := by
    simpa [prefixWord, tailWord_2164861, baseEnd_2164861] using wordTrace_append hprefix tailTrace_2164861
  have hstable : (prefixWord ++ tailWord_2164861).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2164861).length < 2 ^ (prefixWord ++ tailWord_2164861).sum := by decide
  have hdescent : baseEnd_2164861 < baseStart_2164861 := by decide
  rcases family_descends (prefixWord ++ tailWord_2164861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2164893 : List Nat := [1, 4, 2, 1, 1, 5, 1, 1, 3, 3]
def baseStart_2164893 : Nat := 118140960795 + 2164893 * 2 ^ 59
def prefixEnd_2164893 : Nat := 4983230072969 + 3 ^ 40 * 2164893 * 2
def baseEnd_2164893 : Nat := 741087116369402386587563

theorem tailTrace_2164893 : CollatzResearch.WordTrace tailWord_2164893 prefixEnd_2164893 741087116369402386587563 := by
  unfold tailWord_2164893
  simp only [CollatzResearch.WordTrace]
  refine ⟨78960134545969870133459333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52640089697313246755639555 78960134545969870133459333)
  ·
    refine ⟨14805025227369350650023625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 78960134545969870133459333 14805025227369350650023625)
    ·
      refine ⟨11103768920527012987517719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14805025227369350650023625 11103768920527012987517719)
      ·
        refine ⟨16655653380790519481276579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11103768920527012987517719 16655653380790519481276579)
        ·
          refine ⟨24983480071185779221914869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16655653380790519481276579 24983480071185779221914869)
          ·
            refine ⟨2342201256673666802054519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 24983480071185779221914869 2342201256673666802054519)
            ·
              refine ⟨3513301885010500203081779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2342201256673666802054519 3513301885010500203081779)
              ·
                refine ⟨5269952827515750304622669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3513301885010500203081779 5269952827515750304622669)
                ·
                  refine ⟨1976232310318406364233501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5269952827515750304622669 1976232310318406364233501)
                  ·
                    refine ⟨741087116369402386587563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1976232310318406364233501 741087116369402386587563)
                    ·
                      rfl

theorem cell22_2164893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 5, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 5, 1, 1, 3, 3].length) (baseStart_2164893 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2164893 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2164893 prefixEnd_2164893 := by exact prefixLift 2164893
  have htrace : WordTrace (prefixWord ++ tailWord_2164893) baseStart_2164893 baseEnd_2164893 := by
    simpa [prefixWord, tailWord_2164893, baseEnd_2164893] using wordTrace_append hprefix tailTrace_2164893
  have hstable : (prefixWord ++ tailWord_2164893).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2164893).length < 2 ^ (prefixWord ++ tailWord_2164893).sum := by decide
  have hdescent : baseEnd_2164893 < baseStart_2164893 := by decide
  rcases family_descends (prefixWord ++ tailWord_2164893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2164964 : List Nat := [2, 3, 1, 1, 1, 2, 1, 4, 1, 6]
def baseStart_2164964 : Nat := 118140960795 + 2164964 * 2 ^ 59
def prefixEnd_2164964 : Nat := 4983230072969 + 3 ^ 40 * 2164964 * 2
def baseEnd_2164964 : Nat := 741111421120381868062345

theorem tailTrace_2164964 : CollatzResearch.WordTrace tailWord_2164964 prefixEnd_2164964 741111421120381868062345 := by
  unfold tailWord_2164964
  simp only [CollatzResearch.WordTrace]
  refine ⟨39481362064356324629646973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52641816085808432839529297 39481362064356324629646973)
  ·
    refine ⟨14805510774133621736117615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39481362064356324629646973 14805510774133621736117615)
    ·
      refine ⟨22208266161200432604176423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14805510774133621736117615 22208266161200432604176423)
      ·
        refine ⟨33312399241800648906264635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22208266161200432604176423 33312399241800648906264635)
        ·
          refine ⟨49968598862700973359396953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33312399241800648906264635 49968598862700973359396953)
          ·
            refine ⟨37476449147025730019547715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49968598862700973359396953 37476449147025730019547715)
            ·
              refine ⟨56214673720538595029321573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37476449147025730019547715 56214673720538595029321573)
              ·
                refine ⟨10540251322600986567997795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 56214673720538595029321573 10540251322600986567997795)
                ·
                  refine ⟨15810376983901479851996693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10540251322600986567997795 15810376983901479851996693)
                  ·
                    refine ⟨741111421120381868062345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15810376983901479851996693 741111421120381868062345)
                    ·
                      rfl

theorem cell22_2164964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 4, 1, 6].length) (baseStart_2164964 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2164964 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2164964 prefixEnd_2164964 := by exact prefixLift 2164964
  have htrace : WordTrace (prefixWord ++ tailWord_2164964) baseStart_2164964 baseEnd_2164964 := by
    simpa [prefixWord, tailWord_2164964, baseEnd_2164964] using wordTrace_append hprefix tailTrace_2164964
  have hstable : (prefixWord ++ tailWord_2164964).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2164964).length < 2 ^ (prefixWord ++ tailWord_2164964).sum := by decide
  have hdescent : baseEnd_2164964 < baseStart_2164964 := by decide
  rcases family_descends (prefixWord ++ tailWord_2164964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2164996 : List Nat := [2, 3, 2, 2, 3, 1, 9]
def baseStart_2164996 : Nat := 118140960795 + 2164996 * 2 ^ 59
def prefixEnd_2164996 : Nat := 4983230072969 + 3 ^ 40 * 2164996 * 2
def baseEnd_2164996 : Nat := 27448976865716461157861

theorem tailTrace_2164996 : CollatzResearch.WordTrace tailWord_2164996 prefixEnd_2164996 27448976865716461157861 := by
  unfold tailWord_2164996
  simp only [CollatzResearch.WordTrace]
  refine ⟨39481945632298359362229421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52642594176397812482972561 39481945632298359362229421)
  ·
    refine ⟨14805729612111884760836033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39481945632298359362229421 14805729612111884760836033)
    ·
      refine ⟨11104297209083913570627025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14805729612111884760836033 11104297209083913570627025)
      ·
        refine ⟨8328222906812935177970269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11104297209083913570627025 8328222906812935177970269)
        ·
          refine ⟨3123083590054850691738851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8328222906812935177970269 3123083590054850691738851)
          ·
            refine ⟨4684625385082276037608277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3123083590054850691738851 4684625385082276037608277)
            ·
              refine ⟨27448976865716461157861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4684625385082276037608277 27448976865716461157861)
              ·
                rfl

theorem cell22_2164996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 9].length) (baseStart_2164996 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2164996 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2164996 prefixEnd_2164996 := by exact prefixLift 2164996
  have htrace : WordTrace (prefixWord ++ tailWord_2164996) baseStart_2164996 baseEnd_2164996 := by
    simpa [prefixWord, tailWord_2164996, baseEnd_2164996] using wordTrace_append hprefix tailTrace_2164996
  have hstable : (prefixWord ++ tailWord_2164996).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2164996).length < 2 ^ (prefixWord ++ tailWord_2164996).sum := by decide
  have hdescent : baseEnd_2164996 < baseStart_2164996 := by decide
  rcases family_descends (prefixWord ++ tailWord_2164996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2165000 : List Nat := [2, 1, 3, 2, 3, 3, 1, 2, 2, 3]
def baseStart_2165000 : Nat := 118140960795 + 2165000 * 2 ^ 59
def prefixEnd_2165000 : Nat := 4983230072969 + 3 ^ 40 * 2165000 * 2
def baseEnd_2165000 : Nat := 741123744656089774162235

theorem tailTrace_2165000 : CollatzResearch.WordTrace tailWord_2165000 prefixEnd_2165000 741123744656089774162235 := by
  unfold tailWord_2165000
  simp only [CollatzResearch.WordTrace]
  refine ⟨39482018578291113703802227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52642691437721484938402969 39482018578291113703802227)
  ·
    refine ⟨59223027867436670555703341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39482018578291113703802227 59223027867436670555703341)
    ·
      refine ⟨22208635450288751458388753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 59223027867436670555703341 22208635450288751458388753)
      ·
        refine ⟨16656476587716563593791565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22208635450288751458388753 16656476587716563593791565)
        ·
          refine ⟨6246178720393711347671837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16656476587716563593791565 6246178720393711347671837)
          ·
            refine ⟨2342317020147641755376939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6246178720393711347671837 2342317020147641755376939)
            ·
              refine ⟨3513475530221462633065409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2342317020147641755376939 3513475530221462633065409)
              ·
                refine ⟨2635106647666096974799057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3513475530221462633065409 2635106647666096974799057)
                ·
                  refine ⟨1976329985749572731099293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2635106647666096974799057 1976329985749572731099293)
                  ·
                    refine ⟨741123744656089774162235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1976329985749572731099293 741123744656089774162235)
                    ·
                      rfl

theorem cell22_2165000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 3, 1, 2, 2, 3].length) (baseStart_2165000 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2165000 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2165000 prefixEnd_2165000 := by exact prefixLift 2165000
  have htrace : WordTrace (prefixWord ++ tailWord_2165000) baseStart_2165000 baseEnd_2165000 := by
    simpa [prefixWord, tailWord_2165000, baseEnd_2165000] using wordTrace_append hprefix tailTrace_2165000
  have hstable : (prefixWord ++ tailWord_2165000).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2165000).length < 2 ^ (prefixWord ++ tailWord_2165000).sum := by decide
  have hdescent : baseEnd_2165000 < baseStart_2165000 := by decide
  rcases family_descends (prefixWord ++ tailWord_2165000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2165028 : List Nat := [2, 3, 1, 3, 1, 2, 2, 2, 3, 3]
def baseStart_2165028 : Nat := 118140960795 + 2165028 * 2 ^ 59
def prefixEnd_2165028 : Nat := 4983230072969 + 3 ^ 40 * 2165028 * 2
def baseEnd_2165028 : Nat := 741133329628307034462149

theorem tailTrace_2165028 : CollatzResearch.WordTrace tailWord_2165028 prefixEnd_2165028 741133329628307034462149 := by
  unfold tailWord_2165028
  simp only [CollatzResearch.WordTrace]
  refine ⟨39482529200240394094811869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52643372266987192126415825 39482529200240394094811869)
  ·
    refine ⟨14805948450090147785554451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39482529200240394094811869 14805948450090147785554451)
    ·
      refine ⟨22208922675135221678331677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14805948450090147785554451 22208922675135221678331677)
      ·
        refine ⟨8328346003175708129374379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22208922675135221678331677 8328346003175708129374379)
        ·
          refine ⟨12492519004763562194061569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8328346003175708129374379 12492519004763562194061569)
          ·
            refine ⟨9369389253572671645546177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12492519004763562194061569 9369389253572671645546177)
            ·
              refine ⟨7027041940179503734159633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9369389253572671645546177 7027041940179503734159633)
              ·
                refine ⟨5270281455134627800619725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7027041940179503734159633 5270281455134627800619725)
                ·
                  refine ⟨1976355545675485425232397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5270281455134627800619725 1976355545675485425232397)
                  ·
                    refine ⟨741133329628307034462149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1976355545675485425232397 741133329628307034462149)
                    ·
                      rfl

theorem cell22_2165028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 2, 2, 3, 3].length) (baseStart_2165028 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2165028 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2165028 prefixEnd_2165028 := by exact prefixLift 2165028
  have htrace : WordTrace (prefixWord ++ tailWord_2165028) baseStart_2165028 baseEnd_2165028 := by
    simpa [prefixWord, tailWord_2165028, baseEnd_2165028] using wordTrace_append hprefix tailTrace_2165028
  have hstable : (prefixWord ++ tailWord_2165028).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2165028).length < 2 ^ (prefixWord ++ tailWord_2165028).sum := by decide
  have hdescent : baseEnd_2165028 < baseStart_2165028 := by decide
  rcases family_descends (prefixWord ++ tailWord_2165028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2165039 : List Nat := [1, 1, 2, 1, 2, 1, 4, 2, 1, 7]
def baseStart_2165039 : Nat := 118140960795 + 2165039 * 2 ^ 59
def prefixEnd_2165039 : Nat := 4983230072969 + 3 ^ 40 * 2165039 * 2
def baseEnd_2165039 : Nat := 741137095153106672437115

theorem tailTrace_2165039 : CollatzResearch.WordTrace tailWord_2165039 prefixEnd_2165039 741137095153106672437115 := by
  unfold tailWord_2165039
  simp only [CollatzResearch.WordTrace]
  refine ⟨78965459603440937068274171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52643639735627291378849447 78965459603440937068274171)
  ·
    refine ⟨118448189405161405602411257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78965459603440937068274171 118448189405161405602411257)
    ·
      refine ⟨88836142053871054201808443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 118448189405161405602411257 88836142053871054201808443)
      ·
        refine ⟨133254213080806581302712665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88836142053871054201808443 133254213080806581302712665)
        ·
          refine ⟨99940659810604935977034499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 133254213080806581302712665 99940659810604935977034499)
          ·
            refine ⟨149910989715907403965551749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 99940659810604935977034499 149910989715907403965551749)
            ·
              refine ⟨28108310571732638243540953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 149910989715907403965551749 28108310571732638243540953)
              ·
                refine ⟨21081232928799478682655715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28108310571732638243540953 21081232928799478682655715)
                ·
                  refine ⟨31621849393199218023983573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21081232928799478682655715 31621849393199218023983573)
                  ·
                    refine ⟨741137095153106672437115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 31621849393199218023983573 741137095153106672437115)
                    ·
                      rfl

theorem cell22_2165039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 2, 1, 7].length) (baseStart_2165039 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2165039 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2165039 prefixEnd_2165039 := by exact prefixLift 2165039
  have htrace : WordTrace (prefixWord ++ tailWord_2165039) baseStart_2165039 baseEnd_2165039 := by
    simpa [prefixWord, tailWord_2165039, baseEnd_2165039] using wordTrace_append hprefix tailTrace_2165039
  have hstable : (prefixWord ++ tailWord_2165039).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2165039).length < 2 ^ (prefixWord ++ tailWord_2165039).sum := by decide
  have hdescent : baseEnd_2165039 < baseStart_2165039 := by decide
  rcases family_descends (prefixWord ++ tailWord_2165039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2165088 : List Nat := [2, 1, 1, 3, 5, 1, 1, 1, 3, 4]
def baseStart_2165088 : Nat := 118140960795 + 2165088 * 2 ^ 59
def prefixEnd_2165088 : Nat := 4983230072969 + 3 ^ 40 * 2165088 * 2
def baseEnd_2165088 : Nat := 741153868854486877961965

theorem tailTrace_2165088 : CollatzResearch.WordTrace tailWord_2165088 prefixEnd_2165088 741153868854486877961965 := by
  unfold tailWord_2165088
  simp only [CollatzResearch.WordTrace]
  refine ⟨39483623390131709218403959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52644831186842278957871945 39483623390131709218403959)
  ·
    refine ⟨59225435085197563827605939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39483623390131709218403959 59225435085197563827605939)
    ·
      refine ⟨88838152627796345741408909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59225435085197563827605939 88838152627796345741408909)
      ·
        refine ⟨33314307235423629653028341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 88838152627796345741408909 33314307235423629653028341)
        ·
          refine ⟨3123216303320965279971407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 33314307235423629653028341 3123216303320965279971407)
          ·
            refine ⟨4684824454981447919957111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3123216303320965279971407 4684824454981447919957111)
            ·
              refine ⟨7027236682472171879935667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4684824454981447919957111 7027236682472171879935667)
              ·
                refine ⟨10540855023708257819903501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7027236682472171879935667 10540855023708257819903501)
                ·
                  refine ⟨3952820633890596682463813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10540855023708257819903501 3952820633890596682463813)
                  ·
                    refine ⟨741153868854486877961965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3952820633890596682463813 741153868854486877961965)
                    ·
                      rfl

theorem cell22_2165088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 1, 1, 3, 4].length) (baseStart_2165088 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2165088 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2165088 prefixEnd_2165088 := by exact prefixLift 2165088
  have htrace : WordTrace (prefixWord ++ tailWord_2165088) baseStart_2165088 baseEnd_2165088 := by
    simpa [prefixWord, tailWord_2165088, baseEnd_2165088] using wordTrace_append hprefix tailTrace_2165088
  have hstable : (prefixWord ++ tailWord_2165088).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2165088).length < 2 ^ (prefixWord ++ tailWord_2165088).sum := by decide
  have hdescent : baseEnd_2165088 < baseStart_2165088 := by decide
  rcases family_descends (prefixWord ++ tailWord_2165088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2165116 : List Nat := [2, 2, 2, 1, 1, 1, 2, 3, 4, 4]
def baseStart_2165116 : Nat := 118140960795 + 2165116 * 2 ^ 59
def prefixEnd_2165116 : Nat := 4983230072969 + 3 ^ 40 * 2165116 * 2
def baseEnd_2165116 : Nat := 741163453826704138261879

theorem tailTrace_2165116 : CollatzResearch.WordTrace tailWord_2165116 prefixEnd_2165116 741163453826704138261879 := by
  unfold tailWord_2165116
  simp only [CollatzResearch.WordTrace]
  refine ⟨39484134012080989609413601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52645512016107986145884801 39484134012080989609413601)
  ·
    refine ⟨29613100509060742207060201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39484134012080989609413601 29613100509060742207060201)
    ·
      refine ⟨22209825381795556655295151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29613100509060742207060201 22209825381795556655295151)
      ·
        refine ⟨33314738072693334982942727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22209825381795556655295151 33314738072693334982942727)
        ·
          refine ⟨49972107109040002474414091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33314738072693334982942727 49972107109040002474414091)
          ·
            refine ⟨74958160663560003711621137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49972107109040002474414091 74958160663560003711621137)
            ·
              refine ⟨56218620497670002783715853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 74958160663560003711621137 56218620497670002783715853)
              ·
                refine ⟨21081982686626251043893445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 56218620497670002783715853 21081982686626251043893445)
                ·
                  refine ⟨3952871753742422070730021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21081982686626251043893445 3952871753742422070730021)
                  ·
                    refine ⟨741163453826704138261879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3952871753742422070730021 741163453826704138261879)
                    ·
                      rfl

theorem cell22_2165116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 3, 4, 4].length) (baseStart_2165116 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2165116 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2165116 prefixEnd_2165116 := by exact prefixLift 2165116
  have htrace : WordTrace (prefixWord ++ tailWord_2165116) baseStart_2165116 baseEnd_2165116 := by
    simpa [prefixWord, tailWord_2165116, baseEnd_2165116] using wordTrace_append hprefix tailTrace_2165116
  have hstable : (prefixWord ++ tailWord_2165116).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2165116).length < 2 ^ (prefixWord ++ tailWord_2165116).sum := by decide
  have hdescent : baseEnd_2165116 < baseStart_2165116 := by decide
  rcases family_descends (prefixWord ++ tailWord_2165116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2165131 : List Nat := [1, 1, 1, 1, 4, 4, 3, 7]
def baseStart_2165131 : Nat := 118140960795 + 2165131 * 2 ^ 59
def prefixEnd_2165131 : Nat := 4983230072969 + 3 ^ 40 * 2165131 * 2
def baseEnd_2165131 : Nat := 82352065403694344348537

theorem tailTrace_2165131 : CollatzResearch.WordTrace tailWord_2165131 prefixEnd_2165131 82352065403694344348537 := by
  unfold tailWord_2165131
  simp only [CollatzResearch.WordTrace]
  refine ⟨78968815119107636780623247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52645876746071757853748831 78968815119107636780623247)
  ·
    refine ⟨118453222678661455170934871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78968815119107636780623247 118453222678661455170934871)
    ·
      refine ⟨177679834017992182756402307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118453222678661455170934871 177679834017992182756402307)
      ·
        refine ⟨266519751026988274134603461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 177679834017992182756402307 266519751026988274134603461)
        ·
          refine ⟨49972453317560301400238149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 266519751026988274134603461 49972453317560301400238149)
          ·
            refine ⟨9369834997042556512544653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 49972453317560301400238149 9369834997042556512544653)
            ·
              refine ⟨3513688123890958692204245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9369834997042556512544653 3513688123890958692204245)
              ·
                refine ⟨82352065403694344348537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3513688123890958692204245 82352065403694344348537)
                ·
                  rfl

theorem cell22_2165131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 3, 7].length) (baseStart_2165131 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2165131 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2165131 prefixEnd_2165131 := by exact prefixLift 2165131
  have htrace : WordTrace (prefixWord ++ tailWord_2165131) baseStart_2165131 baseEnd_2165131 := by
    simpa [prefixWord, tailWord_2165131, baseEnd_2165131] using wordTrace_append hprefix tailTrace_2165131
  have hstable : (prefixWord ++ tailWord_2165131).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2165131).length < 2 ^ (prefixWord ++ tailWord_2165131).sum := by decide
  have hdescent : baseEnd_2165131 < baseStart_2165131 := by decide
  rcases family_descends (prefixWord ++ tailWord_2165131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2165150 : List Nat := [4, 3, 1, 2, 1, 2, 1, 1, 1, 6]
def baseStart_2165150 : Nat := 118140960795 + 2165150 * 2 ^ 59
def prefixEnd_2165150 : Nat := 4983230072969 + 3 ^ 40 * 2165150 * 2
def baseEnd_2165150 : Nat := 741175092721539382911775

theorem tailTrace_2165150 : CollatzResearch.WordTrace tailWord_2165150 prefixEnd_2165150 741175092721539382911775 := by
  unfold tailWord_2165150
  simp only [CollatzResearch.WordTrace]
  refine ⟨9871188513254850378195613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 52646338737359202017043269 9871188513254850378195613)
  ·
    refine ⟨3701695692470568891823355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9871188513254850378195613 3701695692470568891823355)
    ·
      refine ⟨5552543538705853337735033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3701695692470568891823355 5552543538705853337735033)
      ·
        refine ⟨4164407654029390003301275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5552543538705853337735033 4164407654029390003301275)
        ·
          refine ⟨6246611481044085004951913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4164407654029390003301275 6246611481044085004951913)
          ·
            refine ⟨4684958610783063753713935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6246611481044085004951913 4684958610783063753713935)
            ·
              refine ⟨7027437916174595630570903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4684958610783063753713935 7027437916174595630570903)
              ·
                refine ⟨10541156874261893445856355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7027437916174595630570903 10541156874261893445856355)
                ·
                  refine ⟨15811735311392840168784533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10541156874261893445856355 15811735311392840168784533)
                  ·
                    refine ⟨741175092721539382911775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15811735311392840168784533 741175092721539382911775)
                    ·
                      rfl

theorem cell22_2165150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 1, 1, 1, 6].length) (baseStart_2165150 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2165150 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2165150 prefixEnd_2165150 := by exact prefixLift 2165150
  have htrace : WordTrace (prefixWord ++ tailWord_2165150) baseStart_2165150 baseEnd_2165150 := by
    simpa [prefixWord, tailWord_2165150, baseEnd_2165150] using wordTrace_append hprefix tailTrace_2165150
  have hstable : (prefixWord ++ tailWord_2165150).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2165150).length < 2 ^ (prefixWord ++ tailWord_2165150).sum := by decide
  have hdescent : baseEnd_2165150 < baseStart_2165150 := by decide
  rcases family_descends (prefixWord ++ tailWord_2165150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2165180 : List Nat := [2, 2, 2, 4, 1, 1, 1, 3, 3, 3]
def baseStart_2165180 : Nat := 118140960795 + 2165180 * 2 ^ 59
def prefixEnd_2165180 : Nat := 4983230072969 + 3 ^ 40 * 2165180 * 2
def baseEnd_2165180 : Nat := 741185362334629304661683

theorem tailTrace_2165180 : CollatzResearch.WordTrace tailWord_2165180 prefixEnd_2165180 741185362334629304661683 := by
  unfold tailWord_2165180
  simp only [CollatzResearch.WordTrace]
  refine ⟨39485301147965059074578497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52647068197286745432771329 39485301147965059074578497)
  ·
    refine ⟨29613975860973794305933873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39485301147965059074578497 29613975860973794305933873)
    ·
      refine ⟨22210481895730345729450405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29613975860973794305933873 22210481895730345729450405)
      ·
        refine ⟨4164465355449439824271951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22210481895730345729450405 4164465355449439824271951)
        ·
          refine ⟨6246698033174159736407927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4164465355449439824271951 6246698033174159736407927)
          ·
            refine ⟨9370047049761239604611891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6246698033174159736407927 9370047049761239604611891)
            ·
              refine ⟨14055070574641859406917837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9370047049761239604611891 14055070574641859406917837)
              ·
                refine ⟨5270651465490697277594189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14055070574641859406917837 5270651465490697277594189)
                ·
                  refine ⟨1976494299559011479097821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5270651465490697277594189 1976494299559011479097821)
                  ·
                    refine ⟨741185362334629304661683, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1976494299559011479097821 741185362334629304661683)
                    ·
                      rfl

theorem cell22_2165180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 1, 3, 3, 3].length) (baseStart_2165180 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2165180 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2165180 prefixEnd_2165180 := by exact prefixLift 2165180
  have htrace : WordTrace (prefixWord ++ tailWord_2165180) baseStart_2165180 baseEnd_2165180 := by
    simpa [prefixWord, tailWord_2165180, baseEnd_2165180] using wordTrace_append hprefix tailTrace_2165180
  have hstable : (prefixWord ++ tailWord_2165180).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2165180).length < 2 ^ (prefixWord ++ tailWord_2165180).sum := by decide
  have hdescent : baseEnd_2165180 < baseStart_2165180 := by decide
  rcases family_descends (prefixWord ++ tailWord_2165180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2165345 : List Nat := [1, 2, 3, 1, 1, 4, 3, 2, 5]
def baseStart_2165345 : Nat := 118140960795 + 2165345 * 2 ^ 59
def prefixEnd_2165345 : Nat := 4983230072969 + 3 ^ 40 * 2165345 * 2
def baseEnd_2165345 : Nat := 247080615068874624762059

theorem tailTrace_2165345 : CollatzResearch.WordTrace tailWord_2165345 prefixEnd_2165345 247080615068874624762059 := by
  unfold tailWord_2165345
  simp only [CollatzResearch.WordTrace]
  refine ⟨78976620340332351328913489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52651080226888234219275659 78976620340332351328913489)
  ·
    refine ⟨59232465255249263496685117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78976620340332351328913489 59232465255249263496685117)
    ·
      refine ⟨22212174470718473811256919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 59232465255249263496685117 22212174470718473811256919)
      ·
        refine ⟨33318261706077710716885379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22212174470718473811256919 33318261706077710716885379)
        ·
          refine ⟨49977392559116566075328069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33318261706077710716885379 49977392559116566075328069)
          ·
            refine ⟨9370761104834356139124013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 49977392559116566075328069 9370761104834356139124013)
            ·
              refine ⟨3514035414312883552171505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9370761104834356139124013 3514035414312883552171505)
              ·
                refine ⟨2635526560734662664128629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3514035414312883552171505 2635526560734662664128629)
                ·
                  refine ⟨247080615068874624762059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2635526560734662664128629 247080615068874624762059)
                  ·
                    rfl

theorem cell22_2165345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 3, 2, 5].length) (baseStart_2165345 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2165345 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2165345 prefixEnd_2165345 := by exact prefixLift 2165345
  have htrace : WordTrace (prefixWord ++ tailWord_2165345) baseStart_2165345 baseEnd_2165345 := by
    simpa [prefixWord, tailWord_2165345, baseEnd_2165345] using wordTrace_append hprefix tailTrace_2165345
  have hstable : (prefixWord ++ tailWord_2165345).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2165345).length < 2 ^ (prefixWord ++ tailWord_2165345).sum := by decide
  have hdescent : baseEnd_2165345 < baseStart_2165345 := by decide
  rcases family_descends (prefixWord ++ tailWord_2165345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2165437 : List Nat := [1, 4, 1, 2, 1, 4, 2, 1, 2, 4]
def baseStart_2165437 : Nat := 118140960795 + 2165437 * 2 ^ 59
def prefixEnd_2165437 : Nat := 4983230072969 + 3 ^ 40 * 2165437 * 2
def baseEnd_2165437 : Nat := 741273338686766300985895

theorem tailTrace_2165437 : CollatzResearch.WordTrace tailWord_2165437 prefixEnd_2165437 741273338686766300985895 := by
  unfold tailWord_2165437
  simp only [CollatzResearch.WordTrace]
  refine ⟨78979975855999051041262565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52653317237332700694175043 78979975855999051041262565)
  ·
    refine ⟨14808745472999822070236731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 78979975855999051041262565 14808745472999822070236731)
    ·
      refine ⟨22213118209499733105355097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14808745472999822070236731 22213118209499733105355097)
      ·
        refine ⟨16659838657124799829016323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22213118209499733105355097 16659838657124799829016323)
        ·
          refine ⟨24989757985687199743524485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16659838657124799829016323 24989757985687199743524485)
          ·
            refine ⟨4685579622316349951910841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24989757985687199743524485 4685579622316349951910841)
            ·
              refine ⟨3514184716737262463933131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4685579622316349951910841 3514184716737262463933131)
              ·
                refine ⟨5271277075105893695899697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3514184716737262463933131 5271277075105893695899697)
                ·
                  refine ⟨3953457806329420271924773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5271277075105893695899697 3953457806329420271924773)
                  ·
                    refine ⟨741273338686766300985895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3953457806329420271924773 741273338686766300985895)
                    ·
                      rfl

theorem cell22_2165437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 2, 1, 2, 4].length) (baseStart_2165437 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2165437 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2165437 prefixEnd_2165437 := by exact prefixLift 2165437
  have htrace : WordTrace (prefixWord ++ tailWord_2165437) baseStart_2165437 baseEnd_2165437 := by
    simpa [prefixWord, tailWord_2165437, baseEnd_2165437] using wordTrace_append hprefix tailTrace_2165437
  have hstable : (prefixWord ++ tailWord_2165437).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2165437).length < 2 ^ (prefixWord ++ tailWord_2165437).sum := by decide
  have hdescent : baseEnd_2165437 < baseStart_2165437 := by decide
  rcases family_descends (prefixWord ++ tailWord_2165437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2165458 : List Nat := [3, 2, 2, 2, 4, 1, 2, 2, 4]
def baseStart_2165458 : Nat := 118140960795 + 2165458 * 2 ^ 59
def prefixEnd_2165458 : Nat := 4983230072969 + 3 ^ 40 * 2165458 * 2
def baseEnd_2165458 : Nat := 247093509138643082070277

theorem tailTrace_2165458 : CollatzResearch.WordTrace tailWord_2165458 prefixEnd_2165458 247093509138643082070277 := by
  unfold tailWord_2165458
  simp only [CollatzResearch.WordTrace]
  refine ⟨19745185447230742906944257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52653827859281981085184685 19745185447230742906944257)
  ·
    refine ⟨14808889085423057180208193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19745185447230742906944257 14808889085423057180208193)
    ·
      refine ⟨11106666814067292885156145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14808889085423057180208193 11106666814067292885156145)
      ·
        refine ⟨8330000110550469663867109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11106666814067292885156145 8330000110550469663867109)
        ·
          refine ⟨1561875020728213061975083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8330000110550469663867109 1561875020728213061975083)
          ·
            refine ⟨2342812531092319592962625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1561875020728213061975083 2342812531092319592962625)
            ·
              refine ⟨1757109398319239694721969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2342812531092319592962625 1757109398319239694721969)
              ·
                refine ⟨1317832048739429771041477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1757109398319239694721969 1317832048739429771041477)
                ·
                  refine ⟨247093509138643082070277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1317832048739429771041477 247093509138643082070277)
                  ·
                    rfl

theorem cell22_2165458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 4, 1, 2, 2, 4].length) (baseStart_2165458 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2165458 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2165458 prefixEnd_2165458 := by exact prefixLift 2165458
  have htrace : WordTrace (prefixWord ++ tailWord_2165458) baseStart_2165458 baseEnd_2165458 := by
    simpa [prefixWord, tailWord_2165458, baseEnd_2165458] using wordTrace_append hprefix tailTrace_2165458
  have hstable : (prefixWord ++ tailWord_2165458).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2165458).length < 2 ^ (prefixWord ++ tailWord_2165458).sum := by decide
  have hdescent : baseEnd_2165458 < baseStart_2165458 := by decide
  rcases family_descends (prefixWord ++ tailWord_2165458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2165544 : List Nat := [2, 1, 5, 1, 1, 1, 4, 2, 1, 4]
def baseStart_2165544 : Nat := 118140960795 + 2165544 * 2 ^ 59
def prefixEnd_2165544 : Nat := 4983230072969 + 3 ^ 40 * 2165544 * 2
def baseEnd_2165544 : Nat := 741309966973453688560567

theorem tailTrace_2165544 : CollatzResearch.WordTrace tailWord_2165544 prefixEnd_2165544 741309966973453688560567 := by
  unfold tailWord_2165544
  simp only [CollatzResearch.WordTrace]
  refine ⟨39491939233305704157703843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52655918977740938876938457 39491939233305704157703843)
  ·
    refine ⟨59237908849958556236555765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39491939233305704157703843 59237908849958556236555765)
    ·
      refine ⟨5553553954683614647177103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 59237908849958556236555765 5553553954683614647177103)
      ·
        refine ⟨8330330932025421970765655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5553553954683614647177103 8330330932025421970765655)
        ·
          refine ⟨12495496398038132956148483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8330330932025421970765655 12495496398038132956148483)
          ·
            refine ⟨18743244597057199434222725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12495496398038132956148483 18743244597057199434222725)
            ·
              refine ⟨3514358361948224893916761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18743244597057199434222725 3514358361948224893916761)
              ·
                refine ⟨2635768771461168670437571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3514358361948224893916761 2635768771461168670437571)
                ·
                  refine ⟨3953653157191753005656357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2635768771461168670437571 3953653157191753005656357)
                  ·
                    refine ⟨741309966973453688560567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3953653157191753005656357 741309966973453688560567)
                    ·
                      rfl

theorem cell22_2165544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 4, 2, 1, 4].length) (baseStart_2165544 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2165544 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2165544 prefixEnd_2165544 := by exact prefixLift 2165544
  have htrace : WordTrace (prefixWord ++ tailWord_2165544) baseStart_2165544 baseEnd_2165544 := by
    simpa [prefixWord, tailWord_2165544, baseEnd_2165544] using wordTrace_append hprefix tailTrace_2165544
  have hstable : (prefixWord ++ tailWord_2165544).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2165544).length < 2 ^ (prefixWord ++ tailWord_2165544).sum := by decide
  have hdescent : baseEnd_2165544 < baseStart_2165544 := by decide
  rcases family_descends (prefixWord ++ tailWord_2165544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2165591 : List Nat := [1, 1, 3, 2, 4, 1, 4, 1, 2, 3]
def baseStart_2165591 : Nat := 118140960795 + 2165591 * 2 ^ 59
def prefixEnd_2165591 : Nat := 4983230072969 + 3 ^ 40 * 2165591 * 2
def baseEnd_2165591 : Nat := 741326056033961232635423

theorem tailTrace_2165591 : CollatzResearch.WordTrace tailWord_2165591 prefixEnd_2165591 741326056033961232635423 := by
  unfold tailWord_2165591
  simp only [CollatzResearch.WordTrace]
  refine ⟨78985592697441135342368627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52657061798294090228245751 78985592697441135342368627)
  ·
    refine ⟨118478389046161703013552941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78985592697441135342368627 118478389046161703013552941)
    ·
      refine ⟨44429395892310638630082353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 118478389046161703013552941 44429395892310638630082353)
      ·
        refine ⟨33322046919232978972561765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44429395892310638630082353 33322046919232978972561765)
        ·
          refine ⟨6247883797356183557355331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 33322046919232978972561765 6247883797356183557355331)
          ·
            refine ⟨9371825696034275336032997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6247883797356183557355331 9371825696034275336032997)
            ·
              refine ⟨1757217318006426625506187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9371825696034275336032997 1757217318006426625506187)
              ·
                refine ⟨2635825977009639938259281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1757217318006426625506187 2635825977009639938259281)
                ·
                  refine ⟨1976869482757229953694461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2635825977009639938259281 1976869482757229953694461)
                  ·
                    refine ⟨741326056033961232635423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1976869482757229953694461 741326056033961232635423)
                    ·
                      rfl

theorem cell22_2165591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 4, 1, 2, 3].length) (baseStart_2165591 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2165591 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2165591 prefixEnd_2165591 := by exact prefixLift 2165591
  have htrace : WordTrace (prefixWord ++ tailWord_2165591) baseStart_2165591 baseEnd_2165591 := by
    simpa [prefixWord, tailWord_2165591, baseEnd_2165591] using wordTrace_append hprefix tailTrace_2165591
  have hstable : (prefixWord ++ tailWord_2165591).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2165591).length < 2 ^ (prefixWord ++ tailWord_2165591).sum := by decide
  have hdescent : baseEnd_2165591 < baseStart_2165591 := by decide
  rcases family_descends (prefixWord ++ tailWord_2165591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2165615 : List Nat := [1, 1, 2, 1, 3, 1, 1, 3, 9]
def baseStart_2165615 : Nat := 118140960795 + 2165615 * 2 ^ 59
def prefixEnd_2165615 : Nat := 4983230072969 + 3 ^ 40 * 2165615 * 2
def baseEnd_2165615 : Nat := 247111423908144390011783

theorem tailTrace_2165615 : CollatzResearch.WordTrace tailWord_2165615 prefixEnd_2165615 247111423908144390011783 := by
  unfold tailWord_2165615
  simp only [CollatzResearch.WordTrace]
  refine ⟨78986468049354187441242299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52657645366236124960828199 78986468049354187441242299)
  ·
    refine ⟨118479702074031281161863449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78986468049354187441242299 118479702074031281161863449)
    ·
      refine ⟨88859776555523460871397587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 118479702074031281161863449 88859776555523460871397587)
      ·
        refine ⟨133289664833285191307096381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88859776555523460871397587 133289664833285191307096381)
        ·
          refine ⟨49983624312481946740161143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 133289664833285191307096381 49983624312481946740161143)
          ·
            refine ⟨74975436468722920110241715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49983624312481946740161143 74975436468722920110241715)
            ·
              refine ⟨112463154703084380165362573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 74975436468722920110241715 112463154703084380165362573)
              ·
                refine ⟨42173683013656642562010965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 112463154703084380165362573 42173683013656642562010965)
                ·
                  refine ⟨247111423908144390011783, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 42173683013656642562010965 247111423908144390011783)
                  ·
                    rfl

theorem cell22_2165615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 3, 9].length) (baseStart_2165615 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2165615 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2165615 prefixEnd_2165615 := by exact prefixLift 2165615
  have htrace : WordTrace (prefixWord ++ tailWord_2165615) baseStart_2165615 baseEnd_2165615 := by
    simpa [prefixWord, tailWord_2165615, baseEnd_2165615] using wordTrace_append hprefix tailTrace_2165615
  have hstable : (prefixWord ++ tailWord_2165615).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2165615).length < 2 ^ (prefixWord ++ tailWord_2165615).sum := by decide
  have hdescent : baseEnd_2165615 < baseStart_2165615 := by decide
  rcases family_descends (prefixWord ++ tailWord_2165615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2165694 : List Nat := [4, 2, 1, 1, 1, 2, 4, 1, 6]
def baseStart_2165694 : Nat := 118140960795 + 2165694 * 2 ^ 59
def prefixEnd_2165694 : Nat := 4983230072969 + 3 ^ 40 * 2165694 * 2
def baseEnd_2165694 : Nat := 247120438346301099103369

theorem tailTrace_2165694 : CollatzResearch.WordTrace tailWord_2165694 prefixEnd_2165694 247120438346301099103369 := by
  unfold tailWord_2165694
  simp only [CollatzResearch.WordTrace]
  refine ⟨9873668677008497991671017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 52659566277378655955578757 9873668677008497991671017)
  ·
    refine ⟨7405251507756373493753263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9873668677008497991671017 7405251507756373493753263)
    ·
      refine ⟨11107877261634560240629895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7405251507756373493753263 11107877261634560240629895)
      ·
        refine ⟨16661815892451840360944843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11107877261634560240629895 16661815892451840360944843)
        ·
          refine ⟨24992723838677760541417265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16661815892451840360944843 24992723838677760541417265)
          ·
            refine ⟨18744542879008320406062949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24992723838677760541417265 18744542879008320406062949)
            ·
              refine ⟨3514601789814060076136803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18744542879008320406062949 3514601789814060076136803)
              ·
                refine ⟨5271902684721090114205205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3514601789814060076136803 5271902684721090114205205)
                ·
                  refine ⟨247120438346301099103369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5271902684721090114205205 247120438346301099103369)
                  ·
                    rfl

theorem cell22_2165694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 4, 1, 6].length) (baseStart_2165694 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2165694 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2165694 prefixEnd_2165694 := by exact prefixLift 2165694
  have htrace : WordTrace (prefixWord ++ tailWord_2165694) baseStart_2165694 baseEnd_2165694 := by
    simpa [prefixWord, tailWord_2165694, baseEnd_2165694] using wordTrace_append hprefix tailTrace_2165694
  have hstable : (prefixWord ++ tailWord_2165694).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2165694).length < 2 ^ (prefixWord ++ tailWord_2165694).sum := by decide
  have hdescent : baseEnd_2165694 < baseStart_2165694 := by decide
  rcases family_descends (prefixWord ++ tailWord_2165694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2165707 : List Nat := [1, 1, 1, 1, 3, 5, 1, 2, 1, 6]
def baseStart_2165707 : Nat := 118140960795 + 2165707 * 2 ^ 59
def prefixEnd_2165707 : Nat := 4983230072969 + 3 ^ 40 * 2165707 * 2
def baseEnd_2165707 : Nat := 741365765204575596735067

theorem tailTrace_2165707 : CollatzResearch.WordTrace tailWord_2165707 prefixEnd_2165707 741365765204575596735067 := by
  unfold tailWord_2165707
  simp only [CollatzResearch.WordTrace]
  refine ⟨78989823565020887153591375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52659882376680591435727583 78989823565020887153591375)
  ·
    refine ⟨118484735347531330730387063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78989823565020887153591375 118484735347531330730387063)
    ·
      refine ⟨177727103021296996095580595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118484735347531330730387063 177727103021296996095580595)
      ·
        refine ⟨266590654531945494143370893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 177727103021296996095580595 266590654531945494143370893)
        ·
          refine ⟨99971495449479560303764085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 266590654531945494143370893 99971495449479560303764085)
          ·
            refine ⟨9372327698388708778477883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 99971495449479560303764085 9372327698388708778477883)
            ·
              refine ⟨14058491547583063167716825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9372327698388708778477883 14058491547583063167716825)
              ·
                refine ⟨10543868660687297375787619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14058491547583063167716825 10543868660687297375787619)
                ·
                  refine ⟨15815802991030946063681429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10543868660687297375787619 15815802991030946063681429)
                  ·
                    refine ⟨741365765204575596735067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15815802991030946063681429 741365765204575596735067)
                    ·
                      rfl

theorem cell22_2165707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 1, 2, 1, 6].length) (baseStart_2165707 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2165707 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2165707 prefixEnd_2165707 := by exact prefixLift 2165707
  have htrace : WordTrace (prefixWord ++ tailWord_2165707) baseStart_2165707 baseEnd_2165707 := by
    simpa [prefixWord, tailWord_2165707, baseEnd_2165707] using wordTrace_append hprefix tailTrace_2165707
  have hstable : (prefixWord ++ tailWord_2165707).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2165707).length < 2 ^ (prefixWord ++ tailWord_2165707).sum := by decide
  have hdescent : baseEnd_2165707 < baseStart_2165707 := by decide
  rcases family_descends (prefixWord ++ tailWord_2165707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2165752 : List Nat := [2, 1, 2, 1, 1, 3, 1, 3, 2, 6]
def baseStart_2165752 : Nat := 118140960795 + 2165752 * 2 ^ 59
def prefixEnd_2165752 : Nat := 4983230072969 + 3 ^ 40 * 2165752 * 2
def baseEnd_2165752 : Nat := 741381169624210479359929

theorem tailTrace_2165752 : CollatzResearch.WordTrace tailWord_2165752 prefixEnd_2165752 741381169624210479359929 := by
  unfold tailWord_2165752
  simp only [CollatzResearch.WordTrace]
  refine ⟨39495732424928929919489755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52660976566571906559319673 39495732424928929919489755)
  ·
    refine ⟨59243598637393394879234633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39495732424928929919489755 59243598637393394879234633)
    ·
      refine ⟨44432698978045046159425975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59243598637393394879234633 44432698978045046159425975)
      ·
        refine ⟨66649048467067569239138963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44432698978045046159425975 66649048467067569239138963)
        ·
          refine ⟨99973572700601353858708445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66649048467067569239138963 99973572700601353858708445)
          ·
            refine ⟨37490089762725507697015667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 99973572700601353858708445 37490089762725507697015667)
            ·
              refine ⟨56235134644088261545523501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37490089762725507697015667 56235134644088261545523501)
              ·
                refine ⟨21088175491533098079571313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 56235134644088261545523501 21088175491533098079571313)
                ·
                  refine ⟨15816131618649823559678485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21088175491533098079571313 15816131618649823559678485)
                  ·
                    refine ⟨741381169624210479359929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15816131618649823559678485 741381169624210479359929)
                    ·
                      rfl

theorem cell22_2165752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 3, 2, 6].length) (baseStart_2165752 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2165752 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2165752 prefixEnd_2165752 := by exact prefixLift 2165752
  have htrace : WordTrace (prefixWord ++ tailWord_2165752) baseStart_2165752 baseEnd_2165752 := by
    simpa [prefixWord, tailWord_2165752, baseEnd_2165752] using wordTrace_append hprefix tailTrace_2165752
  have hstable : (prefixWord ++ tailWord_2165752).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2165752).length < 2 ^ (prefixWord ++ tailWord_2165752).sum := by decide
  have hdescent : baseEnd_2165752 < baseStart_2165752 := by decide
  rcases family_descends (prefixWord ++ tailWord_2165752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2165859 : List Nat := [1, 1, 1, 5, 1, 1, 1, 3, 4, 4]
def baseStart_2165859 : Nat := 118140960795 + 2165859 * 2 ^ 59
def prefixEnd_2165859 : Nat := 4983230072969 + 3 ^ 40 * 2165859 * 2
def baseEnd_2165859 : Nat := 741417797910897866934601

theorem tailTrace_2165859 : CollatzResearch.WordTrace tailWord_2165859 prefixEnd_2165859 741417797910897866934601 := by
  unfold tailWord_2165859
  simp only [CollatzResearch.WordTrace]
  refine ⟨78995367460470217113124631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52663578306980144742083087 78995367460470217113124631)
  ·
    refine ⟨118493051190705325669686947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78995367460470217113124631 118493051190705325669686947)
    ·
      refine ⟨177739576786057988504530421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118493051190705325669686947 177739576786057988504530421)
      ·
        refine ⟨16663085323692936422299727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 177739576786057988504530421 16663085323692936422299727)
        ·
          refine ⟨24994627985539404633449591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16663085323692936422299727 24994627985539404633449591)
          ·
            refine ⟨37491941978309106950174387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24994627985539404633449591 37491941978309106950174387)
            ·
              refine ⟨56237912967463660425261581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37491941978309106950174387 56237912967463660425261581)
              ·
                refine ⟨21089217362798872659473093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 56237912967463660425261581 21089217362798872659473093)
                ·
                  refine ⟨3954228255524788623651205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21089217362798872659473093 3954228255524788623651205)
                  ·
                    refine ⟨741417797910897866934601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3954228255524788623651205 741417797910897866934601)
                    ·
                      rfl

theorem cell22_2165859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 3, 4, 4].length) (baseStart_2165859 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2165859 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2165859 prefixEnd_2165859 := by exact prefixLift 2165859
  have htrace : WordTrace (prefixWord ++ tailWord_2165859) baseStart_2165859 baseEnd_2165859 := by
    simpa [prefixWord, tailWord_2165859, baseEnd_2165859] using wordTrace_append hprefix tailTrace_2165859
  have hstable : (prefixWord ++ tailWord_2165859).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2165859).length < 2 ^ (prefixWord ++ tailWord_2165859).sum := by decide
  have hdescent : baseEnd_2165859 < baseStart_2165859 := by decide
  rcases family_descends (prefixWord ++ tailWord_2165859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2165861 : List Nat := [1, 3, 1, 3, 2, 1, 3, 1, 4, 3]
def baseStart_2165861 : Nat := 118140960795 + 2165861 * 2 ^ 59
def prefixEnd_2165861 : Nat := 4983230072969 + 3 ^ 40 * 2165861 * 2
def baseEnd_2165861 : Nat := 741418482551770528384595

theorem tailTrace_2165861 : CollatzResearch.WordTrace tailWord_2165861 prefixEnd_2165861 741418482551770528384595 := by
  unfold tailWord_2165861
  simp only [CollatzResearch.WordTrace]
  refine ⟨78995440406462971454697437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52663626937641980969798291 78995440406462971454697437)
  ·
    refine ⟨29623290152423614295511539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 78995440406462971454697437 29623290152423614295511539)
    ·
      refine ⟨44434935228635421443267309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29623290152423614295511539 44434935228635421443267309)
      ·
        refine ⟨16663100710738283041225241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44434935228635421443267309 16663100710738283041225241)
        ·
          refine ⟨12497325533053712280918931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16663100710738283041225241 12497325533053712280918931)
          ·
            refine ⟨18745988299580568421378397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12497325533053712280918931 18745988299580568421378397)
            ·
              refine ⟨7029745612342713158016899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18745988299580568421378397 7029745612342713158016899)
              ·
                refine ⟨10544618418514069737025349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7029745612342713158016899 10544618418514069737025349)
                ·
                  refine ⟨1977115953471388075692253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10544618418514069737025349 1977115953471388075692253)
                  ·
                    refine ⟨741418482551770528384595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1977115953471388075692253 741418482551770528384595)
                    ·
                      rfl

theorem cell22_2165861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 3, 1, 4, 3].length) (baseStart_2165861 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2165861 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2165861 prefixEnd_2165861 := by exact prefixLift 2165861
  have htrace : WordTrace (prefixWord ++ tailWord_2165861) baseStart_2165861 baseEnd_2165861 := by
    simpa [prefixWord, tailWord_2165861, baseEnd_2165861] using wordTrace_append hprefix tailTrace_2165861
  have hstable : (prefixWord ++ tailWord_2165861).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2165861).length < 2 ^ (prefixWord ++ tailWord_2165861).sum := by decide
  have hdescent : baseEnd_2165861 < baseStart_2165861 := by decide
  rcases family_descends (prefixWord ++ tailWord_2165861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2165874 : List Nat := [3, 2, 1, 2, 2, 1, 2, 9]
def baseStart_2165874 : Nat := 118140960795 + 2165874 * 2 ^ 59
def prefixEnd_2165874 : Nat := 4983230072969 + 3 ^ 40 * 2165874 * 2
def baseEnd_2165874 : Nat := 82380325857493647534395

theorem tailTrace_2165874 : CollatzResearch.WordTrace tailWord_2165874 prefixEnd_2165874 82380325857493647534395 := by
  unfold tailWord_2165874
  simp only [CollatzResearch.WordTrace]
  refine ⟨19748978638853968668730169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52663943036943916449947117 19748978638853968668730169)
  ·
    refine ⟨14811733979140476501547627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19748978638853968668730169 14811733979140476501547627)
    ·
      refine ⟨22217600968710714752321441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14811733979140476501547627 22217600968710714752321441)
      ·
        refine ⟨16663200726533036064241081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22217600968710714752321441 16663200726533036064241081)
        ·
          refine ⟨12497400544899777048180811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16663200726533036064241081 12497400544899777048180811)
          ·
            refine ⟨18746100817349665572271217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12497400544899777048180811 18746100817349665572271217)
            ·
              refine ⟨14059575613012249179203413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18746100817349665572271217 14059575613012249179203413)
              ·
                refine ⟨82380325857493647534395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 14059575613012249179203413 82380325857493647534395)
                ·
                  rfl

theorem cell22_2165874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 2, 9].length) (baseStart_2165874 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2165874 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2165874 prefixEnd_2165874 := by exact prefixLift 2165874
  have htrace : WordTrace (prefixWord ++ tailWord_2165874) baseStart_2165874 baseEnd_2165874 := by
    simpa [prefixWord, tailWord_2165874, baseEnd_2165874] using wordTrace_append hprefix tailTrace_2165874
  have hstable : (prefixWord ++ tailWord_2165874).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2165874).length < 2 ^ (prefixWord ++ tailWord_2165874).sum := by decide
  have hdescent : baseEnd_2165874 < baseStart_2165874 := by decide
  rcases family_descends (prefixWord ++ tailWord_2165874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2165923 : List Nat := [1, 1, 1, 4, 1, 1, 1, 8, 1, 3]
def baseStart_2165923 : Nat := 118140960795 + 2165923 * 2 ^ 59
def prefixEnd_2165923 : Nat := 4983230072969 + 3 ^ 40 * 2165923 * 2
def baseEnd_2165923 : Nat := 741439706418823033334405

theorem tailTrace_2165923 : CollatzResearch.WordTrace tailWord_2165923 prefixEnd_2165923 741439706418823033334405 := by
  unfold tailWord_2165923
  simp only [CollatzResearch.WordTrace]
  refine ⟨78997701732238356043454423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52665134488158904028969615 78997701732238356043454423)
  ·
    refine ⟨118496552598357534065181635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78997701732238356043454423 118496552598357534065181635)
    ·
      refine ⟨177744828897536301097772453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118496552598357534065181635 177744828897536301097772453)
      ·
        refine ⟨33327155418288056455832335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 177744828897536301097772453 33327155418288056455832335)
        ·
          refine ⟨49990733127432084683748503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33327155418288056455832335 49990733127432084683748503)
          ·
            refine ⟨74986099691148127025622755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49990733127432084683748503 74986099691148127025622755)
            ·
              refine ⟨112479149536722190538434133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 74986099691148127025622755 112479149536722190538434133)
              ·
                refine ⟨1318115033633463170372275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 112479149536722190538434133 1318115033633463170372275)
                ·
                  refine ⟨1977172550450194755558413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1318115033633463170372275 1977172550450194755558413)
                  ·
                    refine ⟨741439706418823033334405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1977172550450194755558413 741439706418823033334405)
                    ·
                      rfl

theorem cell22_2165923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 8, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 8, 1, 3].length) (baseStart_2165923 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2165923 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2165923 prefixEnd_2165923 := by exact prefixLift 2165923
  have htrace : WordTrace (prefixWord ++ tailWord_2165923) baseStart_2165923 baseEnd_2165923 := by
    simpa [prefixWord, tailWord_2165923, baseEnd_2165923] using wordTrace_append hprefix tailTrace_2165923
  have hstable : (prefixWord ++ tailWord_2165923).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2165923).length < 2 ^ (prefixWord ++ tailWord_2165923).sum := by decide
  have hdescent : baseEnd_2165923 < baseStart_2165923 := by decide
  rcases family_descends (prefixWord ++ tailWord_2165923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2165974 : List Nat := [5, 2, 1, 2, 2, 1, 1, 4, 1, 3]
def baseStart_2165974 : Nat := 118140960795 + 2165974 * 2 ^ 59
def prefixEnd_2165974 : Nat := 4983230072969 + 3 ^ 40 * 2165974 * 2
def baseEnd_2165974 : Nat := 741457164761075900309249

theorem tailTrace_2165974 : CollatzResearch.WordTrace tailWord_2165974 prefixEnd_2165974 741457164761075900309249 := by
  unfold tailWord_2165974
  simp only [CollatzResearch.WordTrace]
  refine ⟨4937472615940849484597561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 52666374570035727835707317 4937472615940849484597561)
  ·
    refine ⟨3703104461955637113448171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4937472615940849484597561 3703104461955637113448171)
    ·
      refine ⟨5554656692933455670172257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3703104461955637113448171 5554656692933455670172257)
      ·
        refine ⟨4165992519700091752629193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5554656692933455670172257 4165992519700091752629193)
        ·
          refine ⟨3124494389775068814471895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4165992519700091752629193 3124494389775068814471895)
          ·
            refine ⟨4686741584662603221707843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3124494389775068814471895 4686741584662603221707843)
            ·
              refine ⟨7030112376993904832561765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4686741584662603221707843 7030112376993904832561765)
              ·
                refine ⟨1318146070686357156105331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7030112376993904832561765 1318146070686357156105331)
                ·
                  refine ⟨1977219106029535734157997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1318146070686357156105331 1977219106029535734157997)
                  ·
                    refine ⟨741457164761075900309249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1977219106029535734157997 741457164761075900309249)
                    ·
                      rfl

theorem cell22_2165974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 1, 4, 1, 3].length) (baseStart_2165974 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2165974 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2165974 prefixEnd_2165974 := by exact prefixLift 2165974
  have htrace : WordTrace (prefixWord ++ tailWord_2165974) baseStart_2165974 baseEnd_2165974 := by
    simpa [prefixWord, tailWord_2165974, baseEnd_2165974] using wordTrace_append hprefix tailTrace_2165974
  have hstable : (prefixWord ++ tailWord_2165974).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2165974).length < 2 ^ (prefixWord ++ tailWord_2165974).sum := by decide
  have hdescent : baseEnd_2165974 < baseStart_2165974 := by decide
  rcases family_descends (prefixWord ++ tailWord_2165974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2165996 : List Nat := [2, 2, 1, 1, 2, 4, 1, 3, 1, 5]
def baseStart_2165996 : Nat := 118140960795 + 2165996 * 2 ^ 59
def prefixEnd_2165996 : Nat := 4983230072969 + 3 ^ 40 * 2165996 * 2
def baseEnd_2165996 : Nat := 741464695810675176259181

theorem tailTrace_2165996 : CollatzResearch.WordTrace tailWord_2165996 prefixEnd_2165996 741464695810675176259181 := by
  unfold tailWord_2165996
  simp only [CollatzResearch.WordTrace]
  refine ⟨39500182130486944755430921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52666909507315926340574561 39500182130486944755430921)
  ·
    refine ⟨29625136597865208566573191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39500182130486944755430921 29625136597865208566573191)
    ·
      refine ⟨44437704896797812849859787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29625136597865208566573191 44437704896797812849859787)
      ·
        refine ⟨66656557345196719274789681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44437704896797812849859787 66656557345196719274789681)
        ·
          refine ⟨49992418008897539456092261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66656557345196719274789681 49992418008897539456092261)
          ·
            refine ⟨9373578376668288648017299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 49992418008897539456092261 9373578376668288648017299)
            ·
              refine ⟨14060367565002432972025949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9373578376668288648017299 14060367565002432972025949)
              ·
                refine ⟨5272637836875912364509731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14060367565002432972025949 5272637836875912364509731)
                ·
                  refine ⟨7908956755313868546764597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5272637836875912364509731 7908956755313868546764597)
                  ·
                    refine ⟨741464695810675176259181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7908956755313868546764597 741464695810675176259181)
                    ·
                      rfl

theorem cell22_2165996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 5].length) (baseStart_2165996 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2165996 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2165996 prefixEnd_2165996 := by exact prefixLift 2165996
  have htrace : WordTrace (prefixWord ++ tailWord_2165996) baseStart_2165996 baseEnd_2165996 := by
    simpa [prefixWord, tailWord_2165996, baseEnd_2165996] using wordTrace_append hprefix tailTrace_2165996
  have hstable : (prefixWord ++ tailWord_2165996).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2165996).length < 2 ^ (prefixWord ++ tailWord_2165996).sum := by decide
  have hdescent : baseEnd_2165996 < baseStart_2165996 := by decide
  rcases family_descends (prefixWord ++ tailWord_2165996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2166030 : List Nat := [4, 1, 1, 2, 1, 3, 3, 2, 2, 3]
def baseStart_2166030 : Nat := 118140960795 + 2166030 * 2 ^ 59
def prefixEnd_2166030 : Nat := 4983230072969 + 3 ^ 40 * 2166030 * 2
def baseEnd_2166030 : Nat := 741476334705510420909077

theorem tailTrace_2166030 : CollatzResearch.WordTrace tailWord_2166030 prefixEnd_2166030 741476334705510420909077 := by
  unfold tailWord_2166030
  simp only [CollatzResearch.WordTrace]
  refine ⟨9875200542856339164699943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 52667736228567142211733029 9875200542856339164699943)
  ·
    refine ⟨14812800814284508747049915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9875200542856339164699943 14812800814284508747049915)
    ·
      refine ⟨22219201221426763120574873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14812800814284508747049915 22219201221426763120574873)
      ·
        refine ⟨16664400916070072340431155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22219201221426763120574873 16664400916070072340431155)
        ·
          refine ⟨24996601374105108510646733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16664400916070072340431155 24996601374105108510646733)
          ·
            refine ⟨9373725515289415691492525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24996601374105108510646733 9373725515289415691492525)
            ·
              refine ⟨3515147068233530884309697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9373725515289415691492525 3515147068233530884309697)
              ·
                refine ⟨2636360301175148163232273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3515147068233530884309697 2636360301175148163232273)
                ·
                  refine ⟨1977270225881361122424205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2636360301175148163232273 1977270225881361122424205)
                  ·
                    refine ⟨741476334705510420909077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1977270225881361122424205 741476334705510420909077)
                    ·
                      rfl

theorem cell22_2166030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 3, 2, 2, 3].length) (baseStart_2166030 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2166030 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2166030 prefixEnd_2166030 := by exact prefixLift 2166030
  have htrace : WordTrace (prefixWord ++ tailWord_2166030) baseStart_2166030 baseEnd_2166030 := by
    simpa [prefixWord, tailWord_2166030, baseEnd_2166030] using wordTrace_append hprefix tailTrace_2166030
  have hstable : (prefixWord ++ tailWord_2166030).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2166030).length < 2 ^ (prefixWord ++ tailWord_2166030).sum := by decide
  have hdescent : baseEnd_2166030 < baseStart_2166030 := by decide
  rcases family_descends (prefixWord ++ tailWord_2166030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2166047 : List Nat := [1, 1, 2, 4, 4, 1, 3, 1, 2, 3]
def baseStart_2166047 : Nat := 118140960795 + 2166047 * 2 ^ 59
def prefixEnd_2166047 : Nat := 4983230072969 + 3 ^ 40 * 2166047 * 2
def baseEnd_2166047 : Nat := 741482154152928043234025

theorem tailTrace_2166047 : CollatzResearch.WordTrace tailWord_2166047 prefixEnd_2166047 741482154152928043234025 := by
  unfold tailWord_2166047
  simp only [CollatzResearch.WordTrace]
  refine ⟨79002224383789125220968395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52668149589192750147312263 79002224383789125220968395)
  ·
    refine ⟨118503336575683687831452593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79002224383789125220968395 118503336575683687831452593)
    ·
      refine ⟨88877502431762765873589445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 118503336575683687831452593 88877502431762765873589445)
      ·
        refine ⟨16664531705955518601298021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 88877502431762765873589445 16664531705955518601298021)
        ·
          refine ⟨3124599694866659737743379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16664531705955518601298021 3124599694866659737743379)
          ·
            refine ⟨4686899542299989606615069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3124599694866659737743379 4686899542299989606615069)
            ·
              refine ⟨1757587328362496102480651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4686899542299989606615069 1757587328362496102480651)
              ·
                refine ⟨2636380992543744153720977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1757587328362496102480651 2636380992543744153720977)
                ·
                  refine ⟨1977285744407808115290733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2636380992543744153720977 1977285744407808115290733)
                  ·
                    refine ⟨741482154152928043234025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1977285744407808115290733 741482154152928043234025)
                    ·
                      rfl

theorem cell22_2166047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 3, 1, 2, 3].length) (baseStart_2166047 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2166047 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2166047 prefixEnd_2166047 := by exact prefixLift 2166047
  have htrace : WordTrace (prefixWord ++ tailWord_2166047) baseStart_2166047 baseEnd_2166047 := by
    simpa [prefixWord, tailWord_2166047, baseEnd_2166047] using wordTrace_append hprefix tailTrace_2166047
  have hstable : (prefixWord ++ tailWord_2166047).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2166047).length < 2 ^ (prefixWord ++ tailWord_2166047).sum := by decide
  have hdescent : baseEnd_2166047 < baseStart_2166047 := by decide
  rcases family_descends (prefixWord ++ tailWord_2166047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2166135 : List Nat := [1, 1, 3, 1, 1, 2, 7, 1, 1, 4]
def baseStart_2166135 : Nat := 118140960795 + 2166135 * 2 ^ 59
def prefixEnd_2166135 : Nat := 4983230072969 + 3 ^ 40 * 2166135 * 2
def baseEnd_2166135 : Nat := 741512278351325147033755

theorem tailTrace_2166135 : CollatzResearch.WordTrace tailWord_2166135 prefixEnd_2166135 741512278351325147033755 := by
  unfold tailWord_2166135
  simp only [CollatzResearch.WordTrace]
  refine ⟨79005434007470316250171859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52670289338313544166781239 79005434007470316250171859)
  ·
    refine ⟨118508151011205474375257789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79005434007470316250171859 118508151011205474375257789)
    ·
      refine ⟨44440556629202052890721671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 118508151011205474375257789 44440556629202052890721671)
      ·
        refine ⟨66660834943803079336082507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44440556629202052890721671 66660834943803079336082507)
        ·
          refine ⟨99991252415704619004123761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66660834943803079336082507 99991252415704619004123761)
          ·
            refine ⟨74993439311778464253092821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 99991252415704619004123761 74993439311778464253092821)
            ·
              refine ⟨1757658733869807755931863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 74993439311778464253092821 1757658733869807755931863)
              ·
                refine ⟨2636488100804711633897795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1757658733869807755931863 2636488100804711633897795)
                ·
                  refine ⟨3954732151207067450846693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2636488100804711633897795 3954732151207067450846693)
                  ·
                    refine ⟨741512278351325147033755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3954732151207067450846693 741512278351325147033755)
                    ·
                      rfl

theorem cell22_2166135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 7, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 7, 1, 1, 4].length) (baseStart_2166135 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2166135 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2166135 prefixEnd_2166135 := by exact prefixLift 2166135
  have htrace : WordTrace (prefixWord ++ tailWord_2166135) baseStart_2166135 baseEnd_2166135 := by
    simpa [prefixWord, tailWord_2166135, baseEnd_2166135] using wordTrace_append hprefix tailTrace_2166135
  have hstable : (prefixWord ++ tailWord_2166135).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2166135).length < 2 ^ (prefixWord ++ tailWord_2166135).sum := by decide
  have hdescent : baseEnd_2166135 < baseStart_2166135 := by decide
  rcases family_descends (prefixWord ++ tailWord_2166135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2166165 : List Nat := [1, 3, 2, 1, 1, 2, 4, 3, 2, 3]
def baseStart_2166165 : Nat := 118140960795 + 2166165 * 2 ^ 59
def prefixEnd_2166165 : Nat := 4983230072969 + 3 ^ 40 * 2166165 * 2
def baseEnd_2166165 : Nat := 741522547964415068783663

theorem tailTrace_2166165 : CollatzResearch.WordTrace tailWord_2166165 prefixEnd_2166165 741522547964415068783663 := by
  unfold tailWord_2166165
  simp only [CollatzResearch.WordTrace]
  refine ⟨79006528197361631373763949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52671018798241087582509299 79006528197361631373763949)
  ·
    refine ⟨29627448074010611765161481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 79006528197361631373763949 29627448074010611765161481)
    ·
      refine ⟨22220586055507958823871111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29627448074010611765161481 22220586055507958823871111)
      ·
        refine ⟨33330879083261938235806667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22220586055507958823871111 33330879083261938235806667)
        ·
          refine ⟨49996318624892907353710001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33330879083261938235806667 49996318624892907353710001)
          ·
            refine ⟨37497238968669680515282501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49996318624892907353710001 37497238968669680515282501)
            ·
              refine ⟨7030732306625565096615469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 37497238968669680515282501 7030732306625565096615469)
              ·
                refine ⟨2636524614984586911230801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7030732306625565096615469 2636524614984586911230801)
                ·
                  refine ⟨1977393461238440183423101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2636524614984586911230801 1977393461238440183423101)
                  ·
                    refine ⟨741522547964415068783663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1977393461238440183423101 741522547964415068783663)
                    ·
                      rfl

theorem cell22_2166165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 4, 3, 2, 3].length) (baseStart_2166165 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2166165 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2166165 prefixEnd_2166165 := by exact prefixLift 2166165
  have htrace : WordTrace (prefixWord ++ tailWord_2166165) baseStart_2166165 baseEnd_2166165 := by
    simpa [prefixWord, tailWord_2166165, baseEnd_2166165] using wordTrace_append hprefix tailTrace_2166165
  have hstable : (prefixWord ++ tailWord_2166165).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2166165).length < 2 ^ (prefixWord ++ tailWord_2166165).sum := by decide
  have hdescent : baseEnd_2166165 < baseStart_2166165 := by decide
  rcases family_descends (prefixWord ++ tailWord_2166165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2166184 : List Nat := [2, 1, 6, 1, 2, 1, 2, 3, 4]
def baseStart_2166184 : Nat := 118140960795 + 2166184 * 2 ^ 59
def prefixEnd_2166184 : Nat := 4983230072969 + 3 ^ 40 * 2166184 * 2
def baseEnd_2166184 : Nat := 247176350684235117519535

theorem tailTrace_2166184 : CollatzResearch.WordTrace tailWord_2166184 prefixEnd_2166184 247176350684235117519535 := by
  unfold tailWord_2166184
  simp only [CollatzResearch.WordTrace]
  refine ⟨39503610592146398809352803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52671480789528531745803737 39503610592146398809352803)
  ·
    refine ⟨59255415888219598214029205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39503610592146398809352803 59255415888219598214029205)
    ·
      refine ⟨2777597619760293666282619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 59255415888219598214029205 2777597619760293666282619)
      ·
        refine ⟨4166396429640440499423929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2777597619760293666282619 4166396429640440499423929)
        ·
          refine ⟨3124797322230330374567947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4166396429640440499423929 3124797322230330374567947)
          ·
            refine ⟨4687195983345495561851921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3124797322230330374567947 4687195983345495561851921)
            ·
              refine ⟨3515396987509121671388941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4687195983345495561851921 3515396987509121671388941)
              ·
                refine ⟨1318273870315920626770853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3515396987509121671388941 1318273870315920626770853)
                ·
                  refine ⟨247176350684235117519535, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1318273870315920626770853 247176350684235117519535)
                  ·
                    rfl

theorem cell22_2166184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 2, 3, 4].length) (baseStart_2166184 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2166184 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2166184 prefixEnd_2166184 := by exact prefixLift 2166184
  have htrace : WordTrace (prefixWord ++ tailWord_2166184) baseStart_2166184 baseEnd_2166184 := by
    simpa [prefixWord, tailWord_2166184, baseEnd_2166184] using wordTrace_append hprefix tailTrace_2166184
  have hstable : (prefixWord ++ tailWord_2166184).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2166184).length < 2 ^ (prefixWord ++ tailWord_2166184).sum := by decide
  have hdescent : baseEnd_2166184 < baseStart_2166184 := by decide
  rcases family_descends (prefixWord ++ tailWord_2166184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2166223 : List Nat := [1, 1, 2, 1, 1, 4, 2, 5, 5]
def baseStart_2166223 : Nat := 118140960795 + 2166223 * 2 ^ 59
def prefixEnd_2166223 : Nat := 4983230072969 + 3 ^ 40 * 2166223 * 2
def baseEnd_2166223 : Nat := 247180800849907416944495

theorem tailTrace_2166223 : CollatzResearch.WordTrace tailWord_2166223 prefixEnd_2166223 247180800849907416944495 := by
  unfold tailWord_2166223
  simp only [CollatzResearch.WordTrace]
  refine ⟨79008643631151507279375323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52672429087434338186250215 79008643631151507279375323)
  ·
    refine ⟨118512965446727260919062985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79008643631151507279375323 118512965446727260919062985)
    ·
      refine ⟨88884724085045445689297239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 118512965446727260919062985 88884724085045445689297239)
      ·
        refine ⟨133327086127568168533945859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88884724085045445689297239 133327086127568168533945859)
        ·
          refine ⟨199990629191352252800918789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 133327086127568168533945859 199990629191352252800918789)
          ·
            refine ⟨37498242973378547400172273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 199990629191352252800918789 37498242973378547400172273)
            ·
              refine ⟨28123682230033910550129205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37498242973378547400172273 28123682230033910550129205)
              ·
                refine ⟨2636595209065679114074613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 28123682230033910550129205 2636595209065679114074613)
                ·
                  refine ⟨247180800849907416944495, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2636595209065679114074613 247180800849907416944495)
                  ·
                    rfl

theorem cell22_2166223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 5, 5].length) (baseStart_2166223 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2166223 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2166223 prefixEnd_2166223 := by exact prefixLift 2166223
  have htrace : WordTrace (prefixWord ++ tailWord_2166223) baseStart_2166223 baseEnd_2166223 := by
    simpa [prefixWord, tailWord_2166223, baseEnd_2166223] using wordTrace_append hprefix tailTrace_2166223
  have hstable : (prefixWord ++ tailWord_2166223).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2166223).length < 2 ^ (prefixWord ++ tailWord_2166223).sum := by decide
  have hdescent : baseEnd_2166223 < baseStart_2166223 := by decide
  rcases family_descends (prefixWord ++ tailWord_2166223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2166274 : List Nat := [3, 4, 1, 2, 1, 1, 4, 1, 5]
def baseStart_2166274 : Nat := 118140960795 + 2166274 * 2 ^ 59
def prefixEnd_2166274 : Nat := 4983230072969 + 3 ^ 40 * 2166274 * 2
def baseEnd_2166274 : Nat := 247186620297325039269443

theorem tailTrace_2166274 : CollatzResearch.WordTrace tailWord_2166274 prefixEnd_2166274 247186620297325039269443 := by
  unfold tailWord_2166274
  simp only [CollatzResearch.WordTrace]
  refine ⟨19752625938491685747370469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52673669169311161992987917 19752625938491685747370469)
  ·
    refine ⟨3703617363467191077631963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19752625938491685747370469 3703617363467191077631963)
    ·
      refine ⟨5555426045200786616447945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3703617363467191077631963 5555426045200786616447945)
      ·
        refine ⟨4166569533900589962335959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5555426045200786616447945 4166569533900589962335959)
        ·
          refine ⟨6249854300850884943503939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4166569533900589962335959 6249854300850884943503939)
          ·
            refine ⟨9374781451276327415255909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6249854300850884943503939 9374781451276327415255909)
            ·
              refine ⟨1757771522114311390360483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9374781451276327415255909 1757771522114311390360483)
              ·
                refine ⟨2636657283171467085540725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1757771522114311390360483 2636657283171467085540725)
                ·
                  refine ⟨247186620297325039269443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2636657283171467085540725 247186620297325039269443)
                  ·
                    rfl

theorem cell22_2166274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 4, 1, 5].length) (baseStart_2166274 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2166274 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2166274 prefixEnd_2166274 := by exact prefixLift 2166274
  have htrace : WordTrace (prefixWord ++ tailWord_2166274) baseStart_2166274 baseEnd_2166274 := by
    simpa [prefixWord, tailWord_2166274, baseEnd_2166274] using wordTrace_append hprefix tailTrace_2166274
  have hstable : (prefixWord ++ tailWord_2166274).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2166274).length < 2 ^ (prefixWord ++ tailWord_2166274).sum := by decide
  have hdescent : baseEnd_2166274 < baseStart_2166274 := by decide
  rcases family_descends (prefixWord ++ tailWord_2166274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2166300 : List Nat := [2, 2, 3, 1, 2, 1, 3, 2, 1, 5]
def baseStart_2166300 : Nat := 118140960795 + 2166300 * 2 ^ 59
def prefixEnd_2166300 : Nat := 4983230072969 + 3 ^ 40 * 2166300 * 2
def baseEnd_2166300 : Nat := 741568761223319716658249

theorem tailTrace_2166300 : CollatzResearch.WordTrace tailWord_2166300 prefixEnd_2166300 741568761223319716658249 := by
  unfold tailWord_2166300
  simp only [CollatzResearch.WordTrace]
  refine ⟨39505726025936274714964177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52674301367915032953285569 39505726025936274714964177)
  ·
    refine ⟨29629294519452206036223133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39505726025936274714964177 29629294519452206036223133)
    ·
      refine ⟨11110985444794577263583675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29629294519452206036223133 11110985444794577263583675)
      ·
        refine ⟨16666478167191865895375513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11110985444794577263583675 16666478167191865895375513)
        ·
          refine ⟨12499858625393899421531635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16666478167191865895375513 12499858625393899421531635)
          ·
            refine ⟨18749787938090849132297453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12499858625393899421531635 18749787938090849132297453)
            ·
              refine ⟨7031170476784068424611545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18749787938090849132297453 7031170476784068424611545)
              ·
                refine ⟨5273377857588051318458659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7031170476784068424611545 5273377857588051318458659)
                ·
                  refine ⟨7910066786382076977687989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5273377857588051318458659 7910066786382076977687989)
                  ·
                    refine ⟨741568761223319716658249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7910066786382076977687989 741568761223319716658249)
                    ·
                      rfl

theorem cell22_2166300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 3, 2, 1, 5].length) (baseStart_2166300 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2166300 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2166300 prefixEnd_2166300 := by exact prefixLift 2166300
  have htrace : WordTrace (prefixWord ++ tailWord_2166300) baseStart_2166300 baseEnd_2166300 := by
    simpa [prefixWord, tailWord_2166300, baseEnd_2166300] using wordTrace_append hprefix tailTrace_2166300
  have hstable : (prefixWord ++ tailWord_2166300).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2166300).length < 2 ^ (prefixWord ++ tailWord_2166300).sum := by decide
  have hdescent : baseEnd_2166300 < baseStart_2166300 := by decide
  rcases family_descends (prefixWord ++ tailWord_2166300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2166304 : List Nat := [2, 1, 1, 6, 1, 2, 3, 1, 1, 4]
def baseStart_2166304 : Nat := 118140960795 + 2166304 * 2 ^ 59
def prefixEnd_2166304 : Nat := 4983230072969 + 3 ^ 40 * 2166304 * 2
def baseEnd_2166304 : Nat := 741570130505065039558237

theorem tailTrace_2166304 : CollatzResearch.WordTrace tailWord_2166304 prefixEnd_2166304 741570130505065039558237 := by
  unfold tailWord_2166304
  simp only [CollatzResearch.WordTrace]
  refine ⟨39505798971929029056536983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52674398629238705408715977 39505798971929029056536983)
  ·
    refine ⟨59258698457893543584805475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39505798971929029056536983 59258698457893543584805475)
    ·
      refine ⟨88888047686840315377208213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59258698457893543584805475 88888047686840315377208213)
      ·
        refine ⟨4166627235320639783306635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 88888047686840315377208213 4166627235320639783306635)
        ·
          refine ⟨6249940852980959674959953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4166627235320639783306635 6249940852980959674959953)
          ·
            refine ⟨4687455639735719756219965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6249940852980959674959953 4687455639735719756219965)
            ·
              refine ⟨1757795864900894908582487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4687455639735719756219965 1757795864900894908582487)
              ·
                refine ⟨2636693797351342362873731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1757795864900894908582487 2636693797351342362873731)
                ·
                  refine ⟨3955040696027013544310597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2636693797351342362873731 3955040696027013544310597)
                  ·
                    refine ⟨741570130505065039558237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3955040696027013544310597 741570130505065039558237)
                    ·
                      rfl

theorem cell22_2166304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 3, 1, 1, 4].length) (baseStart_2166304 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2166304 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2166304 prefixEnd_2166304 := by exact prefixLift 2166304
  have htrace : WordTrace (prefixWord ++ tailWord_2166304) baseStart_2166304 baseEnd_2166304 := by
    simpa [prefixWord, tailWord_2166304, baseEnd_2166304] using wordTrace_append hprefix tailTrace_2166304
  have hstable : (prefixWord ++ tailWord_2166304).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2166304).length < 2 ^ (prefixWord ++ tailWord_2166304).sum := by decide
  have hdescent : baseEnd_2166304 < baseStart_2166304 := by decide
  rcases family_descends (prefixWord ++ tailWord_2166304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2166437 : List Nat := [1, 3, 1, 2, 1, 2, 2, 6, 4]
def baseStart_2166437 : Nat := 118140960795 + 2166437 * 2 ^ 59
def prefixEnd_2166437 : Nat := 4983230072969 + 3 ^ 40 * 2166437 * 2
def baseEnd_2166437 : Nat := 247205219707699008660943

theorem tailTrace_2166437 : CollatzResearch.WordTrace tailWord_2166437 prefixEnd_2166437 247205219707699008660943 := by
  unfold tailWord_2166437
  simp only [CollatzResearch.WordTrace]
  refine ⟨79016448852376221827665565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52677632568250814551777043 79016448852376221827665565)
  ·
    refine ⟨29631168319641083185374587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 79016448852376221827665565 29631168319641083185374587)
    ·
      refine ⟨44446752479461624778061881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29631168319641083185374587 44446752479461624778061881)
      ·
        refine ⟨33335064359596218583546411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44446752479461624778061881 33335064359596218583546411)
        ·
          refine ⟨50002596539394327875319617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33335064359596218583546411 50002596539394327875319617)
          ·
            refine ⟨37501947404545745906489713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50002596539394327875319617 37501947404545745906489713)
            ·
              refine ⟨28126460553409309429867285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37501947404545745906489713 28126460553409309429867285)
              ·
                refine ⟨1318427838441061379525029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 28126460553409309429867285 1318427838441061379525029)
                ·
                  refine ⟨247205219707699008660943, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1318427838441061379525029 247205219707699008660943)
                  ·
                    rfl

theorem cell22_2166437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 6, 4].length) (baseStart_2166437 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2166437 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2166437 prefixEnd_2166437 := by exact prefixLift 2166437
  have htrace : WordTrace (prefixWord ++ tailWord_2166437) baseStart_2166437 baseEnd_2166437 := by
    simpa [prefixWord, tailWord_2166437, baseEnd_2166437] using wordTrace_append hprefix tailTrace_2166437
  have hstable : (prefixWord ++ tailWord_2166437).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2166437).length < 2 ^ (prefixWord ++ tailWord_2166437).sum := by decide
  have hdescent : baseEnd_2166437 < baseStart_2166437 := by decide
  rcases family_descends (prefixWord ++ tailWord_2166437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2166450 : List Nat := [3, 2, 1, 1, 1, 2, 2, 1, 3, 6]
def baseStart_2166450 : Nat := 118140960795 + 2166450 * 2 ^ 59
def prefixEnd_2166450 : Nat := 4983230072969 + 3 ^ 40 * 2166450 * 2
def baseEnd_2166450 : Nat := 741620109288769325407789

theorem tailTrace_2166450 : CollatzResearch.WordTrace tailWord_2166450 prefixEnd_2166450 741620109288769325407789 := by
  unfold tailWord_2166450
  simp only [CollatzResearch.WordTrace]
  refine ⟨19754230750332281261972201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52677948667552750031925869 19754230750332281261972201)
  ·
    refine ⟨14815673062749210946479151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19754230750332281261972201 14815673062749210946479151)
    ·
      refine ⟨22223509594123816419718727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14815673062749210946479151 22223509594123816419718727)
      ·
        refine ⟨33335264391185724629578091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22223509594123816419718727 33335264391185724629578091)
        ·
          refine ⟨50002896586778586944367137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33335264391185724629578091 50002896586778586944367137)
          ·
            refine ⟨37502172440083940208275353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50002896586778586944367137 37502172440083940208275353)
            ·
              refine ⟨28126629330062955156206515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37502172440083940208275353 28126629330062955156206515)
              ·
                refine ⟨42189943995094432734309773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28126629330062955156206515 42189943995094432734309773)
                ·
                  refine ⟨15821228998160412275366165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 42189943995094432734309773 15821228998160412275366165)
                  ·
                    refine ⟨741620109288769325407789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15821228998160412275366165 741620109288769325407789)
                    ·
                      rfl

theorem cell22_2166450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 1, 3, 6].length) (baseStart_2166450 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2166450 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2166450 prefixEnd_2166450 := by exact prefixLift 2166450
  have htrace : WordTrace (prefixWord ++ tailWord_2166450) baseStart_2166450 baseEnd_2166450 := by
    simpa [prefixWord, tailWord_2166450, baseEnd_2166450] using wordTrace_append hprefix tailTrace_2166450
  have hstable : (prefixWord ++ tailWord_2166450).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2166450).length < 2 ^ (prefixWord ++ tailWord_2166450).sum := by decide
  have hdescent : baseEnd_2166450 < baseStart_2166450 := by decide
  rcases family_descends (prefixWord ++ tailWord_2166450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2166484 : List Nat := [2, 4, 1, 3, 1, 1, 2, 2, 2, 4]
def baseStart_2166484 : Nat := 118140960795 + 2166484 * 2 ^ 59
def prefixEnd_2166484 : Nat := 4983230072969 + 3 ^ 40 * 2166484 * 2
def baseEnd_2166484 : Nat := 741631748183604570057685

theorem tailTrace_2166484 : CollatzResearch.WordTrace tailWord_2166484 prefixEnd_2166484 741631748183604570057685 := by
  unfold tailWord_2166484
  simp only [CollatzResearch.WordTrace]
  refine ⟨39509081541602974427313253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52678775388803965903084337 39509081541602974427313253)
  ·
    refine ⟨7407952789050557705121235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 39509081541602974427313253 7407952789050557705121235)
    ·
      refine ⟨11111929183575836557681853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7407952789050557705121235 11111929183575836557681853)
      ·
        refine ⟨4166973443840938709130695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11111929183575836557681853 4166973443840938709130695)
        ·
          refine ⟨6250460165761408063696043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4166973443840938709130695 6250460165761408063696043)
          ·
            refine ⟨9375690248642112095544065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6250460165761408063696043 9375690248642112095544065)
            ·
              refine ⟨7031767686481584071658049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9375690248642112095544065 7031767686481584071658049)
              ·
                refine ⟨5273825764861188053743537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7031767686481584071658049 5273825764861188053743537)
                ·
                  refine ⟨3955369323645891040307653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5273825764861188053743537 3955369323645891040307653)
                  ·
                    refine ⟨741631748183604570057685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3955369323645891040307653 741631748183604570057685)
                    ·
                      rfl

theorem cell22_2166484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 2, 2, 2, 4].length) (baseStart_2166484 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2166484 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2166484 prefixEnd_2166484 := by exact prefixLift 2166484
  have htrace : WordTrace (prefixWord ++ tailWord_2166484) baseStart_2166484 baseEnd_2166484 := by
    simpa [prefixWord, tailWord_2166484, baseEnd_2166484] using wordTrace_append hprefix tailTrace_2166484
  have hstable : (prefixWord ++ tailWord_2166484).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2166484).length < 2 ^ (prefixWord ++ tailWord_2166484).sum := by decide
  have hdescent : baseEnd_2166484 < baseStart_2166484 := by decide
  rcases family_descends (prefixWord ++ tailWord_2166484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2166495 : List Nat := [1, 1, 2, 3, 2, 2, 1, 1, 1, 8]
def baseStart_2166495 : Nat := 118140960795 + 2166495 * 2 ^ 59
def prefixEnd_2166495 : Nat := 4983230072969 + 3 ^ 40 * 2166495 * 2
def baseEnd_2166495 : Nat := 741635513708404208032651

theorem tailTrace_2166495 : CollatzResearch.WordTrace tailWord_2166495 prefixEnd_2166495 741635513708404208032651 := by
  unfold tailWord_2166495
  simp only [CollatzResearch.WordTrace]
  refine ⟨79018564286166097733276939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52679042857444065155517959 79018564286166097733276939)
  ·
    refine ⟨118527846429249146599915409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79018564286166097733276939 118527846429249146599915409)
    ·
      refine ⟨88895884821936859949936557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 118527846429249146599915409 88895884821936859949936557)
      ·
        refine ⟨33335956808226322481226209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 88895884821936859949936557 33335956808226322481226209)
        ·
          refine ⟨25001967606169741860919657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33335956808226322481226209 25001967606169741860919657)
          ·
            refine ⟨18751475704627306395689743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25001967606169741860919657 18751475704627306395689743)
            ·
              refine ⟨28127213556940959593534615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18751475704627306395689743 28127213556940959593534615)
              ·
                refine ⟨42190820335411439390301923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28127213556940959593534615 42190820335411439390301923)
                ·
                  refine ⟨63286230503117159085452885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 42190820335411439390301923 63286230503117159085452885)
                  ·
                    refine ⟨741635513708404208032651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 63286230503117159085452885 741635513708404208032651)
                    ·
                      rfl

theorem cell22_2166495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 1, 1, 8].length) (baseStart_2166495 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2166495 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2166495 prefixEnd_2166495 := by exact prefixLift 2166495
  have htrace : WordTrace (prefixWord ++ tailWord_2166495) baseStart_2166495 baseEnd_2166495 := by
    simpa [prefixWord, tailWord_2166495, baseEnd_2166495] using wordTrace_append hprefix tailTrace_2166495
  have hstable : (prefixWord ++ tailWord_2166495).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2166495).length < 2 ^ (prefixWord ++ tailWord_2166495).sum := by decide
  have hdescent : baseEnd_2166495 < baseStart_2166495 := by decide
  rcases family_descends (prefixWord ++ tailWord_2166495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2166499 : List Nat := [1, 1, 1, 7, 2, 2, 1, 7]
def baseStart_2166499 : Nat := 118140960795 + 2166499 * 2 ^ 59
def prefixEnd_2166499 : Nat := 4983230072969 + 3 ^ 40 * 2166499 * 2
def baseEnd_2166499 : Nat := 82404098110016614548071

theorem tailTrace_2166499 : CollatzResearch.WordTrace tailWord_2166499 prefixEnd_2166499 82404098110016614548071 := by
  unfold tailWord_2166499
  simp only [CollatzResearch.WordTrace]
  refine ⟨79018710178151606416422551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52679140118767737610948367 79018710178151606416422551)
  ·
    refine ⟨118528065267227409624633827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79018710178151606416422551 118528065267227409624633827)
    ·
      refine ⟨177792097900841114436950741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118528065267227409624633827 177792097900841114436950741)
      ·
        refine ⟨4167002294550963619616033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 177792097900841114436950741 4167002294550963619616033)
        ·
          refine ⟨3125251720913222714712025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4167002294550963619616033 3125251720913222714712025)
          ·
            refine ⟨2343938790684917036034019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3125251720913222714712025 2343938790684917036034019)
            ·
              refine ⟨3515908186027375554051029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2343938790684917036034019 3515908186027375554051029)
              ·
                refine ⟨82404098110016614548071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3515908186027375554051029 82404098110016614548071)
                ·
                  rfl

theorem cell22_2166499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 2, 1, 7].length) (baseStart_2166499 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2166499 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2166499 prefixEnd_2166499 := by exact prefixLift 2166499
  have htrace : WordTrace (prefixWord ++ tailWord_2166499) baseStart_2166499 baseEnd_2166499 := by
    simpa [prefixWord, tailWord_2166499, baseEnd_2166499] using wordTrace_append hprefix tailTrace_2166499
  have hstable : (prefixWord ++ tailWord_2166499).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2166499).length < 2 ^ (prefixWord ++ tailWord_2166499).sum := by decide
  have hdescent : baseEnd_2166499 < baseStart_2166499 := by decide
  rcases family_descends (prefixWord ++ tailWord_2166499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2166514 : List Nat := [3, 2, 1, 3, 1, 1, 3, 2, 3, 3]
def baseStart_2166514 : Nat := 118140960795 + 2166514 * 2 ^ 59
def prefixEnd_2166514 : Nat := 4983230072969 + 3 ^ 40 * 2166514 * 2
def baseEnd_2166514 : Nat := 741642017796694491807593

theorem tailTrace_2166514 : CollatzResearch.WordTrace tailWord_2166514 prefixEnd_2166514 741642017796694491807593 := by
  unfold tailWord_2166514
  simp only [CollatzResearch.WordTrace]
  refine ⟨19754814318274315994554649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52679504848731509318812397 19754814318274315994554649)
  ·
    refine ⟨14816110738705736995915987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19754814318274315994554649 14816110738705736995915987)
    ·
      refine ⟨22224166108058605493873981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14816110738705736995915987 22224166108058605493873981)
      ·
        refine ⟨8334062290521977060202743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22224166108058605493873981 8334062290521977060202743)
        ·
          refine ⟨12501093435782965590304115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8334062290521977060202743 12501093435782965590304115)
          ·
            refine ⟨18751640153674448385456173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12501093435782965590304115 18751640153674448385456173)
            ·
              refine ⟨7031865057627918144546065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18751640153674448385456173 7031865057627918144546065)
              ·
                refine ⟨5273898793220938608409549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7031865057627918144546065 5273898793220938608409549)
                ·
                  refine ⟨1977712047457851978153581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5273898793220938608409549 1977712047457851978153581)
                  ·
                    refine ⟨741642017796694491807593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1977712047457851978153581 741642017796694491807593)
                    ·
                      rfl

theorem cell22_2166514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 3, 2, 3, 3].length) (baseStart_2166514 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2166514 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2166514 prefixEnd_2166514 := by exact prefixLift 2166514
  have htrace : WordTrace (prefixWord ++ tailWord_2166514) baseStart_2166514 baseEnd_2166514 := by
    simpa [prefixWord, tailWord_2166514, baseEnd_2166514] using wordTrace_append hprefix tailTrace_2166514
  have hstable : (prefixWord ++ tailWord_2166514).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2166514).length < 2 ^ (prefixWord ++ tailWord_2166514).sum := by decide
  have hdescent : baseEnd_2166514 < baseStart_2166514 := by decide
  rcases family_descends (prefixWord ++ tailWord_2166514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2166542 : List Nat := [4, 1, 1, 2, 1, 1, 3, 2, 2, 5]
def baseStart_2166542 : Nat := 118140960795 + 2166542 * 2 ^ 59
def prefixEnd_2166542 : Nat := 4983230072969 + 3 ^ 40 * 2166542 * 2
def baseEnd_2166542 : Nat := 741651602768911752107507

theorem tailTrace_2166542 : CollatzResearch.WordTrace tailWord_2166542 prefixEnd_2166542 741651602768911752107507 := by
  unfold tailWord_2166542
  simp only [CollatzResearch.WordTrace]
  refine ⟨9877534814624478095029735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 52680185677997216506825253 9877534814624478095029735)
  ·
    refine ⟨14816302221936717142544603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9877534814624478095029735 14816302221936717142544603)
    ·
      refine ⟨22224453332905075713816905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14816302221936717142544603 22224453332905075713816905)
      ·
        refine ⟨16668339999678806785362679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22224453332905075713816905 16668339999678806785362679)
        ·
          refine ⟨25002509999518210178044019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16668339999678806785362679 25002509999518210178044019)
          ·
            refine ⟨37503764999277315267066029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25002509999518210178044019 37503764999277315267066029)
            ·
              refine ⟨14063911874728993225149761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37503764999277315267066029 14063911874728993225149761)
              ·
                refine ⟨10547933906046744918862321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14063911874728993225149761 10547933906046744918862321)
                ·
                  refine ⟨7910950429535058689146741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10547933906046744918862321 7910950429535058689146741)
                  ·
                    refine ⟨741651602768911752107507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7910950429535058689146741 741651602768911752107507)
                    ·
                      rfl

theorem cell22_2166542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 3, 2, 2, 5].length) (baseStart_2166542 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2166542 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2166542 prefixEnd_2166542 := by exact prefixLift 2166542
  have htrace : WordTrace (prefixWord ++ tailWord_2166542) baseStart_2166542 baseEnd_2166542 := by
    simpa [prefixWord, tailWord_2166542, baseEnd_2166542] using wordTrace_append hprefix tailTrace_2166542
  have hstable : (prefixWord ++ tailWord_2166542).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2166542).length < 2 ^ (prefixWord ++ tailWord_2166542).sum := by decide
  have hdescent : baseEnd_2166542 < baseStart_2166542 := by decide
  rcases family_descends (prefixWord ++ tailWord_2166542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2166555 : List Nat := [1, 1, 1, 1, 1, 1, 4, 2, 10]
def baseStart_2166555 : Nat := 118140960795 + 2166555 * 2 ^ 59
def prefixEnd_2166555 : Nat := 4983230072969 + 3 ^ 40 * 2166555 * 2
def baseEnd_2166555 : Nat := 247218684311528017177489

theorem tailTrace_2166555 : CollatzResearch.WordTrace tailWord_2166555 prefixEnd_2166555 247218684311528017177489 := by
  unfold tailWord_2166555
  simp only [CollatzResearch.WordTrace]
  refine ⟨79020752665948727980461119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52680501777299151986974079 79020752665948727980461119)
  ·
    refine ⟨118531128998923091970691679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79020752665948727980461119 118531128998923091970691679)
    ·
      refine ⟨177796693498384637956037519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118531128998923091970691679 177796693498384637956037519)
      ·
        refine ⟨266695040247576956934056279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 177796693498384637956037519 266695040247576956934056279)
        ·
          refine ⟨400042560371365435401084419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 266695040247576956934056279 400042560371365435401084419)
          ·
            refine ⟨600063840557048153101626629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 400042560371365435401084419 600063840557048153101626629)
            ·
              refine ⟨112511970104446528706554993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 600063840557048153101626629 112511970104446528706554993)
              ·
                refine ⟨84383977578334896529916245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 112511970104446528706554993 84383977578334896529916245)
                ·
                  refine ⟨247218684311528017177489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 84383977578334896529916245 247218684311528017177489)
                  ·
                    rfl

theorem cell22_2166555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 2, 10].length) (baseStart_2166555 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2166555 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2166555 prefixEnd_2166555 := by exact prefixLift 2166555
  have htrace : WordTrace (prefixWord ++ tailWord_2166555) baseStart_2166555 baseEnd_2166555 := by
    simpa [prefixWord, tailWord_2166555, baseEnd_2166555] using wordTrace_append hprefix tailTrace_2166555
  have hstable : (prefixWord ++ tailWord_2166555).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2166555).length < 2 ^ (prefixWord ++ tailWord_2166555).sum := by decide
  have hdescent : baseEnd_2166555 < baseStart_2166555 := by decide
  rcases family_descends (prefixWord ++ tailWord_2166555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2166572 : List Nat := [2, 2, 1, 1, 1, 5, 2, 2, 6]
def baseStart_2166572 : Nat := 118140960795 + 2166572 * 2 ^ 59
def prefixEnd_2166572 : Nat := 4983230072969 + 3 ^ 40 * 2166572 * 2
def baseEnd_2166572 : Nat := 247220624127333891285805

theorem tailTrace_2166572 : CollatzResearch.WordTrace tailWord_2166572 prefixEnd_2166572 247220624127333891285805 := by
  unfold tailWord_2166572
  simp only [CollatzResearch.WordTrace]
  refine ⟨39510686353443569941914985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52680915137924759922553313 39510686353443569941914985)
  ·
    refine ⟨29633014765082677456436239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39510686353443569941914985 29633014765082677456436239)
    ·
      refine ⟨44449522147624016184654359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29633014765082677456436239 44449522147624016184654359)
      ·
        refine ⟨66674283221436024276981539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44449522147624016184654359 66674283221436024276981539)
        ·
          refine ⟨100011424832154036415472309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66674283221436024276981539 100011424832154036415472309)
          ·
            refine ⟨9376071078014440913950529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 100011424832154036415472309 9376071078014440913950529)
            ·
              refine ⟨7032053308510830685462897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9376071078014440913950529 7032053308510830685462897)
              ·
                refine ⟨5274039981383123014097173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7032053308510830685462897 5274039981383123014097173)
                ·
                  refine ⟨247220624127333891285805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5274039981383123014097173 247220624127333891285805)
                  ·
                    rfl

theorem cell22_2166572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 6].length) (baseStart_2166572 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2166572 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2166572 prefixEnd_2166572 := by exact prefixLift 2166572
  have htrace : WordTrace (prefixWord ++ tailWord_2166572) baseStart_2166572 baseEnd_2166572 := by
    simpa [prefixWord, tailWord_2166572, baseEnd_2166572] using wordTrace_append hprefix tailTrace_2166572
  have hstable : (prefixWord ++ tailWord_2166572).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2166572).length < 2 ^ (prefixWord ++ tailWord_2166572).sum := by decide
  have hdescent : baseEnd_2166572 < baseStart_2166572 := by decide
  rcases family_descends (prefixWord ++ tailWord_2166572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2166617 : List Nat := [1, 2, 1, 2, 2, 3, 4, 7]
def baseStart_2166617 : Nat := 118140960795 + 2166617 * 2 ^ 59
def prefixEnd_2166617 : Nat := 4983230072969 + 3 ^ 40 * 2166617 * 2
def baseEnd_2166617 : Nat := 82408586311292950720253

theorem tailTrace_2166617 : CollatzResearch.WordTrace tailWord_2166617 prefixEnd_2166617 82408586311292950720253 := by
  unfold tailWord_2166617
  simp only [CollatzResearch.WordTrace]
  refine ⟨79023013991724112569218105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52682009327816075046145403 79023013991724112569218105)
  ·
    refine ⟨59267260493793084426913579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79023013991724112569218105 59267260493793084426913579)
    ·
      refine ⟨88900890740689626640370369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59267260493793084426913579 88900890740689626640370369)
      ·
        refine ⟨66675668055517219980277777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 88900890740689626640370369 66675668055517219980277777)
        ·
          refine ⟨50006751041637914985208333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66675668055517219980277777 50006751041637914985208333)
          ·
            refine ⟨18752531640614218119453125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 50006751041637914985208333 18752531640614218119453125)
            ·
              refine ⟨3516099682615165897397461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18752531640614218119453125 3516099682615165897397461)
              ·
                refine ⟨82408586311292950720253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3516099682615165897397461 82408586311292950720253)
                ·
                  rfl

theorem cell22_2166617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 4, 7].length) (baseStart_2166617 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2166617 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2166617 prefixEnd_2166617 := by exact prefixLift 2166617
  have htrace : WordTrace (prefixWord ++ tailWord_2166617) baseStart_2166617 baseEnd_2166617 := by
    simpa [prefixWord, tailWord_2166617, baseEnd_2166617] using wordTrace_append hprefix tailTrace_2166617
  have hstable : (prefixWord ++ tailWord_2166617).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2166617).length < 2 ^ (prefixWord ++ tailWord_2166617).sum := by decide
  have hdescent : baseEnd_2166617 < baseStart_2166617 := by decide
  rcases family_descends (prefixWord ++ tailWord_2166617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2166657 : List Nat := [1, 2, 4, 4, 2, 1, 2, 2, 4]
def baseStart_2166657 : Nat := 118140960795 + 2166657 * 2 ^ 59
def prefixEnd_2166657 : Nat := 4983230072969 + 3 ^ 40 * 2166657 * 2
def baseEnd_2166657 : Nat := 247230323206363261827385

theorem tailTrace_2166657 : CollatzResearch.WordTrace tailWord_2166657 prefixEnd_2166657 247230323206363261827385 := by
  unfold tailWord_2166657
  simp only [CollatzResearch.WordTrace]
  refine ⟨79024472911579199400674225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52682981941052799600449483 79024472911579199400674225)
  ·
    refine ⟨59268354683684399550505669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79024472911579199400674225 59268354683684399550505669)
    ·
      refine ⟨11112816503190824915719813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 59268354683684399550505669 11112816503190824915719813)
      ·
        refine ⟨2083653094348279671697465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11112816503190824915719813 2083653094348279671697465)
        ·
          refine ⟨1562739820761209753773099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2083653094348279671697465 1562739820761209753773099)
          ·
            refine ⟨2344109731141814630659649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1562739820761209753773099 2344109731141814630659649)
            ·
              refine ⟨1758082298356360972994737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2344109731141814630659649 1758082298356360972994737)
              ·
                refine ⟨1318561723767270729746053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1758082298356360972994737 1318561723767270729746053)
                ·
                  refine ⟨247230323206363261827385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1318561723767270729746053 247230323206363261827385)
                  ·
                    rfl

theorem cell22_2166657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 2, 1, 2, 2, 4].length) (baseStart_2166657 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2166657 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2166657 prefixEnd_2166657 := by exact prefixLift 2166657
  have htrace : WordTrace (prefixWord ++ tailWord_2166657) baseStart_2166657 baseEnd_2166657 := by
    simpa [prefixWord, tailWord_2166657, baseEnd_2166657] using wordTrace_append hprefix tailTrace_2166657
  have hstable : (prefixWord ++ tailWord_2166657).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2166657).length < 2 ^ (prefixWord ++ tailWord_2166657).sum := by decide
  have hdescent : baseEnd_2166657 < baseStart_2166657 := by decide
  rcases family_descends (prefixWord ++ tailWord_2166657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2166679 : List Nat := [1, 1, 3, 3, 1, 3, 2, 3, 5]
def baseStart_2166679 : Nat := 118140960795 + 2166679 * 2 ^ 59
def prefixEnd_2166679 : Nat := 4983230072969 + 3 ^ 40 * 2166679 * 2
def baseEnd_2166679 : Nat := 247232833556229687144029

theorem tailTrace_2166679 : CollatzResearch.WordTrace tailWord_2166679 prefixEnd_2166679 247232833556229687144029 := by
  unfold tailWord_2166679
  simp only [CollatzResearch.WordTrace]
  refine ⟨79025275317499497157975091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52683516878332998105316727 79025275317499497157975091)
  ·
    refine ⟨118537912976249245736962637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79025275317499497157975091 118537912976249245736962637)
    ·
      refine ⟨44451717366093467151360989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 118537912976249245736962637 44451717366093467151360989)
      ·
        refine ⟨16669394012285050181760371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44451717366093467151360989 16669394012285050181760371)
        ·
          refine ⟨25004091018427575272640557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16669394012285050181760371 25004091018427575272640557)
          ·
            refine ⟨9376534131910340727240209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25004091018427575272640557 9376534131910340727240209)
            ·
              refine ⟨7032400598932755545430157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9376534131910340727240209 7032400598932755545430157)
              ·
                refine ⟨2637150224599783329536309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7032400598932755545430157 2637150224599783329536309)
                ·
                  refine ⟨247232833556229687144029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2637150224599783329536309 247232833556229687144029)
                  ·
                    rfl

theorem cell22_2166679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 2, 3, 5].length) (baseStart_2166679 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2166679 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2166679 prefixEnd_2166679 := by exact prefixLift 2166679
  have htrace : WordTrace (prefixWord ++ tailWord_2166679) baseStart_2166679 baseEnd_2166679 := by
    simpa [prefixWord, tailWord_2166679, baseEnd_2166679] using wordTrace_append hprefix tailTrace_2166679
  have hstable : (prefixWord ++ tailWord_2166679).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2166679).length < 2 ^ (prefixWord ++ tailWord_2166679).sum := by decide
  have hdescent : baseEnd_2166679 < baseStart_2166679 := by decide
  rcases family_descends (prefixWord ++ tailWord_2166679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2166707 : List Nat := [1, 1, 1, 2, 3, 1, 3, 2, 8]
def baseStart_2166707 : Nat := 118140960795 + 2166707 * 2 ^ 59
def prefixEnd_2166707 : Nat := 4983230072969 + 3 ^ 40 * 2166707 * 2
def baseEnd_2166707 : Nat := 247236028546968773910667

theorem tailTrace_2166707 : CollatzResearch.WordTrace tailWord_2166707 prefixEnd_2166707 247236028546968773910667 := by
  unfold tailWord_2166707
  simp only [CollatzResearch.WordTrace]
  refine ⟨79026296561398057939994375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52684197707598705293329583 79026296561398057939994375)
  ·
    refine ⟨118539444842097086909991563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79026296561398057939994375 118539444842097086909991563)
    ·
      refine ⟨177809167263145630364987345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118539444842097086909991563 177809167263145630364987345)
      ·
        refine ⟨133356875447359222773740509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 177809167263145630364987345 133356875447359222773740509)
        ·
          refine ⟨50008828292759708540152691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 133356875447359222773740509 50008828292759708540152691)
          ·
            refine ⟨75013242439139562810229037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50008828292759708540152691 75013242439139562810229037)
            ·
              refine ⟨28129965914677336053835889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 75013242439139562810229037 28129965914677336053835889)
              ·
                refine ⟨21097474436008002040376917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28129965914677336053835889 21097474436008002040376917)
                ·
                  refine ⟨247236028546968773910667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 21097474436008002040376917 247236028546968773910667)
                  ·
                    rfl

theorem cell22_2166707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 2, 8].length) (baseStart_2166707 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2166707 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2166707 prefixEnd_2166707 := by exact prefixLift 2166707
  have htrace : WordTrace (prefixWord ++ tailWord_2166707) baseStart_2166707 baseEnd_2166707 := by
    simpa [prefixWord, tailWord_2166707, baseEnd_2166707] using wordTrace_append hprefix tailTrace_2166707
  have hstable : (prefixWord ++ tailWord_2166707).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2166707).length < 2 ^ (prefixWord ++ tailWord_2166707).sum := by decide
  have hdescent : baseEnd_2166707 < baseStart_2166707 := by decide
  rcases family_descends (prefixWord ++ tailWord_2166707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2166835 : List Nat := [1, 1, 1, 2, 4, 1, 6, 2, 1, 3]
def baseStart_2166835 : Nat := 118140960795 + 2166835 * 2 ^ 59
def prefixEnd_2166835 : Nat := 4983230072969 + 3 ^ 40 * 2166835 * 2
def baseEnd_2166835 : Nat := 741751902656756654531609

theorem tailTrace_2166835 : CollatzResearch.WordTrace tailWord_2166835 prefixEnd_2166835 741751902656756654531609 := by
  unfold tailWord_2166835
  simp only [CollatzResearch.WordTrace]
  refine ⟨79030965104934335800653959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52687310069956223867102639 79030965104934335800653959)
  ·
    refine ⟨118546447657401503700980939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79030965104934335800653959 118546447657401503700980939)
    ·
      refine ⟨177819671486102255551471409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118546447657401503700980939 177819671486102255551471409)
      ·
        refine ⟨133364753614576691663603557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 177819671486102255551471409 133364753614576691663603557)
        ·
          refine ⟨25005891302733129686925667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 133364753614576691663603557 25005891302733129686925667)
          ·
            refine ⟨37508836954099694530388501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25005891302733129686925667 37508836954099694530388501)
            ·
              refine ⟨1758226732223423181111961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 37508836954099694530388501 1758226732223423181111961)
              ·
                refine ⟨1318670049167567385833971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1758226732223423181111961 1318670049167567385833971)
                ·
                  refine ⟨1978005073751351078750957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1318670049167567385833971 1978005073751351078750957)
                  ·
                    refine ⟨741751902656756654531609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1978005073751351078750957 741751902656756654531609)
                    ·
                      rfl

theorem cell22_2166835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 6, 2, 1, 3].length) (baseStart_2166835 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2166835 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2166835 prefixEnd_2166835 := by exact prefixLift 2166835
  have htrace : WordTrace (prefixWord ++ tailWord_2166835) baseStart_2166835 baseEnd_2166835 := by
    simpa [prefixWord, tailWord_2166835, baseEnd_2166835] using wordTrace_append hprefix tailTrace_2166835
  have hstable : (prefixWord ++ tailWord_2166835).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2166835).length < 2 ^ (prefixWord ++ tailWord_2166835).sum := by decide
  have hdescent : baseEnd_2166835 < baseStart_2166835 := by decide
  rcases family_descends (prefixWord ++ tailWord_2166835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2166859 : List Nat := [1, 1, 1, 1, 3, 1, 2, 6, 6]
def baseStart_2166859 : Nat := 118140960795 + 2166859 * 2 ^ 59
def prefixEnd_2166859 : Nat := 4983230072969 + 3 ^ 40 * 2166859 * 2
def baseEnd_2166859 : Nat := 247253372782409530643845

theorem tailTrace_2166859 : CollatzResearch.WordTrace tailWord_2166859 prefixEnd_2166859 247253372782409530643845 := by
  unfold tailWord_2166859
  simp only [CollatzResearch.WordTrace]
  refine ⟨79031840456847387899527631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52687893637898258599685087 79031840456847387899527631)
  ·
    refine ⟨118547760685271081849291447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79031840456847387899527631 118547760685271081849291447)
    ·
      refine ⟨177821641027906622773937171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118547760685271081849291447 177821641027906622773937171)
      ·
        refine ⟨266732461541859934160905757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 177821641027906622773937171 266732461541859934160905757)
        ·
          refine ⟨100024673078197475310339659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 266732461541859934160905757 100024673078197475310339659)
          ·
            refine ⟨150037009617296212965509489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 100024673078197475310339659 150037009617296212965509489)
            ·
              refine ⟨112527757212972159724132117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 150037009617296212965509489 112527757212972159724132117)
              ·
                refine ⟨5274738619358069987068693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 112527757212972159724132117 5274738619358069987068693)
                ·
                  refine ⟨247253372782409530643845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5274738619358069987068693 247253372782409530643845)
                  ·
                    rfl

theorem cell22_2166859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 6, 6].length) (baseStart_2166859 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2166859 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2166859 prefixEnd_2166859 := by exact prefixLift 2166859
  have htrace : WordTrace (prefixWord ++ tailWord_2166859) baseStart_2166859 baseEnd_2166859 := by
    simpa [prefixWord, tailWord_2166859, baseEnd_2166859] using wordTrace_append hprefix tailTrace_2166859
  have hstable : (prefixWord ++ tailWord_2166859).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2166859).length < 2 ^ (prefixWord ++ tailWord_2166859).sum := by decide
  have hdescent : baseEnd_2166859 < baseStart_2166859 := by decide
  rcases family_descends (prefixWord ++ tailWord_2166859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2166882 : List Nat := [3, 3, 2, 2, 3, 1, 1, 2, 5]
def baseStart_2166882 : Nat := 118140960795 + 2166882 * 2 ^ 59
def prefixEnd_2166882 : Nat := 4983230072969 + 3 ^ 40 * 2166882 * 2
def baseEnd_2166882 : Nat := 247255997239088066202155

theorem tailTrace_2166882 : CollatzResearch.WordTrace tailWord_2166882 prefixEnd_2166882 247255997239088066202155 := by
  unfold tailWord_2166882
  simp only [CollatzResearch.WordTrace]
  refine ⟨19758169833941015706903725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52688452890509375218409933 19758169833941015706903725)
  ·
    refine ⟨7409313687727880890088897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19758169833941015706903725 7409313687727880890088897)
    ·
      refine ⟨5556985265795910667566673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7409313687727880890088897 5556985265795910667566673)
      ·
        refine ⟨4167738949346933000675005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5556985265795910667566673 4167738949346933000675005)
        ·
          refine ⟨1562902106005099875253127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4167738949346933000675005 1562902106005099875253127)
          ·
            refine ⟨2344353159007649812879691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1562902106005099875253127 2344353159007649812879691)
            ·
              refine ⟨3516529738511474719319537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2344353159007649812879691 3516529738511474719319537)
              ·
                refine ⟨2637397303883606039489653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3516529738511474719319537 2637397303883606039489653)
                ·
                  refine ⟨247255997239088066202155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2637397303883606039489653 247255997239088066202155)
                  ·
                    rfl

theorem cell22_2166882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 3, 1, 1, 2, 5].length) (baseStart_2166882 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2166882 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2166882 prefixEnd_2166882 := by exact prefixLift 2166882
  have htrace : WordTrace (prefixWord ++ tailWord_2166882) baseStart_2166882 baseEnd_2166882 := by
    simpa [prefixWord, tailWord_2166882, baseEnd_2166882] using wordTrace_append hprefix tailTrace_2166882
  have hstable : (prefixWord ++ tailWord_2166882).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2166882).length < 2 ^ (prefixWord ++ tailWord_2166882).sum := by decide
  have hdescent : baseEnd_2166882 < baseStart_2166882 := by decide
  rcases family_descends (prefixWord ++ tailWord_2166882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
