import V185TrunkScan22Chunk443

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_3958709 : List Nat := [1, 3, 3, 2, 1, 2, 1, 2, 1, 6]
def baseStart_3958709 : Nat := 118140960795 + 3958709 * 2 ^ 59
def prefixEnd_3958709 : Nat := 4983230072969 + 3 ^ 40 * 3958709 * 2
def baseEnd_3958709 : Nat := 1355146992186438177687823

theorem tailTrace_3958709 : CollatzResearch.WordTrace tailWord_3958709 prefixEnd_3958709 1355146992186438177687823 := by
  unfold tailWord_3958709
  simp only [CollatzResearch.WordTrace]
  refine ⟨144385979015280861515743181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96257319343520574343828787 144385979015280861515743181)
  ·
    refine ⟨54144742130730323068403693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 144385979015280861515743181 54144742130730323068403693)
    ·
      refine ⟨20304278299023871150651385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54144742130730323068403693 20304278299023871150651385)
      ·
        refine ⟨15228208724267903362988539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20304278299023871150651385 15228208724267903362988539)
        ·
          refine ⟨22842313086401855044482809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15228208724267903362988539 22842313086401855044482809)
          ·
            refine ⟨17131734814801391283362107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22842313086401855044482809 17131734814801391283362107)
            ·
              refine ⟨25697602222202086925043161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17131734814801391283362107 25697602222202086925043161)
              ·
                refine ⟨19273201666651565193782371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25697602222202086925043161 19273201666651565193782371)
                ·
                  refine ⟨28909802499977347790673557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19273201666651565193782371 28909802499977347790673557)
                  ·
                    refine ⟨1355146992186438177687823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28909802499977347790673557 1355146992186438177687823)
                    ·
                      rfl

theorem cell22_3958709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 1, 2, 1, 6].length) (baseStart_3958709 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3958709 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3958709 prefixEnd_3958709 := by exact prefixLift 3958709
  have htrace : WordTrace (prefixWord ++ tailWord_3958709) baseStart_3958709 baseEnd_3958709 := by
    simpa [prefixWord, tailWord_3958709, baseEnd_3958709] using wordTrace_append hprefix tailTrace_3958709
  have hstable : (prefixWord ++ tailWord_3958709).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3958709).length < 2 ^ (prefixWord ++ tailWord_3958709).sum := by decide
  have hdescent : baseEnd_3958709 < baseStart_3958709 := by decide
  rcases family_descends (prefixWord ++ tailWord_3958709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3958848 : List Nat := [2, 1, 1, 2, 2, 5, 2, 3, 4]
def baseStart_3958848 : Nat := 118140960795 + 3958848 * 2 ^ 59
def prefixEnd_3958848 : Nat := 4983230072969 + 3 ^ 40 * 3958848 * 2
def baseEnd_3958848 : Nat := 451731524909029382820799

theorem tailTrace_3958848 : CollatzResearch.WordTrace tailWord_3958848 prefixEnd_3958848 451731524909029382820799 := by
  unfold tailWord_3958848
  simp only [CollatzResearch.WordTrace]
  refine ⟨72195524380888644127526599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96260699174518192170035465 72195524380888644127526599)
  ·
    refine ⟨108293286571332966191289899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72195524380888644127526599 108293286571332966191289899)
    ·
      refine ⟨162439929856999449286934849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108293286571332966191289899 162439929856999449286934849)
      ·
        refine ⟨121829947392749586965201137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 162439929856999449286934849 121829947392749586965201137)
        ·
          refine ⟨91372460544562190223900853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 121829947392749586965201137 91372460544562190223900853)
          ·
            refine ⟨8566168176052705333490705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 91372460544562190223900853 8566168176052705333490705)
            ·
              refine ⟨6424626132039529000118029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8566168176052705333490705 6424626132039529000118029)
              ·
                refine ⟨2409234799514823375044261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6424626132039529000118029 2409234799514823375044261)
                ·
                  refine ⟨451731524909029382820799, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2409234799514823375044261 451731524909029382820799)
                  ·
                    rfl

theorem cell22_3958848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 2, 3, 4].length) (baseStart_3958848 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3958848 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3958848 prefixEnd_3958848 := by exact prefixLift 3958848
  have htrace : WordTrace (prefixWord ++ tailWord_3958848) baseStart_3958848 baseEnd_3958848 := by
    simpa [prefixWord, tailWord_3958848, baseEnd_3958848] using wordTrace_append hprefix tailTrace_3958848
  have hstable : (prefixWord ++ tailWord_3958848).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3958848).length < 2 ^ (prefixWord ++ tailWord_3958848).sum := by decide
  have hdescent : baseEnd_3958848 < baseStart_3958848 := by decide
  rcases family_descends (prefixWord ++ tailWord_3958848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3958880 : List Nat := [2, 1, 1, 3, 2, 4, 3, 1, 2, 3]
def baseStart_3958880 : Nat := 118140960795 + 3958880 * 2 ^ 59
def prefixEnd_3958880 : Nat := 4983230072969 + 3 ^ 40 * 3958880 * 2
def baseEnd_3958880 : Nat := 1355205528981050731662299

theorem tailTrace_3958880 : CollatzResearch.WordTrace tailWord_3958880 prefixEnd_3958880 1355205528981050731662299 := by
  unfold tailWord_3958880
  simp only [CollatzResearch.WordTrace]
  refine ⟨72196107948830678860109047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96261477265107571813478729 72196107948830678860109047)
  ·
    refine ⟨108294161923246018290163571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72196107948830678860109047 108294161923246018290163571)
    ·
      refine ⟨162441242884869027435245357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108294161923246018290163571 162441242884869027435245357)
      ·
        refine ⟨60915466081825885288217009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 162441242884869027435245357 60915466081825885288217009)
        ·
          refine ⟨45686599561369413966162757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60915466081825885288217009 45686599561369413966162757)
          ·
            refine ⟨8566237417756765118655517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45686599561369413966162757 8566237417756765118655517)
            ·
              refine ⟨3212339031658786919495819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8566237417756765118655517 3212339031658786919495819)
              ·
                refine ⟨4818508547488180379243729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3212339031658786919495819 4818508547488180379243729)
                ·
                  refine ⟨3613881410616135284432797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4818508547488180379243729 3613881410616135284432797)
                  ·
                    refine ⟨1355205528981050731662299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3613881410616135284432797 1355205528981050731662299)
                    ·
                      rfl

theorem cell22_3958880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 3, 1, 2, 3].length) (baseStart_3958880 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3958880 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3958880 prefixEnd_3958880 := by exact prefixLift 3958880
  have htrace : WordTrace (prefixWord ++ tailWord_3958880) baseStart_3958880 baseEnd_3958880 := by
    simpa [prefixWord, tailWord_3958880, baseEnd_3958880] using wordTrace_append hprefix tailTrace_3958880
  have hstable : (prefixWord ++ tailWord_3958880).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3958880).length < 2 ^ (prefixWord ++ tailWord_3958880).sum := by decide
  have hdescent : baseEnd_3958880 < baseStart_3958880 := by decide
  rcases family_descends (prefixWord ++ tailWord_3958880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3958921 : List Nat := [1, 2, 1, 1, 4, 2, 2, 4, 5]
def baseStart_3958921 : Nat := 118140960795 + 3958921 * 2 ^ 59
def prefixEnd_3958921 : Nat := 4983230072969 + 3 ^ 40 * 3958921 * 2
def baseEnd_3958921 : Nat := 451739854706313430462391

theorem tailTrace_3958921 : CollatzResearch.WordTrace tailWord_3958921 prefixEnd_3958921 451739854706313430462391 := by
  unfold tailWord_3958921
  simp only [CollatzResearch.WordTrace]
  refine ⟨144393711290512821722460617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96262474193675214481640411 144393711290512821722460617)
  ·
    refine ⟨108295283467884616291845463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144393711290512821722460617 108295283467884616291845463)
    ·
      refine ⟨162442925201826924437768195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108295283467884616291845463 162442925201826924437768195)
      ·
        refine ⟨243664387802740386656652293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162442925201826924437768195 243664387802740386656652293)
        ·
          refine ⟨45687072713013822498122305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 243664387802740386656652293 45687072713013822498122305)
          ·
            refine ⟨34265304534760366873591729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45687072713013822498122305 34265304534760366873591729)
            ·
              refine ⟨25698978401070275155193797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34265304534760366873591729 25698978401070275155193797)
              ·
                refine ⟨4818558450200676591598837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25698978401070275155193797 4818558450200676591598837)
                ·
                  refine ⟨451739854706313430462391, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4818558450200676591598837 451739854706313430462391)
                  ·
                    rfl

theorem cell22_3958921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 2, 4, 5].length) (baseStart_3958921 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3958921 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3958921 prefixEnd_3958921 := by exact prefixLift 3958921
  have htrace : WordTrace (prefixWord ++ tailWord_3958921) baseStart_3958921 baseEnd_3958921 := by
    simpa [prefixWord, tailWord_3958921, baseEnd_3958921] using wordTrace_append hprefix tailTrace_3958921
  have hstable : (prefixWord ++ tailWord_3958921).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3958921).length < 2 ^ (prefixWord ++ tailWord_3958921).sum := by decide
  have hdescent : baseEnd_3958921 < baseStart_3958921 := by decide
  rcases family_descends (prefixWord ++ tailWord_3958921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3959013 : List Nat := [1, 3, 1, 4, 2, 2, 1, 1, 1, 6]
def baseStart_3959013 : Nat := 118140960795 + 3959013 * 2 ^ 59
def prefixEnd_3959013 : Nat := 4983230072969 + 3 ^ 40 * 3959013 * 2
def baseEnd_3959013 : Nat := 1355251057599082718086891

theorem tailTrace_3959013 : CollatzResearch.WordTrace tailWord_3959013 prefixEnd_3959013 1355251057599082718086891 := by
  unfold tailWord_3959013
  simp only [CollatzResearch.WordTrace]
  refine ⟨144397066806179521434809693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96264711204119680956539795 144397066806179521434809693)
  ·
    refine ⟨54148900052317320538053635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 144397066806179521434809693 54148900052317320538053635)
    ·
      refine ⟨81223350078475980807080453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54148900052317320538053635 81223350078475980807080453)
      ·
        refine ⟨15229378139714246401327585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 81223350078475980807080453 15229378139714246401327585)
        ·
          refine ⟨11422033604785684800995689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15229378139714246401327585 11422033604785684800995689)
          ·
            refine ⟨8566525203589263600746767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11422033604785684800995689 8566525203589263600746767)
            ·
              refine ⟨12849787805383895401120151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8566525203589263600746767 12849787805383895401120151)
              ·
                refine ⟨19274681708075843101680227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12849787805383895401120151 19274681708075843101680227)
                ·
                  refine ⟨28912022562113764652520341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19274681708075843101680227 28912022562113764652520341)
                  ·
                    refine ⟨1355251057599082718086891, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28912022562113764652520341 1355251057599082718086891)
                    ·
                      rfl

theorem cell22_3959013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 1, 1, 1, 6].length) (baseStart_3959013 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3959013 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3959013 prefixEnd_3959013 := by exact prefixLift 3959013
  have htrace : WordTrace (prefixWord ++ tailWord_3959013) baseStart_3959013 baseEnd_3959013 := by
    simpa [prefixWord, tailWord_3959013, baseEnd_3959013] using wordTrace_append hprefix tailTrace_3959013
  have hstable : (prefixWord ++ tailWord_3959013).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3959013).length < 2 ^ (prefixWord ++ tailWord_3959013).sum := by decide
  have hdescent : baseEnd_3959013 < baseStart_3959013 := by decide
  rcases family_descends (prefixWord ++ tailWord_3959013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3959079 : List Nat := [1, 1, 8, 1, 2, 1, 8]
def baseStart_3959079 : Nat := 118140960795 + 3959079 * 2 ^ 59
def prefixEnd_3959079 : Nat := 4983230072969 + 3 ^ 40 * 3959079 * 2
def baseEnd_3959079 : Nat := 50195320398069649849507

theorem tailTrace_3959079 : CollatzResearch.WordTrace tailWord_3959079 prefixEnd_3959079 50195320398069649849507 := by
  unfold tailWord_3959079
  simp only [CollatzResearch.WordTrace]
  refine ⟨144399474023940414706712291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96266316015960276471141527 144399474023940414706712291)
  ·
    refine ⟨216599211035910622060068437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144399474023940414706712291 216599211035910622060068437)
    ·
      refine ⟨2538272004327077602266427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 216599211035910622060068437 2538272004327077602266427)
      ·
        refine ⟨3807408006490616403399641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2538272004327077602266427 3807408006490616403399641)
        ·
          refine ⟨2855556004867962302549731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3807408006490616403399641 2855556004867962302549731)
          ·
            refine ⟨4283334007301943453824597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2855556004867962302549731 4283334007301943453824597)
            ·
              refine ⟨50195320398069649849507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4283334007301943453824597 50195320398069649849507)
              ·
                rfl

theorem cell22_3959079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 2, 1, 8].length) (baseStart_3959079 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3959079 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3959079 prefixEnd_3959079 := by exact prefixLift 3959079
  have htrace : WordTrace (prefixWord ++ tailWord_3959079) baseStart_3959079 baseEnd_3959079 := by
    simpa [prefixWord, tailWord_3959079, baseEnd_3959079] using wordTrace_append hprefix tailTrace_3959079
  have hstable : (prefixWord ++ tailWord_3959079).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3959079).length < 2 ^ (prefixWord ++ tailWord_3959079).sum := by decide
  have hdescent : baseEnd_3959079 < baseStart_3959079 := by decide
  rcases family_descends (prefixWord ++ tailWord_3959079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3959103 : List Nat := [1, 1, 2, 2, 4, 1, 2, 2, 3, 4]
def baseStart_3959103 : Nat := 118140960795 + 3959103 * 2 ^ 59
def prefixEnd_3959103 : Nat := 4983230072969 + 3 ^ 40 * 3959103 * 2
def baseEnd_3959103 : Nat := 1355281866438352483336615

theorem tailTrace_3959103 : CollatzResearch.WordTrace tailWord_3959103 prefixEnd_3959103 1355281866438352483336615 := by
  unfold tailWord_3959103
  simp only [CollatzResearch.WordTrace]
  refine ⟨144400349375853466805585963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96266899583902311203723975 144400349375853466805585963)
  ·
    refine ⟨216600524063780200208378945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144400349375853466805585963 216600524063780200208378945)
    ·
      refine ⟨162450393047835150156284209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 216600524063780200208378945 162450393047835150156284209)
      ·
        refine ⟨121837794785876362617213157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 162450393047835150156284209 121837794785876362617213157)
        ·
          refine ⟨22844586522351817990727467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 121837794785876362617213157 22844586522351817990727467)
          ·
            refine ⟨34266879783527726986091201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22844586522351817990727467 34266879783527726986091201)
            ·
              refine ⟨25700159837645795239568401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34266879783527726986091201 25700159837645795239568401)
              ·
                refine ⟨19275119878234346429676301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25700159837645795239568401 19275119878234346429676301)
                ·
                  refine ⟨7228169954337879911128613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19275119878234346429676301 7228169954337879911128613)
                  ·
                    refine ⟨1355281866438352483336615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7228169954337879911128613 1355281866438352483336615)
                    ·
                      rfl

theorem cell22_3959103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 2, 2, 3, 4].length) (baseStart_3959103 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3959103 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3959103 prefixEnd_3959103 := by exact prefixLift 3959103
  have htrace : WordTrace (prefixWord ++ tailWord_3959103) baseStart_3959103 baseEnd_3959103 := by
    simpa [prefixWord, tailWord_3959103, baseEnd_3959103] using wordTrace_append hprefix tailTrace_3959103
  have hstable : (prefixWord ++ tailWord_3959103).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3959103).length < 2 ^ (prefixWord ++ tailWord_3959103).sum := by decide
  have hdescent : baseEnd_3959103 < baseStart_3959103 := by decide
  rcases family_descends (prefixWord ++ tailWord_3959103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3959120 : List Nat := [2, 1, 1, 1, 1, 6, 3, 2, 1, 4]
def baseStart_3959120 : Nat := 118140960795 + 3959120 * 2 ^ 59
def prefixEnd_3959120 : Nat := 4983230072969 + 3 ^ 40 * 3959120 * 2
def baseEnd_3959120 : Nat := 1355287685885770105661563

theorem tailTrace_3959120 : CollatzResearch.WordTrace tailWord_3959120 prefixEnd_3959120 1355287685885770105661563 := by
  unfold tailWord_3959120
  simp only [CollatzResearch.WordTrace]
  refine ⟨72200484708395939354477407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96267312944527919139303209 72200484708395939354477407)
  ·
    refine ⟨108300727062593909031716111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72200484708395939354477407 108300727062593909031716111)
    ·
      refine ⟨162451090593890863547574167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108300727062593909031716111 162451090593890863547574167)
      ·
        refine ⟨243676635890836295321361251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162451090593890863547574167 243676635890836295321361251)
        ·
          refine ⟨365514953836254442982041877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 243676635890836295321361251 365514953836254442982041877)
          ·
            refine ⟨17133513461074427014783213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 365514953836254442982041877 17133513461074427014783213)
            ·
              refine ⟨6425067547902910130543705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17133513461074427014783213 6425067547902910130543705)
              ·
                refine ⟨4818800660927182597907779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6425067547902910130543705 4818800660927182597907779)
                ·
                  refine ⟨7228200991390773896861669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4818800660927182597907779 7228200991390773896861669)
                  ·
                    refine ⟨1355287685885770105661563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7228200991390773896861669 1355287685885770105661563)
                    ·
                      rfl

theorem cell22_3959120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 3, 2, 1, 4].length) (baseStart_3959120 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3959120 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3959120 prefixEnd_3959120 := by exact prefixLift 3959120
  have htrace : WordTrace (prefixWord ++ tailWord_3959120) baseStart_3959120 baseEnd_3959120 := by
    simpa [prefixWord, tailWord_3959120, baseEnd_3959120] using wordTrace_append hprefix tailTrace_3959120
  have hstable : (prefixWord ++ tailWord_3959120).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3959120).length < 2 ^ (prefixWord ++ tailWord_3959120).sum := by decide
  have hdescent : baseEnd_3959120 < baseStart_3959120 := by decide
  rcases family_descends (prefixWord ++ tailWord_3959120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3959152 : List Nat := [2, 1, 1, 1, 4, 3, 4, 2, 4]
def baseStart_3959152 : Nat := 118140960795 + 3959152 * 2 ^ 59
def prefixEnd_3959152 : Nat := 4983230072969 + 3 ^ 40 * 3959152 * 2
def baseEnd_3959152 : Nat := 451766213379910896287155

theorem tailTrace_3959152 : CollatzResearch.WordTrace tailWord_3959152 prefixEnd_3959152 451766213379910896287155 := by
  unfold tailWord_3959152
  simp only [CollatzResearch.WordTrace]
  refine ⟨72201068276337974087059855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96268091035117298782746473 72201068276337974087059855)
  ·
    refine ⟨108301602414506961130589783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72201068276337974087059855 108301602414506961130589783)
    ·
      refine ⟨162452403621760441695884675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108301602414506961130589783 162452403621760441695884675)
      ·
        refine ⟨243678605432640662543827013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162452403621760441695884675 243678605432640662543827013)
        ·
          refine ⟨45689738518620124226967565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 243678605432640662543827013 45689738518620124226967565)
          ·
            refine ⟨17133651944482546585112837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45689738518620124226967565 17133651944482546585112837)
            ·
              refine ⟨3212559739590477484708657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17133651944482546585112837 3212559739590477484708657)
              ·
                refine ⟨2409419804692858113531493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3212559739590477484708657 2409419804692858113531493)
                ·
                  refine ⟨451766213379910896287155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2409419804692858113531493 451766213379910896287155)
                  ·
                    rfl

theorem cell22_3959152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 4, 2, 4].length) (baseStart_3959152 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3959152 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3959152 prefixEnd_3959152 := by exact prefixLift 3959152
  have htrace : WordTrace (prefixWord ++ tailWord_3959152) baseStart_3959152 baseEnd_3959152 := by
    simpa [prefixWord, tailWord_3959152, baseEnd_3959152] using wordTrace_append hprefix tailTrace_3959152
  have hstable : (prefixWord ++ tailWord_3959152).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3959152).length < 2 ^ (prefixWord ++ tailWord_3959152).sum := by decide
  have hdescent : baseEnd_3959152 < baseStart_3959152 := by decide
  rcases family_descends (prefixWord ++ tailWord_3959152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3959163 : List Nat := [1, 1, 1, 1, 1, 7, 3, 7]
def baseStart_3959163 : Nat := 118140960795 + 3959163 * 2 ^ 59
def prefixEnd_3959163 : Nat := 4983230072969 + 3 ^ 40 * 3959163 * 2
def baseEnd_3959163 : Nat := 150589156184948036315159

theorem tailTrace_3959163 : CollatzResearch.WordTrace tailWord_3959163 prefixEnd_3959163 150589156184948036315159 := by
  unfold tailWord_3959163
  simp only [CollatzResearch.WordTrace]
  refine ⟨144402537755636097052770143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96268358503757398035180095 144402537755636097052770143)
  ·
    refine ⟨216603806633454145579155215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144402537755636097052770143 216603806633454145579155215)
    ·
      refine ⟨324905709950181218368732823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216603806633454145579155215 324905709950181218368732823)
      ·
        refine ⟨487358564925271827553099235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 324905709950181218368732823 487358564925271827553099235)
        ·
          refine ⟨731037847387907741329648853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 487358564925271827553099235 731037847387907741329648853)
          ·
            refine ⟨17133699548154087687413645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 731037847387907741329648853 17133699548154087687413645)
            ·
              refine ⟨6425137330557782882780117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17133699548154087687413645 6425137330557782882780117)
              ·
                refine ⟨150589156184948036315159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6425137330557782882780117 150589156184948036315159)
                ·
                  rfl

theorem cell22_3959163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 3, 7].length) (baseStart_3959163 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3959163 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3959163 prefixEnd_3959163 := by exact prefixLift 3959163
  have htrace : WordTrace (prefixWord ++ tailWord_3959163) baseStart_3959163 baseEnd_3959163 := by
    simpa [prefixWord, tailWord_3959163, baseEnd_3959163] using wordTrace_append hprefix tailTrace_3959163
  have hstable : (prefixWord ++ tailWord_3959163).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3959163).length < 2 ^ (prefixWord ++ tailWord_3959163).sum := by decide
  have hdescent : baseEnd_3959163 < baseStart_3959163 := by decide
  rcases family_descends (prefixWord ++ tailWord_3959163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3959180 : List Nat := [2, 2, 1, 2, 1, 5, 3, 6]
def baseStart_3959180 : Nat := 118140960795 + 3959180 * 2 ^ 59
def prefixEnd_3959180 : Nat := 4983230072969 + 3 ^ 40 * 3959180 * 2
def baseEnd_3959180 : Nat := 150589802790216661017931

theorem tailTrace_3959180 : CollatzResearch.WordTrace tailWord_3959180 prefixEnd_3959180 150589802790216661017931 := by
  unfold tailWord_3959180
  simp only [CollatzResearch.WordTrace]
  refine ⟨72201578898287254478069497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96268771864383005970759329 72201578898287254478069497)
  ·
    refine ⟨54151184173715440858552123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72201578898287254478069497 54151184173715440858552123)
    ·
      refine ⟨81226776260573161287828185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54151184173715440858552123 81226776260573161287828185)
      ·
        refine ⟨60920082195429870965871139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81226776260573161287828185 60920082195429870965871139)
        ·
          refine ⟨91380123293144806448806709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60920082195429870965871139 91380123293144806448806709)
          ·
            refine ⟨8566886558732325604575629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 91380123293144806448806709 8566886558732325604575629)
            ·
              refine ⟨3212582459524622101715861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8566886558732325604575629 3212582459524622101715861)
              ·
                refine ⟨150589802790216661017931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3212582459524622101715861 150589802790216661017931)
                ·
                  rfl

theorem cell22_3959180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 3, 6].length) (baseStart_3959180 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3959180 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3959180 prefixEnd_3959180 := by exact prefixLift 3959180
  have htrace : WordTrace (prefixWord ++ tailWord_3959180) baseStart_3959180 baseEnd_3959180 := by
    simpa [prefixWord, tailWord_3959180, baseEnd_3959180] using wordTrace_append hprefix tailTrace_3959180
  have hstable : (prefixWord ++ tailWord_3959180).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3959180).length < 2 ^ (prefixWord ++ tailWord_3959180).sum := by decide
  have hdescent : baseEnd_3959180 < baseStart_3959180 := by decide
  rcases family_descends (prefixWord ++ tailWord_3959180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3959182 : List Nat := [4, 1, 1, 4, 1, 1, 3, 1, 2, 4]
def baseStart_3959182 : Nat := 118140960795 + 3959182 * 2 ^ 59
def prefixEnd_3959182 : Nat := 4983230072969 + 3 ^ 40 * 3959182 * 2
def baseEnd_3959182 : Nat := 1355308909752822610611373

theorem tailTrace_3959182 : CollatzResearch.WordTrace tailWord_3959182 prefixEnd_3959182 1355308909752822610611373 := by
  unfold tailWord_3959182
  simp only [CollatzResearch.WordTrace]
  refine ⟨18050403842820907912213975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 96268820495044842198474533 18050403842820907912213975)
  ·
    refine ⟨27075605764231361868320963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18050403842820907912213975 27075605764231361868320963)
    ·
      refine ⟨40613408646347042802481445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27075605764231361868320963 40613408646347042802481445)
      ·
        refine ⟨7615014121190070525465271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 40613408646347042802481445 7615014121190070525465271)
        ·
          refine ⟨11422521181785105788197907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7615014121190070525465271 11422521181785105788197907)
          ·
            refine ⟨17133781772677658682296861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11422521181785105788197907 17133781772677658682296861)
            ·
              refine ⟨6425168164754122005861323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17133781772677658682296861 6425168164754122005861323)
              ·
                refine ⟨9637752247131183008791985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6425168164754122005861323 9637752247131183008791985)
                ·
                  refine ⟨7228314185348387256593989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9637752247131183008791985 7228314185348387256593989)
                  ·
                    refine ⟨1355308909752822610611373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7228314185348387256593989 1355308909752822610611373)
                    ·
                      rfl

theorem cell22_3959182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 3, 1, 2, 4].length) (baseStart_3959182 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3959182 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3959182 prefixEnd_3959182 := by exact prefixLift 3959182
  have htrace : WordTrace (prefixWord ++ tailWord_3959182) baseStart_3959182 baseEnd_3959182 := by
    simpa [prefixWord, tailWord_3959182, baseEnd_3959182] using wordTrace_append hprefix tailTrace_3959182
  have hstable : (prefixWord ++ tailWord_3959182).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3959182).length < 2 ^ (prefixWord ++ tailWord_3959182).sum := by decide
  have hdescent : baseEnd_3959182 < baseStart_3959182 := by decide
  rcases family_descends (prefixWord ++ tailWord_3959182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3959201 : List Nat := [1, 2, 3, 5, 1, 2, 1, 2, 2, 3]
def baseStart_3959201 : Nat := 118140960795 + 3959201 * 2 ^ 59
def prefixEnd_3959201 : Nat := 4983230072969 + 3 ^ 40 * 3959201 * 2
def baseEnd_3959201 : Nat := 1355315413841112894386315

theorem tailTrace_3959201 : CollatzResearch.WordTrace tailWord_3959201 prefixEnd_3959201 1355315413841112894386315 := by
  unfold tailWord_3959201
  simp only [CollatzResearch.WordTrace]
  refine ⟨144403923729498429542653457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96269282486332286361768971 144403923729498429542653457)
  ·
    refine ⟨108302942797123822156990093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144403923729498429542653457 108302942797123822156990093)
    ·
      refine ⟨40613603548921433308871285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 108302942797123822156990093 40613603548921433308871285)
      ·
        refine ⟨3807525332711384372706683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 40613603548921433308871285 3807525332711384372706683)
        ·
          refine ⟨5711287999067076559060025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3807525332711384372706683 5711287999067076559060025)
          ·
            refine ⟨4283465999300307419295019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5711287999067076559060025 4283465999300307419295019)
            ·
              refine ⟨6425198998950461128942529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4283465999300307419295019 6425198998950461128942529)
              ·
                refine ⟨4818899249212845846706897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6425198998950461128942529 4818899249212845846706897)
                ·
                  refine ⟨3614174436909634385030173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4818899249212845846706897 3614174436909634385030173)
                  ·
                    refine ⟨1355315413841112894386315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3614174436909634385030173 1355315413841112894386315)
                    ·
                      rfl

theorem cell22_3959201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 2, 1, 2, 2, 3].length) (baseStart_3959201 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3959201 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3959201 prefixEnd_3959201 := by exact prefixLift 3959201
  have htrace : WordTrace (prefixWord ++ tailWord_3959201) baseStart_3959201 baseEnd_3959201 := by
    simpa [prefixWord, tailWord_3959201, baseEnd_3959201] using wordTrace_append hprefix tailTrace_3959201
  have hstable : (prefixWord ++ tailWord_3959201).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3959201).length < 2 ^ (prefixWord ++ tailWord_3959201).sum := by decide
  have hdescent : baseEnd_3959201 < baseStart_3959201 := by decide
  rcases family_descends (prefixWord ++ tailWord_3959201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3959330 : List Nat := [3, 3, 1, 1, 1, 1, 1, 2, 2, 7]
def baseStart_3959330 : Nat := 118140960795 + 3959330 * 2 ^ 59
def prefixEnd_3959330 : Nat := 4983230072969 + 3 ^ 40 * 3959330 * 2
def baseEnd_3959330 : Nat := 1355359573177399557910919

theorem tailTrace_3959330 : CollatzResearch.WordTrace tailWord_3959330 prefixEnd_3959330 1355359573177399557910919 := by
  unfold tailWord_3959330
  simp only [CollatzResearch.WordTrace]
  refine ⟨36102157186507771143524861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96272419164020723049399629 36102157186507771143524861)
  ·
    refine ⟨13538308944940414178821823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36102157186507771143524861 13538308944940414178821823)
    ·
      refine ⟨20307463417410621268232735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13538308944940414178821823 20307463417410621268232735)
      ·
        refine ⟨30461195126115931902349103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20307463417410621268232735 30461195126115931902349103)
        ·
          refine ⟨45691792689173897853523655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30461195126115931902349103 45691792689173897853523655)
          ·
            refine ⟨68537689033760846780285483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45691792689173897853523655 68537689033760846780285483)
            ·
              refine ⟨102806533550641270170428225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68537689033760846780285483 102806533550641270170428225)
              ·
                refine ⟨77104900162980952627821169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 102806533550641270170428225 77104900162980952627821169)
                ·
                  refine ⟨57828675122235714470865877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 77104900162980952627821169 57828675122235714470865877)
                  ·
                    refine ⟨1355359573177399557910919, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 57828675122235714470865877 1355359573177399557910919)
                    ·
                      rfl

theorem cell22_3959330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 2, 2, 7].length) (baseStart_3959330 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3959330 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3959330 prefixEnd_3959330 := by exact prefixLift 3959330
  have htrace : WordTrace (prefixWord ++ tailWord_3959330) baseStart_3959330 baseEnd_3959330 := by
    simpa [prefixWord, tailWord_3959330, baseEnd_3959330] using wordTrace_append hprefix tailTrace_3959330
  have hstable : (prefixWord ++ tailWord_3959330).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3959330).length < 2 ^ (prefixWord ++ tailWord_3959330).sum := by decide
  have hdescent : baseEnd_3959330 < baseStart_3959330 := by decide
  rcases family_descends (prefixWord ++ tailWord_3959330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3959347 : List Nat := [1, 1, 1, 2, 4, 2, 3, 2, 3, 3]
def baseStart_3959347 : Nat := 118140960795 + 3959347 * 2 ^ 59
def prefixEnd_3959347 : Nat := 4983230072969 + 3 ^ 40 * 3959347 * 2
def baseEnd_3959347 : Nat := 1355365392624817180235867

theorem tailTrace_3959347 : CollatzResearch.WordTrace tailWord_3959347 prefixEnd_3959347 1355365392624817180235867 := by
  unfold tailWord_3959347
  simp only [CollatzResearch.WordTrace]
  refine ⟨144409248786969496477468295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96272832524646330984978863 144409248786969496477468295)
  ·
    refine ⟨216613873180454244716202443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144409248786969496477468295 216613873180454244716202443)
    ·
      refine ⟨324920809770681367074303665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216613873180454244716202443 324920809770681367074303665)
      ·
        refine ⟨243690607328011025305727749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 324920809770681367074303665 243690607328011025305727749)
        ·
          refine ⟨45691988874002067244823953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 243690607328011025305727749 45691988874002067244823953)
          ·
            refine ⟨34268991655501550433617965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45691988874002067244823953 34268991655501550433617965)
            ·
              refine ⟨12850871870813081412606737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34268991655501550433617965 12850871870813081412606737)
              ·
                refine ⟨9638153903109811059455053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12850871870813081412606737 9638153903109811059455053)
                ·
                  refine ⟨3614307713666179147295645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9638153903109811059455053 3614307713666179147295645)
                  ·
                    refine ⟨1355365392624817180235867, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3614307713666179147295645 1355365392624817180235867)
                    ·
                      rfl

theorem cell22_3959347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 3, 2, 3, 3].length) (baseStart_3959347 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3959347 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3959347 prefixEnd_3959347 := by exact prefixLift 3959347
  have htrace : WordTrace (prefixWord ++ tailWord_3959347) baseStart_3959347 baseEnd_3959347 := by
    simpa [prefixWord, tailWord_3959347, baseEnd_3959347] using wordTrace_append hprefix tailTrace_3959347
  have hstable : (prefixWord ++ tailWord_3959347).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3959347).length < 2 ^ (prefixWord ++ tailWord_3959347).sum := by decide
  have hdescent : baseEnd_3959347 < baseStart_3959347 := by decide
  rcases family_descends (prefixWord ++ tailWord_3959347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3959375 : List Nat := [1, 1, 2, 1, 1, 2, 5, 2, 2, 5]
def baseStart_3959375 : Nat := 118140960795 + 3959375 * 2 ^ 59
def prefixEnd_3959375 : Nat := 4983230072969 + 3 ^ 40 * 3959375 * 2
def baseEnd_3959375 : Nat := 1355374977597034440535781

theorem tailTrace_3959375 : CollatzResearch.WordTrace tailWord_3959375 prefixEnd_3959375 1355374977597034440535781 := by
  unfold tailWord_3959375
  simp only [CollatzResearch.WordTrace]
  refine ⟨144410270030868057259487579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96273513353912038172991719 144410270030868057259487579)
  ·
    refine ⟨216615405046302085889231369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144410270030868057259487579 216615405046302085889231369)
    ·
      refine ⟨162461553784726564416923527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 216615405046302085889231369 162461553784726564416923527)
      ·
        refine ⟨243692330677089846625385291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162461553784726564416923527 243692330677089846625385291)
        ·
          refine ⟨365538496015634769938077937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 243692330677089846625385291 365538496015634769938077937)
          ·
            refine ⟨274153872011726077453558453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 365538496015634769938077937 274153872011726077453558453)
            ·
              refine ⟨25701925501099319761271105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 274153872011726077453558453 25701925501099319761271105)
              ·
                refine ⟨19276444125824489820953329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25701925501099319761271105 19276444125824489820953329)
                ·
                  refine ⟨14457333094368367365714997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19276444125824489820953329 14457333094368367365714997)
                  ·
                    refine ⟨1355374977597034440535781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14457333094368367365714997 1355374977597034440535781)
                    ·
                      rfl

theorem cell22_3959375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 5, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 5, 2, 2, 5].length) (baseStart_3959375 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3959375 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3959375 prefixEnd_3959375 := by exact prefixLift 3959375
  have htrace : WordTrace (prefixWord ++ tailWord_3959375) baseStart_3959375 baseEnd_3959375 := by
    simpa [prefixWord, tailWord_3959375, baseEnd_3959375] using wordTrace_append hprefix tailTrace_3959375
  have hstable : (prefixWord ++ tailWord_3959375).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3959375).length < 2 ^ (prefixWord ++ tailWord_3959375).sum := by decide
  have hdescent : baseEnd_3959375 < baseStart_3959375 := by decide
  rcases family_descends (prefixWord ++ tailWord_3959375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3959377 : List Nat := [1, 2, 2, 1, 3, 3, 3, 2, 5]
def baseStart_3959377 : Nat := 118140960795 + 3959377 * 2 ^ 59
def prefixEnd_3959377 : Nat := 4983230072969 + 3 ^ 40 * 3959377 * 2
def baseEnd_3959377 : Nat := 451791887412635700661925

theorem tailTrace_3959377 : CollatzResearch.WordTrace tailWord_3959377 prefixEnd_3959377 451791887412635700661925 := by
  unfold tailWord_3959377
  simp only [CollatzResearch.WordTrace]
  refine ⟨144410342976860811601060385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96273561984573874400706923 144410342976860811601060385)
  ·
    refine ⟨108307757232645608700795289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144410342976860811601060385 108307757232645608700795289)
    ·
      refine ⟨81230817924484206525596467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108307757232645608700795289 81230817924484206525596467)
      ·
        refine ⟨121846226886726309788394701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81230817924484206525596467 121846226886726309788394701)
        ·
          refine ⟨45692335082522366170648013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 121846226886726309788394701 45692335082522366170648013)
          ·
            refine ⟨17134625655945887313993005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45692335082522366170648013 17134625655945887313993005)
            ·
              refine ⟨6425484620979707742747377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17134625655945887313993005 6425484620979707742747377)
              ·
                refine ⟨4819113465734780807060533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6425484620979707742747377 4819113465734780807060533)
                ·
                  refine ⟨451791887412635700661925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4819113465734780807060533 451791887412635700661925)
                  ·
                    rfl

theorem cell22_3959377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 3, 2, 5].length) (baseStart_3959377 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3959377 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3959377 prefixEnd_3959377 := by exact prefixLift 3959377
  have htrace : WordTrace (prefixWord ++ tailWord_3959377) baseStart_3959377 baseEnd_3959377 := by
    simpa [prefixWord, tailWord_3959377, baseEnd_3959377] using wordTrace_append hprefix tailTrace_3959377
  have hstable : (prefixWord ++ tailWord_3959377).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3959377).length < 2 ^ (prefixWord ++ tailWord_3959377).sum := by decide
  have hdescent : baseEnd_3959377 < baseStart_3959377 := by decide
  rcases family_descends (prefixWord ++ tailWord_3959377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3959407 : List Nat := [1, 1, 2, 1, 3, 2, 3, 4, 1, 4]
def baseStart_3959407 : Nat := 118140960795 + 3959407 * 2 ^ 59
def prefixEnd_3959407 : Nat := 4983230072969 + 3 ^ 40 * 3959407 * 2
def baseEnd_3959407 : Nat := 1355385931850997023735683

theorem tailTrace_3959407 : CollatzResearch.WordTrace tailWord_3959407 prefixEnd_3959407 1355385931850997023735683 := by
  unfold tailWord_3959407
  simp only [CollatzResearch.WordTrace]
  refine ⟨144411437166752126724652475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96274291444501417816434983 144411437166752126724652475)
  ·
    refine ⟨216617155750128190086978713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144411437166752126724652475 216617155750128190086978713)
    ·
      refine ⟨162462866812596142565234035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 216617155750128190086978713 162462866812596142565234035)
      ·
        refine ⟨243694300218894213847851053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162462866812596142565234035 243694300218894213847851053)
        ·
          refine ⟨91385362582085330192944145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 243694300218894213847851053 91385362582085330192944145)
          ·
            refine ⟨68539021936563997644708109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91385362582085330192944145 68539021936563997644708109)
            ·
              refine ⟨25702133226211499116765541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68539021936563997644708109 25702133226211499116765541)
              ·
                refine ⟨4819149979914656084393539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25702133226211499116765541 4819149979914656084393539)
                ·
                  refine ⟨7228724969871984126590309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4819149979914656084393539 7228724969871984126590309)
                  ·
                    refine ⟨1355385931850997023735683, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7228724969871984126590309 1355385931850997023735683)
                    ·
                      rfl

theorem cell22_3959407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 3, 4, 1, 4].length) (baseStart_3959407 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3959407 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3959407 prefixEnd_3959407 := by exact prefixLift 3959407
  have htrace : WordTrace (prefixWord ++ tailWord_3959407) baseStart_3959407 baseEnd_3959407 := by
    simpa [prefixWord, tailWord_3959407, baseEnd_3959407] using wordTrace_append hprefix tailTrace_3959407
  have hstable : (prefixWord ++ tailWord_3959407).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3959407).length < 2 ^ (prefixWord ++ tailWord_3959407).sum := by decide
  have hdescent : baseEnd_3959407 < baseStart_3959407 := by decide
  rcases family_descends (prefixWord ++ tailWord_3959407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3959435 : List Nat := [1, 1, 1, 1, 4, 1, 2, 2, 3, 6]
def baseStart_3959435 : Nat := 118140960795 + 3959435 * 2 ^ 59
def prefixEnd_3959435 : Nat := 4983230072969 + 3 ^ 40 * 3959435 * 2
def baseEnd_3959435 : Nat := 1355395516823214284035597

theorem tailTrace_3959435 : CollatzResearch.WordTrace tailWord_3959435 prefixEnd_3959435 1355395516823214284035597 := by
  unfold tailWord_3959435
  simp only [CollatzResearch.WordTrace]
  refine ⟨144412458410650687506671759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96274972273767125004447839 144412458410650687506671759)
  ·
    refine ⟨216618687615976031260007639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144412458410650687506671759 216618687615976031260007639)
    ·
      refine ⟨324928031423964046890011459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216618687615976031260007639 324928031423964046890011459)
      ·
        refine ⟨487392047135946070335017189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 324928031423964046890011459 487392047135946070335017189)
        ·
          refine ⟨91386008837989888187815723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 487392047135946070335017189 91386008837989888187815723)
          ·
            refine ⟨137079013256984832281723585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91386008837989888187815723 137079013256984832281723585)
            ·
              refine ⟨102809259942738624211292689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 137079013256984832281723585 102809259942738624211292689)
              ·
                refine ⟨77106944957053968158469517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 102809259942738624211292689 77106944957053968158469517)
                ·
                  refine ⟨28915104358895238059426069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 77106944957053968158469517 28915104358895238059426069)
                  ·
                    refine ⟨1355395516823214284035597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28915104358895238059426069 1355395516823214284035597)
                    ·
                      rfl

theorem cell22_3959435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 2, 3, 6].length) (baseStart_3959435 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3959435 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3959435 prefixEnd_3959435 := by exact prefixLift 3959435
  have htrace : WordTrace (prefixWord ++ tailWord_3959435) baseStart_3959435 baseEnd_3959435 := by
    simpa [prefixWord, tailWord_3959435, baseEnd_3959435] using wordTrace_append hprefix tailTrace_3959435
  have hstable : (prefixWord ++ tailWord_3959435).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3959435).length < 2 ^ (prefixWord ++ tailWord_3959435).sum := by decide
  have hdescent : baseEnd_3959435 < baseStart_3959435 := by decide
  rcases family_descends (prefixWord ++ tailWord_3959435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3959454 : List Nat := [4, 3, 1, 1, 1, 1, 2, 3, 1, 5]
def baseStart_3959454 : Nat := 118140960795 + 3959454 * 2 ^ 59
def prefixEnd_3959454 : Nat := 4983230072969 + 3 ^ 40 * 3959454 * 2
def baseEnd_3959454 : Nat := 1355402020911504567810539

theorem tailTrace_3959454 : CollatzResearch.WordTrace tailWord_3959454 prefixEnd_3959454 1355402020911504567810539 := by
  unfold tailWord_3959454
  simp only [CollatzResearch.WordTrace]
  refine ⟨18051643924697731718951677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 96275434265054569167742277 18051643924697731718951677)
  ·
    refine ⟨6769366471761649394606879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18051643924697731718951677 6769366471761649394606879)
    ·
      refine ⟨10154049707642474091910319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6769366471761649394606879 10154049707642474091910319)
      ·
        refine ⟨15231074561463711137865479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10154049707642474091910319 15231074561463711137865479)
        ·
          refine ⟨22846611842195566706798219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15231074561463711137865479 22846611842195566706798219)
          ·
            refine ⟨34269917763293350060197329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22846611842195566706798219 34269917763293350060197329)
            ·
              refine ⟨25702438322470012545147997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34269917763293350060197329 25702438322470012545147997)
              ·
                refine ⟨9638414370926254704430499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25702438322470012545147997 9638414370926254704430499)
                ·
                  refine ⟨14457621556389382056645749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9638414370926254704430499 14457621556389382056645749)
                  ·
                    refine ⟨1355402020911504567810539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14457621556389382056645749 1355402020911504567810539)
                    ·
                      rfl

theorem cell22_3959454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 2, 3, 1, 5].length) (baseStart_3959454 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3959454 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3959454 prefixEnd_3959454 := by exact prefixLift 3959454
  have htrace : WordTrace (prefixWord ++ tailWord_3959454) baseStart_3959454 baseEnd_3959454 := by
    simpa [prefixWord, tailWord_3959454, baseEnd_3959454] using wordTrace_append hprefix tailTrace_3959454
  have hstable : (prefixWord ++ tailWord_3959454).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3959454).length < 2 ^ (prefixWord ++ tailWord_3959454).sum := by decide
  have hdescent : baseEnd_3959454 < baseStart_3959454 := by decide
  rcases family_descends (prefixWord ++ tailWord_3959454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3959465 : List Nat := [1, 2, 1, 1, 1, 1, 2, 3, 1, 9]
def baseStart_3959465 : Nat := 118140960795 + 3959465 * 2 ^ 59
def prefixEnd_3959465 : Nat := 4983230072969 + 3 ^ 40 * 3959465 * 2
def baseEnd_3959465 : Nat := 1355405786436304205785505

theorem tailTrace_3959465 : CollatzResearch.WordTrace tailWord_3959465 prefixEnd_3959465 1355405786436304205785505 := by
  unfold tailWord_3959465
  simp only [CollatzResearch.WordTrace]
  refine ⟨144413552600542002630263849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96275701733694668420175899 144413552600542002630263849)
  ·
    refine ⟨108310164450406501972697887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144413552600542002630263849 108310164450406501972697887)
    ·
      refine ⟨162465246675609752959046831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108310164450406501972697887 162465246675609752959046831)
      ·
        refine ⟨243697870013414629438570247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162465246675609752959046831 243697870013414629438570247)
        ·
          refine ⟨365546805020121944157855371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 243697870013414629438570247 365546805020121944157855371)
          ·
            refine ⟨548320207530182916236783057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 365546805020121944157855371 548320207530182916236783057)
            ·
              refine ⟨411240155647637187177587293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 548320207530182916236783057 411240155647637187177587293)
              ·
                refine ⟨154215058367863945191595235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 411240155647637187177587293 154215058367863945191595235)
                ·
                  refine ⟨231322587551795917787392853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 154215058367863945191595235 231322587551795917787392853)
                  ·
                    refine ⟨1355405786436304205785505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 231322587551795917787392853 1355405786436304205785505)
                    ·
                      rfl

theorem cell22_3959465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 3, 1, 9].length) (baseStart_3959465 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3959465 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3959465 prefixEnd_3959465 := by exact prefixLift 3959465
  have htrace : WordTrace (prefixWord ++ tailWord_3959465) baseStart_3959465 baseEnd_3959465 := by
    simpa [prefixWord, tailWord_3959465, baseEnd_3959465] using wordTrace_append hprefix tailTrace_3959465
  have hstable : (prefixWord ++ tailWord_3959465).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3959465).length < 2 ^ (prefixWord ++ tailWord_3959465).sum := by decide
  have hdescent : baseEnd_3959465 < baseStart_3959465 := by decide
  rcases family_descends (prefixWord ++ tailWord_3959465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3959469 : List Nat := [1, 5, 2, 1, 1, 2, 1, 3, 2, 4]
def baseStart_3959469 : Nat := 118140960795 + 3959469 * 2 ^ 59
def prefixEnd_3959469 : Nat := 4983230072969 + 3 ^ 40 * 3959469 * 2
def baseEnd_3959469 : Nat := 1355407155718049528685493

theorem tailTrace_3959469 : CollatzResearch.WordTrace tailWord_3959469 prefixEnd_3959469 1355407155718049528685493 := by
  unfold tailWord_3959469
  simp only [CollatzResearch.WordTrace]
  refine ⟨144413698492527511313409461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96275798995018340875606307 144413698492527511313409461)
  ·
    refine ⟨13538784233674454185632137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 144413698492527511313409461 13538784233674454185632137)
    ·
      refine ⟨10154088175255840639224103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13538784233674454185632137 10154088175255840639224103)
      ·
        refine ⟨15231132262883760958836155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10154088175255840639224103 15231132262883760958836155)
        ·
          refine ⟨22846698394325641438254233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15231132262883760958836155 22846698394325641438254233)
          ·
            refine ⟨17135023795744231078690675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22846698394325641438254233 17135023795744231078690675)
            ·
              refine ⟨25702535693616346618036013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17135023795744231078690675 25702535693616346618036013)
              ·
                refine ⟨9638450885106129981763505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25702535693616346618036013 9638450885106129981763505)
                ·
                  refine ⟨7228838163829597486322629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9638450885106129981763505 7228838163829597486322629)
                  ·
                    refine ⟨1355407155718049528685493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7228838163829597486322629 1355407155718049528685493)
                    ·
                      rfl

theorem cell22_3959469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 1, 3, 2, 4].length) (baseStart_3959469 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3959469 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3959469 prefixEnd_3959469 := by exact prefixLift 3959469
  have htrace : WordTrace (prefixWord ++ tailWord_3959469) baseStart_3959469 baseEnd_3959469 := by
    simpa [prefixWord, tailWord_3959469, baseEnd_3959469] using wordTrace_append hprefix tailTrace_3959469
  have hstable : (prefixWord ++ tailWord_3959469).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3959469).length < 2 ^ (prefixWord ++ tailWord_3959469).sum := by decide
  have hdescent : baseEnd_3959469 < baseStart_3959469 := by decide
  rcases family_descends (prefixWord ++ tailWord_3959469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3959516 : List Nat := [2, 2, 5, 1, 1, 1, 1, 1, 5, 3]
def baseStart_3959516 : Nat := 118140960795 + 3959516 * 2 ^ 59
def prefixEnd_3959516 : Nat := 4983230072969 + 3 ^ 40 * 3959516 * 2
def baseEnd_3959516 : Nat := 1355423244778557072760349

theorem tailTrace_3959516 : CollatzResearch.WordTrace tailWord_3959516 prefixEnd_3959516 1355423244778557072760349 := by
  unfold tailWord_3959516
  simp only [CollatzResearch.WordTrace]
  refine ⟨72207706361678619170185201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96276941815571492226913601 72207706361678619170185201)
  ·
    refine ⟨54155779771258964377638901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72207706361678619170185201 54155779771258964377638901)
    ·
      refine ⟨5077104353555527910403647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 54155779771258964377638901 5077104353555527910403647)
      ·
        refine ⟨7615656530333291865605471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5077104353555527910403647 7615656530333291865605471)
        ·
          refine ⟨11423484795499937798408207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7615656530333291865605471 11423484795499937798408207)
          ·
            refine ⟨17135227193249906697612311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11423484795499937798408207 17135227193249906697612311)
            ·
              refine ⟨25702840789874860046418467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17135227193249906697612311 25702840789874860046418467)
              ·
                refine ⟨38554261184812290069627701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25702840789874860046418467 38554261184812290069627701)
                ·
                  refine ⟨3614461986076152194027597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 38554261184812290069627701 3614461986076152194027597)
                  ·
                    refine ⟨1355423244778557072760349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3614461986076152194027597 1355423244778557072760349)
                    ·
                      rfl

theorem cell22_3959516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 1, 1, 5, 3].length) (baseStart_3959516 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3959516 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3959516 prefixEnd_3959516 := by exact prefixLift 3959516
  have htrace : WordTrace (prefixWord ++ tailWord_3959516) baseStart_3959516 baseEnd_3959516 := by
    simpa [prefixWord, tailWord_3959516, baseEnd_3959516] using wordTrace_append hprefix tailTrace_3959516
  have hstable : (prefixWord ++ tailWord_3959516).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3959516).length < 2 ^ (prefixWord ++ tailWord_3959516).sum := by decide
  have hdescent : baseEnd_3959516 < baseStart_3959516 := by decide
  rcases family_descends (prefixWord ++ tailWord_3959516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3959533 : List Nat := [1, 5, 1, 2, 1, 1, 4, 3, 1, 3]
def baseStart_3959533 : Nat := 118140960795 + 3959533 * 2 ^ 59
def prefixEnd_3959533 : Nat := 4983230072969 + 3 ^ 40 * 3959533 * 2
def baseEnd_3959533 : Nat := 1355429064225974695085297

theorem tailTrace_3959533 : CollatzResearch.WordTrace tailWord_3959533 prefixEnd_3959533 1355429064225974695085297 := by
  unfold tailWord_3959533
  simp only [CollatzResearch.WordTrace]
  refine ⟨144416032764295650243739253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96277355176197100162492835 144416032764295650243739253)
  ·
    refine ⟨13539003071652717210350555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 144416032764295650243739253 13539003071652717210350555)
    ·
      refine ⟨20308504607479075815525833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13539003071652717210350555 20308504607479075815525833)
      ·
        refine ⟨15231378455609306861644375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20308504607479075815525833 15231378455609306861644375)
        ·
          refine ⟨22847067683413960292466563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15231378455609306861644375 22847067683413960292466563)
          ·
            refine ⟨34270601525120940438699845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22847067683413960292466563 34270601525120940438699845)
            ·
              refine ⟨6425737785960176332256221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34270601525120940438699845 6425737785960176332256221)
              ·
                refine ⟨2409651669735066124596083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6425737785960176332256221 2409651669735066124596083)
                ·
                  refine ⟨3614477504602599186894125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2409651669735066124596083 3614477504602599186894125)
                  ·
                    refine ⟨1355429064225974695085297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3614477504602599186894125 1355429064225974695085297)
                    ·
                      rfl

theorem cell22_3959533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 4, 3, 1, 3].length) (baseStart_3959533 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3959533 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3959533 prefixEnd_3959533 := by exact prefixLift 3959533
  have htrace : WordTrace (prefixWord ++ tailWord_3959533) baseStart_3959533 baseEnd_3959533 := by
    simpa [prefixWord, tailWord_3959533, baseEnd_3959533] using wordTrace_append hprefix tailTrace_3959533
  have hstable : (prefixWord ++ tailWord_3959533).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3959533).length < 2 ^ (prefixWord ++ tailWord_3959533).sum := by decide
  have hdescent : baseEnd_3959533 < baseStart_3959533 := by decide
  rcases family_descends (prefixWord ++ tailWord_3959533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3959589 : List Nat := [1, 3, 1, 2, 3, 1, 1, 1, 6, 3]
def baseStart_3959589 : Nat := 118140960795 + 3959589 * 2 ^ 59
def prefixEnd_3959589 : Nat := 4983230072969 + 3 ^ 40 * 3959589 * 2
def baseEnd_3959589 : Nat := 1355448234170409215685125

theorem tailTrace_3959589 : CollatzResearch.WordTrace tailWord_3959589 prefixEnd_3959589 1355448234170409215685125 := by
  unfold tailWord_3959589
  simp only [CollatzResearch.WordTrace]
  refine ⟨144418075252092771807777821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96278716834728514538518547 144418075252092771807777821)
  ·
    refine ⟨54156778219534789427916683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 144418075252092771807777821 54156778219534789427916683)
    ·
      refine ⟨81235167329302184141875025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54156778219534789427916683 81235167329302184141875025)
      ·
        refine ⟨60926375496976638106406269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81235167329302184141875025 60926375496976638106406269)
        ·
          refine ⟨22847390811366239289902351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60926375496976638106406269 22847390811366239289902351)
          ·
            refine ⟨34271086217049358934853527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22847390811366239289902351 34271086217049358934853527)
            ·
              refine ⟨51406629325574038402280291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34271086217049358934853527 51406629325574038402280291)
              ·
                refine ⟨77109943988361057603420437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51406629325574038402280291 77109943988361057603420437)
                ·
                  refine ⟨3614528624454424575160333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 77109943988361057603420437 3614528624454424575160333)
                  ·
                    refine ⟨1355448234170409215685125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3614528624454424575160333 1355448234170409215685125)
                    ·
                      rfl

theorem cell22_3959589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 1, 6, 3].length) (baseStart_3959589 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3959589 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3959589 prefixEnd_3959589 := by exact prefixLift 3959589
  have htrace : WordTrace (prefixWord ++ tailWord_3959589) baseStart_3959589 baseEnd_3959589 := by
    simpa [prefixWord, tailWord_3959589, baseEnd_3959589] using wordTrace_append hprefix tailTrace_3959589
  have hstable : (prefixWord ++ tailWord_3959589).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3959589).length < 2 ^ (prefixWord ++ tailWord_3959589).sum := by decide
  have hdescent : baseEnd_3959589 < baseStart_3959589 := by decide
  rcases family_descends (prefixWord ++ tailWord_3959589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3959664 : List Nat := [2, 1, 1, 1, 4, 1, 3, 4, 5]
def baseStart_3959664 : Nat := 118140960795 + 3959664 * 2 ^ 59
def prefixEnd_3959664 : Nat := 4983230072969 + 3 ^ 40 * 3959664 * 2
def baseEnd_3959664 : Nat := 451824636067711340019965

theorem tailTrace_3959664 : CollatzResearch.WordTrace tailWord_3959664 prefixEnd_3959664 451824636067711340019965 := by
  unfold tailWord_3959664
  simp only [CollatzResearch.WordTrace]
  refine ⟨72210405363410529808379023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96280540484547373077838697 72210405363410529808379023)
  ·
    refine ⟨108315608045115794712568535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72210405363410529808379023 108315608045115794712568535)
    ·
      refine ⟨162473412067673692068852803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108315608045115794712568535 162473412067673692068852803)
      ·
        refine ⟨243710118101510538103279205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162473412067673692068852803 243710118101510538103279205)
        ·
          refine ⟨45695647144033225894364851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 243710118101510538103279205 45695647144033225894364851)
          ·
            refine ⟨68543470716049838841547277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45695647144033225894364851 68543470716049838841547277)
            ·
              refine ⟨25703801518518689565580229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68543470716049838841547277 25703801518518689565580229)
              ·
                refine ⟨4819462784722254293546293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25703801518518689565580229 4819462784722254293546293)
                ·
                  refine ⟨451824636067711340019965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4819462784722254293546293 451824636067711340019965)
                  ·
                    rfl

theorem cell22_3959664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 3, 4, 5].length) (baseStart_3959664 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3959664 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3959664 prefixEnd_3959664 := by exact prefixLift 3959664
  have htrace : WordTrace (prefixWord ++ tailWord_3959664) baseStart_3959664 baseEnd_3959664 := by
    simpa [prefixWord, tailWord_3959664, baseEnd_3959664] using wordTrace_append hprefix tailTrace_3959664
  have hstable : (prefixWord ++ tailWord_3959664).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3959664).length < 2 ^ (prefixWord ++ tailWord_3959664).sum := by decide
  have hdescent : baseEnd_3959664 < baseStart_3959664 := by decide
  rcases family_descends (prefixWord ++ tailWord_3959664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3959709 : List Nat := [1, 4, 2, 1, 2, 1, 1, 2, 8]
def baseStart_3959709 : Nat := 118140960795 + 3959709 * 2 ^ 59
def prefixEnd_3959709 : Nat := 4983230072969 + 3 ^ 40 * 3959709 * 2
def baseEnd_3959709 : Nat := 451829770874256300894919

theorem tailTrace_3959709 : CollatzResearch.WordTrace tailWord_3959709 prefixEnd_3959709 451829770874256300894919 := by
  unfold tailWord_3959709
  simp only [CollatzResearch.WordTrace]
  refine ⟨144422452011658032302146181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96281634674438688201430787 144422452011658032302146181)
  ·
    refine ⟨27079209752185881056652409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 144422452011658032302146181 27079209752185881056652409)
    ·
      refine ⟨20309407314139410792489307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27079209752185881056652409 20309407314139410792489307)
      ·
        refine ⟨30464110971209116188733961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20309407314139410792489307 30464110971209116188733961)
        ·
          refine ⟨22848083228406837141550471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30464110971209116188733961 22848083228406837141550471)
          ·
            refine ⟨34272124842610255712325707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22848083228406837141550471 34272124842610255712325707)
            ·
              refine ⟨51408187263915383568488561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34272124842610255712325707 51408187263915383568488561)
              ·
                refine ⟨38556140447936537676366421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51408187263915383568488561 38556140447936537676366421)
                ·
                  refine ⟨451829770874256300894919, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 38556140447936537676366421 451829770874256300894919)
                  ·
                    rfl

theorem cell22_3959709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 2, 8].length) (baseStart_3959709 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3959709 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3959709 prefixEnd_3959709 := by exact prefixLift 3959709
  have htrace : WordTrace (prefixWord ++ tailWord_3959709) baseStart_3959709 baseEnd_3959709 := by
    simpa [prefixWord, tailWord_3959709, baseEnd_3959709] using wordTrace_append hprefix tailTrace_3959709
  have hstable : (prefixWord ++ tailWord_3959709).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3959709).length < 2 ^ (prefixWord ++ tailWord_3959709).sum := by decide
  have hdescent : baseEnd_3959709 < baseStart_3959709 := by decide
  rcases family_descends (prefixWord ++ tailWord_3959709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3959756 : List Nat := [2, 2, 1, 4, 1, 1, 2, 3, 2, 4]
def baseStart_3959756 : Nat := 118140960795 + 3959756 * 2 ^ 59
def prefixEnd_3959756 : Nat := 4983230072969 + 3 ^ 40 * 3959756 * 2
def baseEnd_3959756 : Nat := 1355505401683276446759613

theorem tailTrace_3959756 : CollatzResearch.WordTrace tailWord_3959756 prefixEnd_3959756 1355505401683276446759613 := by
  unfold tailWord_3959756
  simp only [CollatzResearch.WordTrace]
  refine ⟨72212083121243879664553561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96282777494991839552738081 72212083121243879664553561)
  ·
    refine ⟨54159062340932909748415171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72212083121243879664553561 54159062340932909748415171)
    ·
      refine ⟨81238593511399364622622757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54159062340932909748415171 81238593511399364622622757)
      ·
        refine ⟨15232236283387380866741767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 81238593511399364622622757 15232236283387380866741767)
        ·
          refine ⟨22848354425081071300112651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15232236283387380866741767 22848354425081071300112651)
          ·
            refine ⟨34272531637621606950168977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22848354425081071300112651 34272531637621606950168977)
            ·
              refine ⟨25704398728216205212626733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34272531637621606950168977 25704398728216205212626733)
              ·
                refine ⟨9639149523081076954735025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25704398728216205212626733 9639149523081076954735025)
                ·
                  refine ⟨7229362142310807716051269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9639149523081076954735025 7229362142310807716051269)
                  ·
                    refine ⟨1355505401683276446759613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7229362142310807716051269 1355505401683276446759613)
                    ·
                      rfl

theorem cell22_3959756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 2, 3, 2, 4].length) (baseStart_3959756 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3959756 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3959756 prefixEnd_3959756 := by exact prefixLift 3959756
  have htrace : WordTrace (prefixWord ++ tailWord_3959756) baseStart_3959756 baseEnd_3959756 := by
    simpa [prefixWord, tailWord_3959756, baseEnd_3959756] using wordTrace_append hprefix tailTrace_3959756
  have hstable : (prefixWord ++ tailWord_3959756).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3959756).length < 2 ^ (prefixWord ++ tailWord_3959756).sum := by decide
  have hdescent : baseEnd_3959756 < baseStart_3959756 := by decide
  rcases family_descends (prefixWord ++ tailWord_3959756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3959773 : List Nat := [1, 4, 3, 1, 2, 2, 1, 2, 2, 4]
def baseStart_3959773 : Nat := 118140960795 + 3959773 * 2 ^ 59
def prefixEnd_3959773 : Nat := 4983230072969 + 3 ^ 40 * 3959773 * 2
def baseEnd_3959773 : Nat := 1355511221130694069084561

theorem tailTrace_3959773 : CollatzResearch.WordTrace tailWord_3959773 prefixEnd_3959773 1355511221130694069084561 := by
  unfold tailWord_3959773
  simp only [CollatzResearch.WordTrace]
  refine ⟨144424786283426171232475973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96283190855617447488317315 144424786283426171232475973)
  ·
    refine ⟨27079647428142407106089245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 144424786283426171232475973 27079647428142407106089245)
    ·
      refine ⟨10154867785553402664783467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27079647428142407106089245 10154867785553402664783467)
      ·
        refine ⟨15232301678330103997175201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10154867785553402664783467 15232301678330103997175201)
        ·
          refine ⟨11424226258747577997881401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15232301678330103997175201 11424226258747577997881401)
          ·
            refine ⟨8568169694060683498411051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11424226258747577997881401 8568169694060683498411051)
            ·
              refine ⟨12852254541091025247616577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8568169694060683498411051 12852254541091025247616577)
              ·
                refine ⟨9639190905818268935712433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12852254541091025247616577 9639190905818268935712433)
                ·
                  refine ⟨7229393179363701701784325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9639190905818268935712433 7229393179363701701784325)
                  ·
                    refine ⟨1355511221130694069084561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7229393179363701701784325 1355511221130694069084561)
                    ·
                      rfl

theorem cell22_3959773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 1, 2, 2, 4].length) (baseStart_3959773 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3959773 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3959773 prefixEnd_3959773 := by exact prefixLift 3959773
  have htrace : WordTrace (prefixWord ++ tailWord_3959773) baseStart_3959773 baseEnd_3959773 := by
    simpa [prefixWord, tailWord_3959773, baseEnd_3959773] using wordTrace_append hprefix tailTrace_3959773
  have hstable : (prefixWord ++ tailWord_3959773).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3959773).length < 2 ^ (prefixWord ++ tailWord_3959773).sum := by decide
  have hdescent : baseEnd_3959773 < baseStart_3959773 := by decide
  rcases family_descends (prefixWord ++ tailWord_3959773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3959796 : List Nat := [2, 6, 2, 1, 1, 2, 1, 2, 1, 4]
def baseStart_3959796 : Nat := 118140960795 + 3959796 * 2 ^ 59
def prefixEnd_3959796 : Nat := 4983230072969 + 3 ^ 40 * 3959796 * 2
def baseEnd_3959796 : Nat := 1355519094500729675759491

theorem tailTrace_3959796 : CollatzResearch.WordTrace tailWord_3959796 prefixEnd_3959796 1355519094500729675759491 := by
  unfold tailWord_3959796
  simp only [CollatzResearch.WordTrace]
  refine ⟨72212812581171423080281621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96283750108228564107042161 72212812581171423080281621)
  ·
    refine ⟨3384975589742410456888201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 72212812581171423080281621 3384975589742410456888201)
    ·
      refine ⟨2538731692306807842666151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3384975589742410456888201 2538731692306807842666151)
      ·
        refine ⟨3808097538460211763999227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2538731692306807842666151 3808097538460211763999227)
        ·
          refine ⟨5712146307690317645998841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3808097538460211763999227 5712146307690317645998841)
          ·
            refine ⟨4284109730767738234499131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5712146307690317645998841 4284109730767738234499131)
            ·
              refine ⟨6426164596151607351748697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4284109730767738234499131 6426164596151607351748697)
              ·
                refine ⟨4819623447113705513811523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6426164596151607351748697 4819623447113705513811523)
                ·
                  refine ⟨7229435170670558270717285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4819623447113705513811523 7229435170670558270717285)
                  ·
                    refine ⟨1355519094500729675759491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7229435170670558270717285 1355519094500729675759491)
                    ·
                      rfl

theorem cell22_3959796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 2, 1, 2, 1, 4].length) (baseStart_3959796 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3959796 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3959796 prefixEnd_3959796 := by exact prefixLift 3959796
  have htrace : WordTrace (prefixWord ++ tailWord_3959796) baseStart_3959796 baseEnd_3959796 := by
    simpa [prefixWord, tailWord_3959796, baseEnd_3959796] using wordTrace_append hprefix tailTrace_3959796
  have hstable : (prefixWord ++ tailWord_3959796).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3959796).length < 2 ^ (prefixWord ++ tailWord_3959796).sum := by decide
  have hdescent : baseEnd_3959796 < baseStart_3959796 := by decide
  rcases family_descends (prefixWord ++ tailWord_3959796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3959837 : List Nat := [1, 4, 2, 2, 3, 1, 1, 4, 1, 3]
def baseStart_3959837 : Nat := 118140960795 + 3959837 * 2 ^ 59
def prefixEnd_3959837 : Nat := 4983230072969 + 3 ^ 40 * 3959837 * 2
def baseEnd_3959837 : Nat := 1355533129638619235484365

theorem tailTrace_3959837 : CollatzResearch.WordTrace tailWord_3959837 prefixEnd_3959837 1355533129638619235484365 := by
  unfold tailWord_3959837
  simp only [CollatzResearch.WordTrace]
  refine ⟨144427120555194310162805765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96284747036796206775203843 144427120555194310162805765)
  ·
    refine ⟨27080085104098933155526081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 144427120555194310162805765 27080085104098933155526081)
    ·
      refine ⟨20310063828074199866644561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27080085104098933155526081 20310063828074199866644561)
      ·
        refine ⟨15232547871055649899983421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20310063828074199866644561 15232547871055649899983421)
        ·
          refine ⟨5712205451645868712493783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15232547871055649899983421 5712205451645868712493783)
          ·
            refine ⟨8568308177468803068740675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5712205451645868712493783 8568308177468803068740675)
            ·
              refine ⟨12852462266203204603111013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8568308177468803068740675 12852462266203204603111013)
              ·
                refine ⟨2409836674913100863083315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12852462266203204603111013 2409836674913100863083315)
                ·
                  refine ⟨3614755012369651294624973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2409836674913100863083315 3614755012369651294624973)
                  ·
                    refine ⟨1355533129638619235484365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3614755012369651294624973 1355533129638619235484365)
                    ·
                      rfl

theorem cell22_3959837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 1, 4, 1, 3].length) (baseStart_3959837 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3959837 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3959837 prefixEnd_3959837 := by exact prefixLift 3959837
  have htrace : WordTrace (prefixWord ++ tailWord_3959837) baseStart_3959837 baseEnd_3959837 := by
    simpa [prefixWord, tailWord_3959837, baseEnd_3959837] using wordTrace_append hprefix tailTrace_3959837
  have hstable : (prefixWord ++ tailWord_3959837).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3959837).length < 2 ^ (prefixWord ++ tailWord_3959837).sum := by decide
  have hdescent : baseEnd_3959837 < baseStart_3959837 := by decide
  rcases family_descends (prefixWord ++ tailWord_3959837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3959893 : List Nat := [1, 3, 2, 2, 1, 2, 3, 1, 4, 3]
def baseStart_3959893 : Nat := 118140960795 + 3959893 * 2 ^ 59
def prefixEnd_3959893 : Nat := 4983230072969 + 3 ^ 40 * 3959893 * 2
def baseEnd_3959893 : Nat := 1355552299583053756084193

theorem tailTrace_3959893 : CollatzResearch.WordTrace tailWord_3959893 prefixEnd_3959893 1355552299583053756084193 := by
  unfold tailWord_3959893
  simp only [CollatzResearch.WordTrace]
  refine ⟨144429163042991431726844333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96286108695327621151229555 144429163042991431726844333)
  ·
    refine ⟨54160936141121786897566625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 144429163042991431726844333 54160936141121786897566625)
    ·
      refine ⟨40620702105841340173174969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54160936141121786897566625 40620702105841340173174969)
      ·
        refine ⟨30465526579381005129881227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40620702105841340173174969 30465526579381005129881227)
        ·
          refine ⟨45698289869071507694821841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30465526579381005129881227 45698289869071507694821841)
          ·
            refine ⟨34273717401803630771116381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45698289869071507694821841 34273717401803630771116381)
            ·
              refine ⟨12852644025676361539168643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34273717401803630771116381 12852644025676361539168643)
              ·
                refine ⟨19278966038514542308752965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12852644025676361539168643 19278966038514542308752965)
                ·
                  refine ⟨3614806132221476682891181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19278966038514542308752965 3614806132221476682891181)
                  ·
                    refine ⟨1355552299583053756084193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3614806132221476682891181 1355552299583053756084193)
                    ·
                      rfl

theorem cell22_3959893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 3, 1, 4, 3].length) (baseStart_3959893 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3959893 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3959893 prefixEnd_3959893 := by exact prefixLift 3959893
  have htrace : WordTrace (prefixWord ++ tailWord_3959893) baseStart_3959893 baseEnd_3959893 := by
    simpa [prefixWord, tailWord_3959893, baseEnd_3959893] using wordTrace_append hprefix tailTrace_3959893
  have hstable : (prefixWord ++ tailWord_3959893).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3959893).length < 2 ^ (prefixWord ++ tailWord_3959893).sum := by decide
  have hdescent : baseEnd_3959893 < baseStart_3959893 := by decide
  rcases family_descends (prefixWord ++ tailWord_3959893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3959955 : List Nat := [1, 1, 1, 2, 1, 2, 4, 6, 1, 3]
def baseStart_3959955 : Nat := 118140960795 + 3959955 * 2 ^ 59
def prefixEnd_3959955 : Nat := 4983230072969 + 3 ^ 40 * 3959955 * 2
def baseEnd_3959955 : Nat := 1355573523450106261034003

theorem tailTrace_3959955 : CollatzResearch.WordTrace tailWord_3959955 prefixEnd_3959955 1355573523450106261034003 := by
  unfold tailWord_3959955
  simp only [CollatzResearch.WordTrace]
  refine ⟨144431424368766816315601319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96287616245844544210400879 144431424368766816315601319)
  ·
    refine ⟨216647136553150224473401979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144431424368766816315601319 216647136553150224473401979)
    ·
      refine ⟨324970704829725336710102969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216647136553150224473401979 324970704829725336710102969)
      ·
        refine ⟨243728028622294002532577227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 324970704829725336710102969 243728028622294002532577227)
        ·
          refine ⟨365592042933441003798865841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 243728028622294002532577227 365592042933441003798865841)
          ·
            refine ⟨274194032200080752849149381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 365592042933441003798865841 274194032200080752849149381)
            ·
              refine ⟨51411381037515141159215509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 274194032200080752849149381 51411381037515141159215509)
              ·
                refine ⟨2409908486133522241838227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 51411381037515141159215509 2409908486133522241838227)
                ·
                  refine ⟨3614862729200283362757341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2409908486133522241838227 3614862729200283362757341)
                  ·
                    refine ⟨1355573523450106261034003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3614862729200283362757341 1355573523450106261034003)
                    ·
                      rfl

theorem cell22_3959955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 6, 1, 3].length) (baseStart_3959955 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3959955 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3959955 prefixEnd_3959955 := by exact prefixLift 3959955
  have htrace : WordTrace (prefixWord ++ tailWord_3959955) baseStart_3959955 baseEnd_3959955 := by
    simpa [prefixWord, tailWord_3959955, baseEnd_3959955] using wordTrace_append hprefix tailTrace_3959955
  have hstable : (prefixWord ++ tailWord_3959955).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3959955).length < 2 ^ (prefixWord ++ tailWord_3959955).sum := by decide
  have hdescent : baseEnd_3959955 < baseStart_3959955 := by decide
  rcases family_descends (prefixWord ++ tailWord_3959955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3959968 : List Nat := [2, 1, 1, 4, 2, 1, 3, 3, 5]
def baseStart_3959968 : Nat := 118140960795 + 3959968 * 2 ^ 59
def prefixEnd_3959968 : Nat := 4983230072969 + 3 ^ 40 * 3959968 * 2
def baseEnd_3959968 : Nat := 451859324538592853486321

theorem tailTrace_3959968 : CollatzResearch.WordTrace tailWord_3959968 prefixEnd_3959968 451859324538592853486321 := by
  unfold tailWord_3959968
  simp only [CollatzResearch.WordTrace]
  refine ⟨72215949258859859767912279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96287932345146479690549705 72215949258859859767912279)
  ·
    refine ⟨108323923888289789651868419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72215949258859859767912279 108323923888289789651868419)
    ·
      refine ⟨162485885832434684477802629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108323923888289789651868419 162485885832434684477802629)
      ·
        refine ⟨30466103593581503339587993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 162485885832434684477802629 30466103593581503339587993)
        ·
          refine ⟨22849577695186127504690995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30466103593581503339587993 22849577695186127504690995)
          ·
            refine ⟨34274366542779191257036493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22849577695186127504690995 34274366542779191257036493)
            ·
              refine ⟨12852887453542196721388685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34274366542779191257036493 12852887453542196721388685)
              ·
                refine ⟨4819832795078323770520757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12852887453542196721388685 4819832795078323770520757)
                ·
                  refine ⟨451859324538592853486321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4819832795078323770520757 451859324538592853486321)
                  ·
                    rfl

theorem cell22_3959968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 3, 3, 5].length) (baseStart_3959968 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3959968 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3959968 prefixEnd_3959968 := by exact prefixLift 3959968
  have htrace : WordTrace (prefixWord ++ tailWord_3959968) baseStart_3959968 baseEnd_3959968 := by
    simpa [prefixWord, tailWord_3959968, baseEnd_3959968] using wordTrace_append hprefix tailTrace_3959968
  have hstable : (prefixWord ++ tailWord_3959968).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3959968).length < 2 ^ (prefixWord ++ tailWord_3959968).sum := by decide
  have hdescent : baseEnd_3959968 < baseStart_3959968 := by decide
  rcases family_descends (prefixWord ++ tailWord_3959968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3960043 : List Nat := [1, 1, 1, 1, 2, 7, 1, 1, 1, 6]
def baseStart_3960043 : Nat := 118140960795 + 3960043 * 2 ^ 59
def prefixEnd_3960043 : Nat := 4983230072969 + 3 ^ 40 * 3960043 * 2
def baseEnd_3960043 : Nat := 1355603647648503364833733

theorem tailTrace_3960043 : CollatzResearch.WordTrace tailWord_3960043 prefixEnd_3960043 1355603647648503364833733 := by
  unfold tailWord_3960043
  simp only [CollatzResearch.WordTrace]
  refine ⟨144434633992448007344804783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96289755994965338229869855 144434633992448007344804783)
  ·
    refine ⟨216651950988672011017207175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144434633992448007344804783 216651950988672011017207175)
    ·
      refine ⟨324977926483008016525810763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216651950988672011017207175 324977926483008016525810763)
      ·
        refine ⟨487466889724512024788716145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 324977926483008016525810763 487466889724512024788716145)
        ·
          refine ⟨365600167293384018591537109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 487466889724512024788716145 365600167293384018591537109)
          ·
            refine ⟨8568753920938687935739151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 365600167293384018591537109 8568753920938687935739151)
            ·
              refine ⟨12853130881408031903608727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8568753920938687935739151 12853130881408031903608727)
              ·
                refine ⟨19279696322112047855413091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12853130881408031903608727 19279696322112047855413091)
                ·
                  refine ⟨28919544483168071783119637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19279696322112047855413091 28919544483168071783119637)
                  ·
                    refine ⟨1355603647648503364833733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28919544483168071783119637 1355603647648503364833733)
                    ·
                      rfl

theorem cell22_3960043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 1, 1, 1, 6].length) (baseStart_3960043 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3960043 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3960043 prefixEnd_3960043 := by exact prefixLift 3960043
  have htrace : WordTrace (prefixWord ++ tailWord_3960043) baseStart_3960043 baseEnd_3960043 := by
    simpa [prefixWord, tailWord_3960043, baseEnd_3960043] using wordTrace_append hprefix tailTrace_3960043
  have hstable : (prefixWord ++ tailWord_3960043).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3960043).length < 2 ^ (prefixWord ++ tailWord_3960043).sum := by decide
  have hdescent : baseEnd_3960043 < baseStart_3960043 := by decide
  rcases family_descends (prefixWord ++ tailWord_3960043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3960045 : List Nat := [1, 5, 1, 2, 2, 1, 2, 2, 1, 5]
def baseStart_3960045 : Nat := 118140960795 + 3960045 * 2 ^ 59
def prefixEnd_3960045 : Nat := 4983230072969 + 3 ^ 40 * 3960045 * 2
def baseEnd_3960045 : Nat := 1355604332289376026283727

theorem tailTrace_3960045 : CollatzResearch.WordTrace tailWord_3960045 prefixEnd_3960045 1355604332289376026283727 := by
  unfold tailWord_3960045
  simp only [CollatzResearch.WordTrace]
  refine ⟨144434706938440761686377589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96289804625627174457585059 144434706938440761686377589)
  ·
    refine ⟨13540753775478821408097899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 144434706938440761686377589 13540753775478821408097899)
    ·
      refine ⟨20311130663218232112146849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13540753775478821408097899 20311130663218232112146849)
      ·
        refine ⟨15233347997413674084110137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20311130663218232112146849 15233347997413674084110137)
        ·
          refine ⟨11425010998060255563082603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15233347997413674084110137 11425010998060255563082603)
          ·
            refine ⟨17137516497090383344623905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11425010998060255563082603 17137516497090383344623905)
            ·
              refine ⟨12853137372817787508467929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17137516497090383344623905 12853137372817787508467929)
              ·
                refine ⟨9639853029613340631350947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12853137372817787508467929 9639853029613340631350947)
                ·
                  refine ⟨14459779544420010947026421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9639853029613340631350947 14459779544420010947026421)
                  ·
                    refine ⟨1355604332289376026283727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14459779544420010947026421 1355604332289376026283727)
                    ·
                      rfl

theorem cell22_3960045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 2, 2, 1, 5].length) (baseStart_3960045 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3960045 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3960045 prefixEnd_3960045 := by exact prefixLift 3960045
  have htrace : WordTrace (prefixWord ++ tailWord_3960045) baseStart_3960045 baseEnd_3960045 := by
    simpa [prefixWord, tailWord_3960045, baseEnd_3960045] using wordTrace_append hprefix tailTrace_3960045
  have hstable : (prefixWord ++ tailWord_3960045).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3960045).length < 2 ^ (prefixWord ++ tailWord_3960045).sum := by decide
  have hdescent : baseEnd_3960045 < baseStart_3960045 := by decide
  rcases family_descends (prefixWord ++ tailWord_3960045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3960047 : List Nat := [1, 1, 2, 1, 7, 1, 2, 3, 4]
def baseStart_3960047 : Nat := 118140960795 + 3960047 * 2 ^ 59
def prefixEnd_3960047 : Nat := 4983230072969 + 3 ^ 40 * 3960047 * 2
def baseEnd_3960047 : Nat := 451868338976749562577907

theorem tailTrace_3960047 : CollatzResearch.WordTrace tailWord_3960047 prefixEnd_3960047 451868338976749562577907 := by
  unfold tailWord_3960047
  simp only [CollatzResearch.WordTrace]
  refine ⟨144434779884433516027950395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96289853256289010685300263 144434779884433516027950395)
  ·
    refine ⟨216652169826650274041925593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144434779884433516027950395 216652169826650274041925593)
    ·
      refine ⟨162489127369987705531444195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 216652169826650274041925593 162489127369987705531444195)
      ·
        refine ⟨243733691054981558297166293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162489127369987705531444195 243733691054981558297166293)
        ·
          refine ⟨5712508384101130272589835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 243733691054981558297166293 5712508384101130272589835)
          ·
            refine ⟨8568762576151695408884753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5712508384101130272589835 8568762576151695408884753)
            ·
              refine ⟨6426571932113771556663565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8568762576151695408884753 6426571932113771556663565)
              ·
                refine ⟨2409964474542664333748837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6426571932113771556663565 2409964474542664333748837)
                ·
                  refine ⟨451868338976749562577907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2409964474542664333748837 451868338976749562577907)
                  ·
                    rfl

theorem cell22_3960047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 2, 3, 4].length) (baseStart_3960047 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3960047 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3960047 prefixEnd_3960047 := by exact prefixLift 3960047
  have htrace : WordTrace (prefixWord ++ tailWord_3960047) baseStart_3960047 baseEnd_3960047 := by
    simpa [prefixWord, tailWord_3960047, baseEnd_3960047] using wordTrace_append hprefix tailTrace_3960047
  have hstable : (prefixWord ++ tailWord_3960047).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3960047).length < 2 ^ (prefixWord ++ tailWord_3960047).sum := by decide
  have hdescent : baseEnd_3960047 < baseStart_3960047 := by decide
  rcases family_descends (prefixWord ++ tailWord_3960047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3960062 : List Nat := [4, 2, 2, 1, 1, 3, 1, 1, 4, 3]
def baseStart_3960062 : Nat := 118140960795 + 3960062 * 2 ^ 59
def prefixEnd_3960062 : Nat := 4983230072969 + 3 ^ 40 * 3960062 * 2
def baseEnd_3960062 : Nat := 1355610151736793648608675

theorem tailTrace_3960062 : CollatzResearch.WordTrace tailWord_3960062 prefixEnd_3960062 1355610151736793648608675 := by
  unfold tailWord_3960062
  simp only [CollatzResearch.WordTrace]
  refine ⟨18054415872422396698718305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 96290217986252782393164293 18054415872422396698718305)
  ·
    refine ⟨13540811904316797524038729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18054415872422396698718305 13540811904316797524038729)
    ·
      refine ⟨10155608928237598143029047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13540811904316797524038729 10155608928237598143029047)
      ·
        refine ⟨15233413392356397214543571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10155608928237598143029047 15233413392356397214543571)
        ·
          refine ⟨22850120088534595821815357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15233413392356397214543571 22850120088534595821815357)
          ·
            refine ⟨8568795033200473433180759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22850120088534595821815357 8568795033200473433180759)
            ·
              refine ⟨12853192549800710149771139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8568795033200473433180759 12853192549800710149771139)
              ·
                refine ⟨19279788824701065224656709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12853192549800710149771139 19279788824701065224656709)
                ·
                  refine ⟨3614960404631449729623133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19279788824701065224656709 3614960404631449729623133)
                  ·
                    refine ⟨1355610151736793648608675, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3614960404631449729623133 1355610151736793648608675)
                    ·
                      rfl

theorem cell22_3960062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 1, 1, 4, 3].length) (baseStart_3960062 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3960062 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3960062 prefixEnd_3960062 := by exact prefixLift 3960062
  have htrace : WordTrace (prefixWord ++ tailWord_3960062) baseStart_3960062 baseEnd_3960062 := by
    simpa [prefixWord, tailWord_3960062, baseEnd_3960062] using wordTrace_append hprefix tailTrace_3960062
  have hstable : (prefixWord ++ tailWord_3960062).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3960062).length < 2 ^ (prefixWord ++ tailWord_3960062).sum := by decide
  have hdescent : baseEnd_3960062 < baseStart_3960062 := by decide
  rcases family_descends (prefixWord ++ tailWord_3960062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3960197 : List Nat := [1, 3, 1, 1, 3, 1, 4, 3, 2, 3]
def baseStart_3960197 : Nat := 118140960795 + 3960197 * 2 ^ 59
def prefixEnd_3960197 : Nat := 4983230072969 + 3 ^ 40 * 3960197 * 2
def baseEnd_3960197 : Nat := 1355656364995698296483261

theorem tailTrace_3960197 : CollatzResearch.WordTrace tailWord_3960197 prefixEnd_3960197 1355656364995698296483261 := by
  unfold tailWord_3960197
  simp only [CollatzResearch.WordTrace]
  refine ⟨144440250833890091645910845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96293500555926727763940563 144440250833890091645910845)
  ·
    refine ⟨54165094062708784367216567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 144440250833890091645910845 54165094062708784367216567)
    ·
      refine ⟨81247641094063176550824851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54165094062708784367216567 81247641094063176550824851)
      ·
        refine ⟨121871461641094764826237277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81247641094063176550824851 121871461641094764826237277)
        ·
          refine ⟨45701798115410536809838979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 121871461641094764826237277 45701798115410536809838979)
          ·
            refine ⟨68552697173115805214758469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45701798115410536809838979 68552697173115805214758469)
            ·
              refine ⟨12853630719959213477767213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 68552697173115805214758469 12853630719959213477767213)
              ·
                refine ⟨4820111519984705054162705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12853630719959213477767213 4820111519984705054162705)
                ·
                  refine ⟨3615083639988528790622029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4820111519984705054162705 3615083639988528790622029)
                  ·
                    refine ⟨1355656364995698296483261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3615083639988528790622029 1355656364995698296483261)
                    ·
                      rfl

theorem cell22_3960197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 4, 3, 2, 3].length) (baseStart_3960197 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3960197 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3960197 prefixEnd_3960197 := by exact prefixLift 3960197
  have htrace : WordTrace (prefixWord ++ tailWord_3960197) baseStart_3960197 baseEnd_3960197 := by
    simpa [prefixWord, tailWord_3960197, baseEnd_3960197] using wordTrace_append hprefix tailTrace_3960197
  have hstable : (prefixWord ++ tailWord_3960197).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3960197).length < 2 ^ (prefixWord ++ tailWord_3960197).sum := by decide
  have hdescent : baseEnd_3960197 < baseStart_3960197 := by decide
  rcases family_descends (prefixWord ++ tailWord_3960197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3960212 : List Nat := [2, 4, 2, 1, 2, 2, 1, 1, 1, 6]
def baseStart_3960212 : Nat := 118140960795 + 3960212 * 2 ^ 59
def prefixEnd_3960212 : Nat := 4983230072969 + 3 ^ 40 * 3960212 * 2
def baseEnd_3960212 : Nat := 1355661499802243257358215

theorem tailTrace_3960212 : CollatzResearch.WordTrace tailWord_3960212 prefixEnd_3960212 1355661499802243257358215 := by
  unfold tailWord_3960212
  simp only [CollatzResearch.WordTrace]
  refine ⟨72220398964417874603853445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96293865285890499471804593 72220398964417874603853445)
  ·
    refine ⟨13541324805828351488222521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 72220398964417874603853445 13541324805828351488222521)
    ·
      refine ⟨10155993604371263616166891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13541324805828351488222521 10155993604371263616166891)
      ·
        refine ⟨15233990406556895424250337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10155993604371263616166891 15233990406556895424250337)
        ·
          refine ⟨11425492804917671568187753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15233990406556895424250337 11425492804917671568187753)
          ·
            refine ⟨8569119603688253676140815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11425492804917671568187753 8569119603688253676140815)
            ·
              refine ⟨12853679405532380514211223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8569119603688253676140815 12853679405532380514211223)
              ·
                refine ⟨19280519108298570771316835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12853679405532380514211223 19280519108298570771316835)
                ·
                  refine ⟨28920778662447856156975253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19280519108298570771316835 28920778662447856156975253)
                  ·
                    refine ⟨1355661499802243257358215, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28920778662447856156975253 1355661499802243257358215)
                    ·
                      rfl

theorem cell22_3960212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 1, 1, 1, 6].length) (baseStart_3960212 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3960212 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3960212 prefixEnd_3960212 := by exact prefixLift 3960212
  have htrace : WordTrace (prefixWord ++ tailWord_3960212) baseStart_3960212 baseEnd_3960212 := by
    simpa [prefixWord, tailWord_3960212, baseEnd_3960212] using wordTrace_append hprefix tailTrace_3960212
  have hstable : (prefixWord ++ tailWord_3960212).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3960212).length < 2 ^ (prefixWord ++ tailWord_3960212).sum := by decide
  have hdescent : baseEnd_3960212 < baseStart_3960212 := by decide
  rcases family_descends (prefixWord ++ tailWord_3960212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3960255 : List Nat := [1, 1, 2, 2, 2, 1, 1, 7, 5]
def baseStart_3960255 : Nat := 118140960795 + 3960255 * 2 ^ 59
def prefixEnd_3960255 : Nat := 4983230072969 + 3 ^ 40 * 3960255 * 2
def baseEnd_3960255 : Nat := 451892073193668492844361

theorem tailTrace_3960255 : CollatzResearch.WordTrace tailWord_3960255 prefixEnd_3960255 451892073193668492844361 := by
  unfold tailWord_3960255
  simp only [CollatzResearch.WordTrace]
  refine ⟨144442366267679967551522219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96294910845119978367681479 144442366267679967551522219)
  ·
    refine ⟨216663549401519951327283329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144442366267679967551522219 216663549401519951327283329)
    ·
      refine ⟨162497662051139963495462497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 216663549401519951327283329 162497662051139963495462497)
      ·
        refine ⟨121873246538354972621596873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 162497662051139963495462497 121873246538354972621596873)
        ·
          refine ⟨91404934903766229466197655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 121873246538354972621596873 91404934903766229466197655)
          ·
            refine ⟨137107402355649344199296483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91404934903766229466197655 137107402355649344199296483)
            ·
              refine ⟨205661103533474016298944725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 137107402355649344199296483 205661103533474016298944725)
              ·
                refine ⟨4820182114065797257006517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 205661103533474016298944725 4820182114065797257006517)
                ·
                  refine ⟨451892073193668492844361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4820182114065797257006517 451892073193668492844361)
                  ·
                    rfl

theorem cell22_3960255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 7, 5].length) (baseStart_3960255 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3960255 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3960255 prefixEnd_3960255 := by exact prefixLift 3960255
  have htrace : WordTrace (prefixWord ++ tailWord_3960255) baseStart_3960255 baseEnd_3960255 := by
    simpa [prefixWord, tailWord_3960255, baseEnd_3960255] using wordTrace_append hprefix tailTrace_3960255
  have hstable : (prefixWord ++ tailWord_3960255).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3960255).length < 2 ^ (prefixWord ++ tailWord_3960255).sum := by decide
  have hdescent : baseEnd_3960255 < baseStart_3960255 := by decide
  rcases family_descends (prefixWord ++ tailWord_3960255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3960270 : List Nat := [4, 1, 1, 1, 2, 1, 2, 2, 1, 7]
def baseStart_3960270 : Nat := 118140960795 + 3960270 * 2 ^ 59
def prefixEnd_3960270 : Nat := 4983230072969 + 3 ^ 40 * 3960270 * 2
def baseEnd_3960270 : Nat := 1355681354387550439408037

theorem tailTrace_3960270 : CollatzResearch.WordTrace tailWord_3960270 prefixEnd_3960270 1355681354387550439408037 := by
  unfold tailWord_3960270
  simp only [CollatzResearch.WordTrace]
  refine ⟨18055364170328203139164783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 96295275575083750075545509 18055364170328203139164783)
  ·
    refine ⟨27083046255492304708747175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18055364170328203139164783 27083046255492304708747175)
    ·
      refine ⟨40624569383238457063120763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27083046255492304708747175 40624569383238457063120763)
      ·
        refine ⟨60936854074857685594681145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40624569383238457063120763 60936854074857685594681145)
        ·
          refine ⟨45702640556143264196010859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60936854074857685594681145 45702640556143264196010859)
          ·
            refine ⟨68553960834214896294016289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45702640556143264196010859 68553960834214896294016289)
            ·
              refine ⟨51415470625661172220512217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68553960834214896294016289 51415470625661172220512217)
              ·
                refine ⟨38561602969245879165384163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51415470625661172220512217 38561602969245879165384163)
                ·
                  refine ⟨57842404453868818748076245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38561602969245879165384163 57842404453868818748076245)
                  ·
                    refine ⟨1355681354387550439408037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 57842404453868818748076245 1355681354387550439408037)
                    ·
                      rfl

theorem cell22_3960270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 2, 1, 7].length) (baseStart_3960270 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3960270 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3960270 prefixEnd_3960270 := by exact prefixLift 3960270
  have htrace : WordTrace (prefixWord ++ tailWord_3960270) baseStart_3960270 baseEnd_3960270 := by
    simpa [prefixWord, tailWord_3960270, baseEnd_3960270] using wordTrace_append hprefix tailTrace_3960270
  have hstable : (prefixWord ++ tailWord_3960270).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3960270).length < 2 ^ (prefixWord ++ tailWord_3960270).sum := by decide
  have hdescent : baseEnd_3960270 < baseStart_3960270 := by decide
  rcases family_descends (prefixWord ++ tailWord_3960270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3960293 : List Nat := [1, 3, 1, 5, 1, 2, 3, 2, 1, 3]
def baseStart_3960293 : Nat := 118140960795 + 3960293 * 2 ^ 59
def prefixEnd_3960293 : Nat := 4983230072969 + 3 ^ 40 * 3960293 * 2
def baseEnd_3960293 : Nat := 1355689227757586046082967

theorem tailTrace_3960293 : CollatzResearch.WordTrace tailWord_3960293 prefixEnd_3960293 1355689227757586046082967 := by
  unfold tailWord_3960293
  simp only [CollatzResearch.WordTrace]
  refine ⟨144443752241542300041405533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96295834827694866694270355 144443752241542300041405533)
  ·
    refine ⟨54166407090578362515527075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 144443752241542300041405533 54166407090578362515527075)
    ·
      refine ⟨81249610635867543773290613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54166407090578362515527075 81249610635867543773290613)
      ·
        refine ⟨7617150997112582228745995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 81249610635867543773290613 7617150997112582228745995)
        ·
          refine ⟨11425726495668873343118993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7617150997112582228745995 11425726495668873343118993)
          ·
            refine ⟨8569294871751655007339245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11425726495668873343118993 8569294871751655007339245)
            ·
              refine ⟨3213485576906870627752217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8569294871751655007339245 3213485576906870627752217)
              ·
                refine ⟨2410114182680152970814163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3213485576906870627752217 2410114182680152970814163)
                ·
                  refine ⟨3615171274020229456221245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2410114182680152970814163 3615171274020229456221245)
                  ·
                    refine ⟨1355689227757586046082967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3615171274020229456221245 1355689227757586046082967)
                    ·
                      rfl

theorem cell22_3960293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 3, 2, 1, 3].length) (baseStart_3960293 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3960293 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3960293 prefixEnd_3960293 := by exact prefixLift 3960293
  have htrace : WordTrace (prefixWord ++ tailWord_3960293) baseStart_3960293 baseEnd_3960293 := by
    simpa [prefixWord, tailWord_3960293, baseEnd_3960293] using wordTrace_append hprefix tailTrace_3960293
  have hstable : (prefixWord ++ tailWord_3960293).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3960293).length < 2 ^ (prefixWord ++ tailWord_3960293).sum := by decide
  have hdescent : baseEnd_3960293 < baseStart_3960293 := by decide
  rcases family_descends (prefixWord ++ tailWord_3960293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3960300 : List Nat := [2, 2, 1, 1, 2, 1, 2, 5, 6]
def baseStart_3960300 : Nat := 118140960795 + 3960300 * 2 ^ 59
def prefixEnd_3960300 : Nat := 4983230072969 + 3 ^ 40 * 3960300 * 2
def baseEnd_3960300 : Nat := 451897208000213453719315

theorem tailTrace_3960300 : CollatzResearch.WordTrace tailWord_3960300 prefixEnd_3960300 451897208000213453719315 := by
  unfold tailWord_3960300
  simp only [CollatzResearch.WordTrace]
  refine ⟨72222003776258470118455177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96296005035011293491273569 72222003776258470118455177)
  ·
    refine ⟨54166502832193852588841383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72222003776258470118455177 54166502832193852588841383)
    ·
      refine ⟨81249754248290778883262075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54166502832193852588841383 81249754248290778883262075)
      ·
        refine ⟨121874631372436168324893113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81249754248290778883262075 121874631372436168324893113)
        ·
          refine ⟨91405973529327126243669835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 121874631372436168324893113 91405973529327126243669835)
          ·
            refine ⟨137108960293990689365504753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91405973529327126243669835 137108960293990689365504753)
            ·
              refine ⟨102831720220493017024128565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 137108960293990689365504753 102831720220493017024128565)
              ·
                refine ⟨9640473770671220346012053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 102831720220493017024128565 9640473770671220346012053)
                ·
                  refine ⟨451897208000213453719315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9640473770671220346012053 451897208000213453719315)
                  ·
                    rfl

theorem cell22_3960300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 6].length) (baseStart_3960300 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3960300 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3960300 prefixEnd_3960300 := by exact prefixLift 3960300
  have htrace : WordTrace (prefixWord ++ tailWord_3960300) baseStart_3960300 baseEnd_3960300 := by
    simpa [prefixWord, tailWord_3960300, baseEnd_3960300] using wordTrace_append hprefix tailTrace_3960300
  have hstable : (prefixWord ++ tailWord_3960300).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3960300).length < 2 ^ (prefixWord ++ tailWord_3960300).sum := by decide
  have hdescent : baseEnd_3960300 < baseStart_3960300 := by decide
  rcases family_descends (prefixWord ++ tailWord_3960300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3960302 : List Nat := [4, 1, 2, 1, 2, 1, 2, 2, 3, 4]
def baseStart_3960302 : Nat := 118140960795 + 3960302 * 2 ^ 59
def prefixEnd_3960302 : Nat := 4983230072969 + 3 ^ 40 * 3960302 * 2
def baseEnd_3960302 : Nat := 1355692308641513022607939

theorem tailTrace_3960302 : CollatzResearch.WordTrace tailWord_3960302 prefixEnd_3960302 1355692308641513022607939 := by
  unfold tailWord_3960302
  simp only [CollatzResearch.WordTrace]
  refine ⟨18055510062313711822310395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 96296053665673129718988773 18055510062313711822310395)
  ·
    refine ⟨27083265093470567733465593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18055510062313711822310395 27083265093470567733465593)
    ·
      refine ⟨20312448820102925800099195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27083265093470567733465593 20312448820102925800099195)
      ·
        refine ⟨30468673230154388700148793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20312448820102925800099195 30468673230154388700148793)
        ·
          refine ⟨22851504922615791525111595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30468673230154388700148793 22851504922615791525111595)
          ·
            refine ⟨34277257383923687287667393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22851504922615791525111595 34277257383923687287667393)
            ·
              refine ⟨25707943037942765465750545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34277257383923687287667393 25707943037942765465750545)
              ·
                refine ⟨19280957278457074099312909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25707943037942765465750545 19280957278457074099312909)
                ·
                  refine ⟨7230358979421402787242341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19280957278457074099312909 7230358979421402787242341)
                  ·
                    refine ⟨1355692308641513022607939, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7230358979421402787242341 1355692308641513022607939)
                    ·
                      rfl

theorem cell22_3960302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 2, 2, 3, 4].length) (baseStart_3960302 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3960302 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3960302 prefixEnd_3960302 := by exact prefixLift 3960302
  have htrace : WordTrace (prefixWord ++ tailWord_3960302) baseStart_3960302 baseEnd_3960302 := by
    simpa [prefixWord, tailWord_3960302, baseEnd_3960302] using wordTrace_append hprefix tailTrace_3960302
  have hstable : (prefixWord ++ tailWord_3960302).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3960302).length < 2 ^ (prefixWord ++ tailWord_3960302).sum := by decide
  have hdescent : baseEnd_3960302 < baseStart_3960302 := by decide
  rcases family_descends (prefixWord ++ tailWord_3960302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3960306 : List Nat := [3, 2, 1, 4, 1, 3, 2, 1, 5]
def baseStart_3960306 : Nat := 118140960795 + 3960306 * 2 ^ 59
def prefixEnd_3960306 : Nat := 4983230072969 + 3 ^ 40 * 3960306 * 2
def baseEnd_3960306 : Nat := 451897892641086115169309

theorem tailTrace_3960306 : CollatzResearch.WordTrace tailWord_3960306 prefixEnd_3960306 451897892641086115169309 := by
  unfold tailWord_3960306
  simp only [CollatzResearch.WordTrace]
  refine ⟨36111056597623800815407193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96296150926996802174419181 36111056597623800815407193)
  ·
    refine ⟨27083292448217850611555395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36111056597623800815407193 27083292448217850611555395)
    ·
      refine ⟨40624938672326775917333093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27083292448217850611555395 40624938672326775917333093)
      ·
        refine ⟨7617176001061270484499955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 40624938672326775917333093 7617176001061270484499955)
        ·
          refine ⟨11425764001591905726749933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7617176001061270484499955 11425764001591905726749933)
          ·
            refine ⟨4284661500596964647531225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11425764001591905726749933 4284661500596964647531225)
            ·
              refine ⟨3213496125447723485648419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4284661500596964647531225 3213496125447723485648419)
              ·
                refine ⟨4820244188171585228472629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3213496125447723485648419 4820244188171585228472629)
                ·
                  refine ⟨451897892641086115169309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4820244188171585228472629 451897892641086115169309)
                  ·
                    rfl

theorem cell22_3960306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 3, 2, 1, 5].length) (baseStart_3960306 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3960306 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3960306 prefixEnd_3960306 := by exact prefixLift 3960306
  have htrace : WordTrace (prefixWord ++ tailWord_3960306) baseStart_3960306 baseEnd_3960306 := by
    simpa [prefixWord, tailWord_3960306, baseEnd_3960306] using wordTrace_append hprefix tailTrace_3960306
  have hstable : (prefixWord ++ tailWord_3960306).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3960306).length < 2 ^ (prefixWord ++ tailWord_3960306).sum := by decide
  have hdescent : baseEnd_3960306 < baseStart_3960306 := by decide
  rcases family_descends (prefixWord ++ tailWord_3960306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3960366 : List Nat := [4, 1, 3, 1, 2, 1, 2, 3, 2, 3]
def baseStart_3960366 : Nat := 118140960795 + 3960366 * 2 ^ 59
def prefixEnd_3960366 : Nat := 4983230072969 + 3 ^ 40 * 3960366 * 2
def baseEnd_3960366 : Nat := 1355714217149438189007743

theorem tailTrace_3960366 : CollatzResearch.WordTrace tailWord_3960366 prefixEnd_3960366 1355714217149438189007743 := by
  unfold tailWord_3960366
  simp only [CollatzResearch.WordTrace]
  refine ⟨18055801846284729188601619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 96297609846851889005875301 18055801846284729188601619)
  ·
    refine ⟨27083702769427093782902429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18055801846284729188601619 27083702769427093782902429)
    ·
      refine ⟨10156388538535160168588411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27083702769427093782902429 10156388538535160168588411)
      ·
        refine ⟨15234582807802740252882617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10156388538535160168588411 15234582807802740252882617)
        ·
          refine ⟨11425937105852055189661963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15234582807802740252882617 11425937105852055189661963)
          ·
            refine ⟨17138905658778082784492945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11425937105852055189661963 17138905658778082784492945)
            ·
              refine ⟨12854179244083562088369709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17138905658778082784492945 12854179244083562088369709)
              ·
                refine ⟨4820317216531335783138641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12854179244083562088369709 4820317216531335783138641)
                ·
                  refine ⟨3615237912398501837353981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4820317216531335783138641 3615237912398501837353981)
                  ·
                    refine ⟨1355714217149438189007743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3615237912398501837353981 1355714217149438189007743)
                    ·
                      rfl

theorem cell22_3960366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 2, 3, 2, 3].length) (baseStart_3960366 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3960366 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3960366 prefixEnd_3960366 := by exact prefixLift 3960366
  have htrace : WordTrace (prefixWord ++ tailWord_3960366) baseStart_3960366 baseEnd_3960366 := by
    simpa [prefixWord, tailWord_3960366, baseEnd_3960366] using wordTrace_append hprefix tailTrace_3960366
  have hstable : (prefixWord ++ tailWord_3960366).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3960366).length < 2 ^ (prefixWord ++ tailWord_3960366).sum := by decide
  have hdescent : baseEnd_3960366 < baseStart_3960366 := by decide
  rcases family_descends (prefixWord ++ tailWord_3960366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3960381 : List Nat := [1, 4, 1, 3, 3, 2, 1, 1, 2, 4]
def baseStart_3960381 : Nat := 118140960795 + 3960381 * 2 ^ 59
def prefixEnd_3960381 : Nat := 4983230072969 + 3 ^ 40 * 3960381 * 2
def baseEnd_3960381 : Nat := 1355719351955983149882697

theorem tailTrace_3960381 : CollatzResearch.WordTrace tailWord_3960381 prefixEnd_3960381 1355719351955983149882697 := by
  unfold tailWord_3960381
  simp only [CollatzResearch.WordTrace]
  refine ⟨144446961865223491070608997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96297974576815660713739331 144446961865223491070608997)
  ·
    refine ⟨27083805349729404575739187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 144446961865223491070608997 27083805349729404575739187)
    ·
      refine ⟨40625708024594106863608781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27083805349729404575739187 40625708024594106863608781)
      ·
        refine ⟨15234640509222790073853293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40625708024594106863608781 15234640509222790073853293)
        ·
          refine ⟨5712990190958546277694985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15234640509222790073853293 5712990190958546277694985)
          ·
            refine ⟨4284742643218909708271239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5712990190958546277694985 4284742643218909708271239)
            ·
              refine ⟨6427113964828364562406859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4284742643218909708271239 6427113964828364562406859)
              ·
                refine ⟨9640670947242546843610289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6427113964828364562406859 9640670947242546843610289)
                ·
                  refine ⟨7230503210431910132707717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9640670947242546843610289 7230503210431910132707717)
                  ·
                    refine ⟨1355719351955983149882697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7230503210431910132707717 1355719351955983149882697)
                    ·
                      rfl

theorem cell22_3960381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 2, 1, 1, 2, 4].length) (baseStart_3960381 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3960381 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3960381 prefixEnd_3960381 := by exact prefixLift 3960381
  have htrace : WordTrace (prefixWord ++ tailWord_3960381) baseStart_3960381 baseEnd_3960381 := by
    simpa [prefixWord, tailWord_3960381, baseEnd_3960381] using wordTrace_append hprefix tailTrace_3960381
  have hstable : (prefixWord ++ tailWord_3960381).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3960381).length < 2 ^ (prefixWord ++ tailWord_3960381).sum := by decide
  have hdescent : baseEnd_3960381 < baseStart_3960381 := by decide
  rcases family_descends (prefixWord ++ tailWord_3960381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3960407 : List Nat := [1, 1, 3, 2, 2, 4, 1, 1, 7]
def baseStart_3960407 : Nat := 118140960795 + 3960407 * 2 ^ 59
def prefixEnd_3960407 : Nat := 4983230072969 + 3 ^ 40 * 3960407 * 2
def baseEnd_3960407 : Nat := 451909417429109249577539

theorem tailTrace_3960407 : CollatzResearch.WordTrace tailWord_3960407 prefixEnd_3960407 451909417429109249577539 := by
  unfold tailWord_3960407
  simp only [CollatzResearch.WordTrace]
  refine ⟨144447910163129297511055475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96298606775419531674036983 144447910163129297511055475)
  ·
    refine ⟨216671865244693946266583213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144447910163129297511055475 216671865244693946266583213)
    ·
      refine ⟨81251949466760229849968705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 216671865244693946266583213 81251949466760229849968705)
      ·
        refine ⟨60938962100070172387476529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81251949466760229849968705 60938962100070172387476529)
        ·
          refine ⟨45704221575052629290607397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60938962100070172387476529 45704221575052629290607397)
          ·
            refine ⟨8569541545322367991988887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45704221575052629290607397 8569541545322367991988887)
            ·
              refine ⟨12854312317983551987983331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8569541545322367991988887 12854312317983551987983331)
              ·
                refine ⟨19281468476975327981974997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12854312317983551987983331 19281468476975327981974997)
                ·
                  refine ⟨451909417429109249577539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19281468476975327981974997 451909417429109249577539)
                  ·
                    rfl

theorem cell22_3960407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 1, 1, 7].length) (baseStart_3960407 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3960407 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3960407 prefixEnd_3960407 := by exact prefixLift 3960407
  have htrace : WordTrace (prefixWord ++ tailWord_3960407) baseStart_3960407 baseEnd_3960407 := by
    simpa [prefixWord, tailWord_3960407, baseEnd_3960407] using wordTrace_append hprefix tailTrace_3960407
  have hstable : (prefixWord ++ tailWord_3960407).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3960407).length < 2 ^ (prefixWord ++ tailWord_3960407).sum := by decide
  have hdescent : baseEnd_3960407 < baseStart_3960407 := by decide
  rcases family_descends (prefixWord ++ tailWord_3960407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3960469 : List Nat := [1, 3, 2, 1, 1, 1, 1, 8, 4]
def baseStart_3960469 : Nat := 118140960795 + 3960469 * 2 ^ 59
def prefixEnd_3960469 : Nat := 4983230072969 + 3 ^ 40 * 3960469 * 2
def baseEnd_3960469 : Nat := 451916492051460084560809

theorem tailTrace_3960469 : CollatzResearch.WordTrace tailWord_3960469 prefixEnd_3960469 451916492051460084560809 := by
  unfold tailWord_3960469
  simp only [CollatzResearch.WordTrace]
  refine ⟨144450171488904682099812461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96300114325936454733208307 144450171488904682099812461)
  ·
    refine ⟨54168814308339255787429673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 144450171488904682099812461 54168814308339255787429673)
    ·
      refine ⟨40626610731254441840572255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54168814308339255787429673 40626610731254441840572255)
      ·
        refine ⟨60939916096881662760858383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40626610731254441840572255 60939916096881662760858383)
        ·
          refine ⟨91409874145322494141287575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60939916096881662760858383 91409874145322494141287575)
          ·
            refine ⟨137114811217983741211931363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91409874145322494141287575 137114811217983741211931363)
            ·
              refine ⟨205672216826975611817897045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 137114811217983741211931363 205672216826975611817897045)
              ·
                refine ⟨2410221290941120450990981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 205672216826975611817897045 2410221290941120450990981)
                ·
                  refine ⟨451916492051460084560809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2410221290941120450990981 451916492051460084560809)
                  ·
                    rfl

theorem cell22_3960469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 8, 4].length) (baseStart_3960469 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3960469 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3960469 prefixEnd_3960469 := by exact prefixLift 3960469
  have htrace : WordTrace (prefixWord ++ tailWord_3960469) baseStart_3960469 baseEnd_3960469 := by
    simpa [prefixWord, tailWord_3960469, baseEnd_3960469] using wordTrace_append hprefix tailTrace_3960469
  have hstable : (prefixWord ++ tailWord_3960469).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3960469).length < 2 ^ (prefixWord ++ tailWord_3960469).sum := by decide
  have hdescent : baseEnd_3960469 < baseStart_3960469 := by decide
  rcases family_descends (prefixWord ++ tailWord_3960469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3960499 : List Nat := [1, 1, 1, 2, 3, 3, 4, 1, 2, 4]
def baseStart_3960499 : Nat := 118140960795 + 3960499 * 2 ^ 59
def prefixEnd_3960499 : Nat := 4983230072969 + 3 ^ 40 * 3960499 * 2
def baseEnd_3960499 : Nat := 1355759745767470175432335

theorem tailTrace_3960499 : CollatzResearch.WordTrace tailWord_3960499 prefixEnd_3960499 1355759745767470175432335 := by
  unfold tailWord_3960499
  simp only [CollatzResearch.WordTrace]
  refine ⟨144451265678795997223404551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96300843785863998148936367 144451265678795997223404551)
  ·
    refine ⟨216676898518193995835106827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144451265678795997223404551 216676898518193995835106827)
    ·
      refine ⟨325015347777290993752660241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216676898518193995835106827 325015347777290993752660241)
      ·
        refine ⟨243761510832968245314495181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 325015347777290993752660241 243761510832968245314495181)
        ·
          refine ⟨91410566562363091992935693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 243761510832968245314495181 91410566562363091992935693)
          ·
            refine ⟨34278962460886159497350885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 91410566562363091992935693 34278962460886159497350885)
            ·
              refine ⟨6427305461416154905753291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34278962460886159497350885 6427305461416154905753291)
              ·
                refine ⟨9640958192124232358629937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6427305461416154905753291 9640958192124232358629937)
                ·
                  refine ⟨7230718644093174268972453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9640958192124232358629937 7230718644093174268972453)
                  ·
                    refine ⟨1355759745767470175432335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7230718644093174268972453 1355759745767470175432335)
                    ·
                      rfl

theorem cell22_3960499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 4, 1, 2, 4].length) (baseStart_3960499 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3960499 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3960499 prefixEnd_3960499 := by exact prefixLift 3960499
  have htrace : WordTrace (prefixWord ++ tailWord_3960499) baseStart_3960499 baseEnd_3960499 := by
    simpa [prefixWord, tailWord_3960499, baseEnd_3960499] using wordTrace_append hprefix tailTrace_3960499
  have hstable : (prefixWord ++ tailWord_3960499).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3960499).length < 2 ^ (prefixWord ++ tailWord_3960499).sum := by decide
  have hdescent : baseEnd_3960499 < baseStart_3960499 := by decide
  rcases family_descends (prefixWord ++ tailWord_3960499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3960501 : List Nat := [1, 3, 3, 3, 2, 1, 1, 2, 1, 5]
def baseStart_3960501 : Nat := 118140960795 + 3960501 * 2 ^ 59
def prefixEnd_3960501 : Nat := 4983230072969 + 3 ^ 40 * 3960501 * 2
def baseEnd_3960501 : Nat := 1355760430408342836882329

theorem tailTrace_3960501 : CollatzResearch.WordTrace tailWord_3960501 prefixEnd_3960501 1355760430408342836882329 := by
  unfold tailWord_3960501
  simp only [CollatzResearch.WordTrace]
  refine ⟨144451338624788751564977357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96300892416525834376651571 144451338624788751564977357)
  ·
    refine ⟨54169251984295781836866509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 144451338624788751564977357 54169251984295781836866509)
    ·
      refine ⟨20313469494110918188824941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54169251984295781836866509 20313469494110918188824941)
      ·
        refine ⟨7617551060291594320809353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20313469494110918188824941 7617551060291594320809353)
        ·
          refine ⟨5713163295218695740607015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7617551060291594320809353 5713163295218695740607015)
          ·
            refine ⟨8569744942828043610910523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5713163295218695740607015 8569744942828043610910523)
            ·
              refine ⟨12854617414242065416365785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8569744942828043610910523 12854617414242065416365785)
              ·
                refine ⟨9640963060681549062274339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12854617414242065416365785 9640963060681549062274339)
                ·
                  refine ⟨14461444591022323593411509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9640963060681549062274339 14461444591022323593411509)
                  ·
                    refine ⟨1355760430408342836882329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14461444591022323593411509 1355760430408342836882329)
                    ·
                      rfl

theorem cell22_3960501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 1, 2, 1, 5].length) (baseStart_3960501 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3960501 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3960501 prefixEnd_3960501 := by exact prefixLift 3960501
  have htrace : WordTrace (prefixWord ++ tailWord_3960501) baseStart_3960501 baseEnd_3960501 := by
    simpa [prefixWord, tailWord_3960501, baseEnd_3960501] using wordTrace_append hprefix tailTrace_3960501
  have hstable : (prefixWord ++ tailWord_3960501).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3960501).length < 2 ^ (prefixWord ++ tailWord_3960501).sum := by decide
  have hdescent : baseEnd_3960501 < baseStart_3960501 := by decide
  rcases family_descends (prefixWord ++ tailWord_3960501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3960604 : List Nat := [2, 2, 3, 1, 1, 2, 1, 4, 6]
def baseStart_3960604 : Nat := 118140960795 + 3960604 * 2 ^ 59
def prefixEnd_3960604 : Nat := 4983230072969 + 3 ^ 40 * 3960604 * 2
def baseEnd_3960604 : Nat := 451931896471094967185671

theorem tailTrace_3960604 : CollatzResearch.WordTrace tailWord_3960604 prefixEnd_3960604 451931896471094967185671 := by
  unfold tailWord_3960604
  simp only [CollatzResearch.WordTrace]
  refine ⟨72227547671707800077988433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96303396895610400103984577 72227547671707800077988433)
  ·
    refine ⟨54170660753780850058491325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72227547671707800077988433 54170660753780850058491325)
    ·
      refine ⟨20313997782667818771934247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54170660753780850058491325 20313997782667818771934247)
      ·
        refine ⟨30470996674001728157901371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20313997782667818771934247 30470996674001728157901371)
        ·
          refine ⟨45706495011002592236852057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30470996674001728157901371 45706495011002592236852057)
          ·
            refine ⟨34279871258251944177639043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45706495011002592236852057 34279871258251944177639043)
            ·
              refine ⟨51419806887377916266458565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34279871258251944177639043 51419806887377916266458565)
              ·
                refine ⟨9641213791383359299960981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 51419806887377916266458565 9641213791383359299960981)
                ·
                  refine ⟨451931896471094967185671, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9641213791383359299960981 451931896471094967185671)
                  ·
                    rfl

theorem cell22_3960604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 4, 6].length) (baseStart_3960604 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3960604 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3960604 prefixEnd_3960604 := by exact prefixLift 3960604
  have htrace : WordTrace (prefixWord ++ tailWord_3960604) baseStart_3960604 baseEnd_3960604 := by
    simpa [prefixWord, tailWord_3960604, baseEnd_3960604] using wordTrace_append hprefix tailTrace_3960604
  have hstable : (prefixWord ++ tailWord_3960604).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3960604).length < 2 ^ (prefixWord ++ tailWord_3960604).sum := by decide
  have hdescent : baseEnd_3960604 < baseStart_3960604 := by decide
  rcases family_descends (prefixWord ++ tailWord_3960604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3960636 : List Nat := [2, 2, 2, 2, 1, 1, 4, 1, 4, 3]
def baseStart_3960636 : Nat := 118140960795 + 3960636 * 2 ^ 59
def prefixEnd_3960636 : Nat := 4983230072969 + 3 ^ 40 * 3960636 * 2
def baseEnd_3960636 : Nat := 1355806643667247484756915

theorem tailTrace_3960636 : CollatzResearch.WordTrace tailWord_3960636 prefixEnd_3960636 1355806643667247484756915 := by
  unfold tailWord_3960636
  simp only [CollatzResearch.WordTrace]
  refine ⟨72228131239649834810570881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96304174986199779747427841 72228131239649834810570881)
  ·
    refine ⟨54171098429737376107928161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72228131239649834810570881 54171098429737376107928161)
    ·
      refine ⟨40628323822303032080946121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54171098429737376107928161 40628323822303032080946121)
      ·
        refine ⟨30471242866727274060709591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40628323822303032080946121 30471242866727274060709591)
        ·
          refine ⟨45706864300090911091064387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30471242866727274060709591 45706864300090911091064387)
          ·
            refine ⟨68560296450136366636596581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45706864300090911091064387 68560296450136366636596581)
            ·
              refine ⟨12855055584400568744361859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 68560296450136366636596581 12855055584400568744361859)
              ·
                refine ⟨19282583376600853116542789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12855055584400568744361859 19282583376600853116542789)
                ·
                  refine ⟨3615484383112659959351773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19282583376600853116542789 3615484383112659959351773)
                  ·
                    refine ⟨1355806643667247484756915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3615484383112659959351773 1355806643667247484756915)
                    ·
                      rfl

theorem cell22_3960636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 4, 1, 4, 3].length) (baseStart_3960636 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3960636 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3960636 prefixEnd_3960636 := by exact prefixLift 3960636
  have htrace : WordTrace (prefixWord ++ tailWord_3960636) baseStart_3960636 baseEnd_3960636 := by
    simpa [prefixWord, tailWord_3960636, baseEnd_3960636] using wordTrace_append hprefix tailTrace_3960636
  have hstable : (prefixWord ++ tailWord_3960636).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3960636).length < 2 ^ (prefixWord ++ tailWord_3960636).sum := by decide
  have hdescent : baseEnd_3960636 < baseStart_3960636 := by decide
  rcases family_descends (prefixWord ++ tailWord_3960636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3960638 : List Nat := [4, 2, 1, 2, 2, 3, 1, 1, 6]
def baseStart_3960638 : Nat := 118140960795 + 3960638 * 2 ^ 59
def prefixEnd_3960638 : Nat := 4983230072969 + 3 ^ 40 * 3960638 * 2
def baseEnd_3960638 : Nat := 451935776102706715402303

theorem tailTrace_3960638 : CollatzResearch.WordTrace tailWord_3960638 prefixEnd_3960638 451935776102706715402303 := by
  unfold tailWord_3960638
  simp only [CollatzResearch.WordTrace]
  refine ⟨18057041928161552995339321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 96304223616861615975143045 18057041928161552995339321)
  ·
    refine ⟨13542781446121164746504491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18057041928161552995339321 13542781446121164746504491)
    ·
      refine ⟨20314172169181747119756737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13542781446121164746504491 20314172169181747119756737)
      ·
        refine ⟨15235629126886310339817553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20314172169181747119756737 15235629126886310339817553)
        ·
          refine ⟨11426721845164732754863165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15235629126886310339817553 11426721845164732754863165)
          ·
            refine ⟨4285020691936774783073687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11426721845164732754863165 4285020691936774783073687)
            ·
              refine ⟨6427531037905162174610531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4285020691936774783073687 6427531037905162174610531)
              ·
                refine ⟨9641296556857743261915797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6427531037905162174610531 9641296556857743261915797)
                ·
                  refine ⟨451935776102706715402303, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9641296556857743261915797 451935776102706715402303)
                  ·
                    rfl

theorem cell22_3960638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 3, 1, 1, 6].length) (baseStart_3960638 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3960638 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3960638 prefixEnd_3960638 := by exact prefixLift 3960638
  have htrace : WordTrace (prefixWord ++ tailWord_3960638) baseStart_3960638 baseEnd_3960638 := by
    simpa [prefixWord, tailWord_3960638, baseEnd_3960638] using wordTrace_append hprefix tailTrace_3960638
  have hstable : (prefixWord ++ tailWord_3960638).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3960638).length < 2 ^ (prefixWord ++ tailWord_3960638).sum := by decide
  have hdescent : baseEnd_3960638 < baseStart_3960638 := by decide
  rcases family_descends (prefixWord ++ tailWord_3960638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3960649 : List Nat := [1, 2, 1, 1, 2, 4, 4, 7]
def baseStart_3960649 : Nat := 118140960795 + 3960649 * 2 ^ 59
def prefixEnd_3960649 : Nat := 4983230072969 + 3 ^ 40 * 3960649 * 2
def baseEnd_3960649 : Nat := 150645677092546642686875

theorem tailTrace_3960649 : CollatzResearch.WordTrace tailWord_3960649 prefixEnd_3960649 150645677092546642686875 := by
  unfold tailWord_3960649
  simp only [CollatzResearch.WordTrace]
  refine ⟨144456736628252572841365001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96304491085501715227576667 144456736628252572841365001)
  ·
    refine ⟨108342552471189429631023751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144456736628252572841365001 108342552471189429631023751)
    ·
      refine ⟨162513828706784144446535627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108342552471189429631023751 162513828706784144446535627)
      ·
        refine ⟨243770743060176216669803441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162513828706784144446535627 243770743060176216669803441)
        ·
          refine ⟨182828057295132162502352581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 243770743060176216669803441 182828057295132162502352581)
          ·
            refine ⟨34280260742837280469191109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 182828057295132162502352581 34280260742837280469191109)
            ·
              refine ⟨6427548889281990087973333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34280260742837280469191109 6427548889281990087973333)
              ·
                refine ⟨150645677092546642686875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6427548889281990087973333 150645677092546642686875)
                ·
                  rfl

theorem cell22_3960649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 4, 7].length) (baseStart_3960649 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3960649 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3960649 prefixEnd_3960649 := by exact prefixLift 3960649
  have htrace : WordTrace (prefixWord ++ tailWord_3960649) baseStart_3960649 baseEnd_3960649 := by
    simpa [prefixWord, tailWord_3960649, baseEnd_3960649] using wordTrace_append hprefix tailTrace_3960649
  have hstable : (prefixWord ++ tailWord_3960649).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3960649).length < 2 ^ (prefixWord ++ tailWord_3960649).sum := by decide
  have hdescent : baseEnd_3960649 < baseStart_3960649 := by decide
  rcases family_descends (prefixWord ++ tailWord_3960649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3960732 : List Nat := [2, 2, 3, 3, 1, 2, 2, 3, 1, 3]
def baseStart_3960732 : Nat := 118140960795 + 3960732 * 2 ^ 59
def prefixEnd_3960732 : Nat := 4983230072969 + 3 ^ 40 * 3960732 * 2
def baseEnd_3960732 : Nat := 1355839506429135234356621

theorem tailTrace_3960732 : CollatzResearch.WordTrace tailWord_3960732 prefixEnd_3960732 1355839506429135234356621 := by
  unfold tailWord_3960732
  simp only [CollatzResearch.WordTrace]
  refine ⟨72229881943475939008318225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96306509257967918677757633 72229881943475939008318225)
  ·
    refine ⟨54172411457606954256238669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72229881943475939008318225 54172411457606954256238669)
    ·
      refine ⟨20314654296602607846089501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54172411457606954256238669 20314654296602607846089501)
      ·
        refine ⟨7617995361225977942283563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20314654296602607846089501 7617995361225977942283563)
        ·
          refine ⟨11426993041838966913425345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7617995361225977942283563 11426993041838966913425345)
          ·
            refine ⟨8570244781379225185069009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11426993041838966913425345 8570244781379225185069009)
            ·
              refine ⟨6427683586034418888801757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8570244781379225185069009 6427683586034418888801757)
              ·
                refine ⟨2410381344762907083300659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6427683586034418888801757 2410381344762907083300659)
                ·
                  refine ⟨3615572017144360624950989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2410381344762907083300659 3615572017144360624950989)
                  ·
                    refine ⟨1355839506429135234356621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3615572017144360624950989 1355839506429135234356621)
                    ·
                      rfl

theorem cell22_3960732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 2, 3, 1, 3].length) (baseStart_3960732 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3960732 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3960732 prefixEnd_3960732 := by exact prefixLift 3960732
  have htrace : WordTrace (prefixWord ++ tailWord_3960732) baseStart_3960732 baseEnd_3960732 := by
    simpa [prefixWord, tailWord_3960732, baseEnd_3960732] using wordTrace_append hprefix tailTrace_3960732
  have hstable : (prefixWord ++ tailWord_3960732).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3960732).length < 2 ^ (prefixWord ++ tailWord_3960732).sum := by decide
  have hdescent : baseEnd_3960732 < baseStart_3960732 := by decide
  rcases family_descends (prefixWord ++ tailWord_3960732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3960739 : List Nat := [1, 1, 1, 4, 1, 2, 1, 1, 10]
def baseStart_3960739 : Nat := 118140960795 + 3960739 * 2 ^ 59
def prefixEnd_3960739 : Nat := 4983230072969 + 3 ^ 40 * 3960739 * 2
def baseEnd_3960739 : Nat := 451947300890729849810533

theorem tailTrace_3960739 : CollatzResearch.WordTrace tailWord_3960739 prefixEnd_3960739 451947300890729849810533 := by
  unfold tailWord_3960739
  simp only [CollatzResearch.WordTrace]
  refine ⟨144460019197926518212141271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96306679465284345474760847 144460019197926518212141271)
  ·
    refine ⟨216690028796889777318211907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144460019197926518212141271 216690028796889777318211907)
    ·
      refine ⟨325035043195334665977317861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216690028796889777318211907 325035043195334665977317861)
      ·
        refine ⟨60944070599125249870747099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 325035043195334665977317861 60944070599125249870747099)
        ·
          refine ⟨91416105898687874806120649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60944070599125249870747099 91416105898687874806120649)
          ·
            refine ⟨68562079424015906104590487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91416105898687874806120649 68562079424015906104590487)
            ·
              refine ⟨102843119136023859156885731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68562079424015906104590487 102843119136023859156885731)
              ·
                refine ⟨154264678704035788735328597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 102843119136023859156885731 154264678704035788735328597)
                ·
                  refine ⟨451947300890729849810533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 154264678704035788735328597 451947300890729849810533)
                  ·
                    rfl

theorem cell22_3960739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 1, 10].length) (baseStart_3960739 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3960739 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3960739 prefixEnd_3960739 := by exact prefixLift 3960739
  have htrace : WordTrace (prefixWord ++ tailWord_3960739) baseStart_3960739 baseEnd_3960739 := by
    simpa [prefixWord, tailWord_3960739, baseEnd_3960739] using wordTrace_append hprefix tailTrace_3960739
  have hstable : (prefixWord ++ tailWord_3960739).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3960739).length < 2 ^ (prefixWord ++ tailWord_3960739).sum := by decide
  have hdescent : baseEnd_3960739 < baseStart_3960739 := by decide
  rcases family_descends (prefixWord ++ tailWord_3960739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3960771 : List Nat := [1, 1, 1, 3, 1, 1, 2, 1, 8, 3]
def baseStart_3960771 : Nat := 118140960795 + 3960771 * 2 ^ 59
def prefixEnd_3960771 : Nat := 4983230072969 + 3 ^ 40 * 3960771 * 2
def baseEnd_3960771 : Nat := 1355852856926152132631501

theorem tailTrace_3960771 : CollatzResearch.WordTrace tailWord_3960771 prefixEnd_3960771 1355852856926152132631501 := by
  unfold tailWord_3960771
  simp only [CollatzResearch.WordTrace]
  refine ⟨144461186333810587677306167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96307457555873725118204111 144461186333810587677306167)
  ·
    refine ⟨216691779500715881515959251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144461186333810587677306167 216691779500715881515959251)
    ·
      refine ⟨325037669251073822273938877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216691779500715881515959251 325037669251073822273938877)
      ·
        refine ⟨121889125969152683352727079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 325037669251073822273938877 121889125969152683352727079)
        ·
          refine ⟨182833688953729025029090619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121889125969152683352727079 182833688953729025029090619)
          ·
            refine ⟨274250533430593537543635929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 182833688953729025029090619 274250533430593537543635929)
            ·
              refine ⟨205687900072945153157726947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 274250533430593537543635929 205687900072945153157726947)
              ·
                refine ⟨308531850109417729736590421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 205687900072945153157726947 308531850109417729736590421)
                ·
                  refine ⟨3615607618469739020350669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 308531850109417729736590421 3615607618469739020350669)
                  ·
                    refine ⟨1355852856926152132631501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3615607618469739020350669 1355852856926152132631501)
                    ·
                      rfl

theorem cell22_3960771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 1, 8, 3].length) (baseStart_3960771 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3960771 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3960771 prefixEnd_3960771 := by exact prefixLift 3960771
  have htrace : WordTrace (prefixWord ++ tailWord_3960771) baseStart_3960771 baseEnd_3960771 := by
    simpa [prefixWord, tailWord_3960771, baseEnd_3960771] using wordTrace_append hprefix tailTrace_3960771
  have hstable : (prefixWord ++ tailWord_3960771).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3960771).length < 2 ^ (prefixWord ++ tailWord_3960771).sum := by decide
  have hdescent : baseEnd_3960771 < baseStart_3960771 := by decide
  rcases family_descends (prefixWord ++ tailWord_3960771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3960788 : List Nat := [2, 4, 1, 2, 1, 1, 1, 1, 6, 3]
def baseStart_3960788 : Nat := 118140960795 + 3960788 * 2 ^ 59
def prefixEnd_3960788 : Nat := 4983230072969 + 3 ^ 40 * 3960788 * 2
def baseEnd_3960788 : Nat := 1355858676373569754956449

theorem tailTrace_3960788 : CollatzResearch.WordTrace tailWord_3960788 prefixEnd_3960788 1355858676373569754956449 := by
  unfold tailWord_3960788
  simp only [CollatzResearch.WordTrace]
  refine ⟨72230903187374499790337509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96307870916499333053783345 72230903187374499790337509)
  ·
    refine ⟨13543294347632718710688283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 72230903187374499790337509 13543294347632718710688283)
    ·
      refine ⟨20314941521449078066032425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13543294347632718710688283 20314941521449078066032425)
      ·
        refine ⟨15236206141086808549524319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20314941521449078066032425 15236206141086808549524319)
        ·
          refine ⟨22854309211630212824286479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15236206141086808549524319 22854309211630212824286479)
          ·
            refine ⟨34281463817445319236429719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22854309211630212824286479 34281463817445319236429719)
            ·
              refine ⟨51422195726167978854644579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34281463817445319236429719 51422195726167978854644579)
              ·
                refine ⟨77133293589251968281966869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51422195726167978854644579 77133293589251968281966869)
                ·
                  refine ⟨3615623136996186013217197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 77133293589251968281966869 3615623136996186013217197)
                  ·
                    refine ⟨1355858676373569754956449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3615623136996186013217197 1355858676373569754956449)
                    ·
                      rfl

theorem cell22_3960788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 1, 6, 3].length) (baseStart_3960788 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3960788 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3960788 prefixEnd_3960788 := by exact prefixLift 3960788
  have htrace : WordTrace (prefixWord ++ tailWord_3960788) baseStart_3960788 baseEnd_3960788 := by
    simpa [prefixWord, tailWord_3960788, baseEnd_3960788] using wordTrace_append hprefix tailTrace_3960788
  have hstable : (prefixWord ++ tailWord_3960788).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3960788).length < 2 ^ (prefixWord ++ tailWord_3960788).sum := by decide
  have hdescent : baseEnd_3960788 < baseStart_3960788 := by decide
  rcases family_descends (prefixWord ++ tailWord_3960788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3960803 : List Nat := [1, 1, 1, 6, 1, 3, 1, 2, 2, 4]
def baseStart_3960803 : Nat := 118140960795 + 3960803 * 2 ^ 59
def prefixEnd_3960803 : Nat := 4983230072969 + 3 ^ 40 * 3960803 * 2
def baseEnd_3960803 : Nat := 1355863811180114715831403

theorem tailTrace_3960803 : CollatzResearch.WordTrace tailWord_3960803 prefixEnd_3960803 1355863811180114715831403 := by
  unfold tailWord_3960803
  simp only [CollatzResearch.WordTrace]
  refine ⟨144462353469694657142471063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96308235646463104761647375 144462353469694657142471063)
  ·
    refine ⟨216693530204541985713706595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144462353469694657142471063 216693530204541985713706595)
    ·
      refine ⟨325040295306812978570559893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216693530204541985713706595 325040295306812978570559893)
      ·
        refine ⟨15236263842506858370494995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 325040295306812978570559893 15236263842506858370494995)
        ·
          refine ⟨22854395763760287555742493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15236263842506858370494995 22854395763760287555742493)
          ·
            refine ⟨8570398411410107833403435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22854395763760287555742493 8570398411410107833403435)
            ·
              refine ⟨12855597617115161750105153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8570398411410107833403435 12855597617115161750105153)
              ·
                refine ⟨9641698212836371312578865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12855597617115161750105153 9641698212836371312578865)
                ·
                  refine ⟨7231273659627278484434149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9641698212836371312578865 7231273659627278484434149)
                  ·
                    refine ⟨1355863811180114715831403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7231273659627278484434149 1355863811180114715831403)
                    ·
                      rfl

theorem cell22_3960803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 1, 2, 2, 4].length) (baseStart_3960803 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3960803 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3960803 prefixEnd_3960803 := by exact prefixLift 3960803
  have htrace : WordTrace (prefixWord ++ tailWord_3960803) baseStart_3960803 baseEnd_3960803 := by
    simpa [prefixWord, tailWord_3960803, baseEnd_3960803] using wordTrace_append hprefix tailTrace_3960803
  have hstable : (prefixWord ++ tailWord_3960803).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3960803).length < 2 ^ (prefixWord ++ tailWord_3960803).sum := by decide
  have hdescent : baseEnd_3960803 < baseStart_3960803 := by decide
  rcases family_descends (prefixWord ++ tailWord_3960803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3960807 : List Nat := [1, 1, 5, 2, 3, 1, 3, 2, 4]
def baseStart_3960807 : Nat := 118140960795 + 3960807 * 2 ^ 59
def prefixEnd_3960807 : Nat := 4983230072969 + 3 ^ 40 * 3960807 * 2
def baseEnd_3960807 : Nat := 451955060153953346243797

theorem tailTrace_3960807 : CollatzResearch.WordTrace tailWord_3960807 prefixEnd_3960807 451955060153953346243797 := by
  unfold tailWord_3960807
  simp only [CollatzResearch.WordTrace]
  refine ⟨144462499361680165825616675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96308332907786777217077783 144462499361680165825616675)
  ·
    refine ⟨216693749042520248738425013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144462499361680165825616675 216693749042520248738425013)
    ·
      refine ⟨20315038972736273319227345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 216693749042520248738425013 20315038972736273319227345)
      ·
        refine ⟨15236279229552204989420509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20315038972736273319227345 15236279229552204989420509)
        ·
          refine ⟨5713604711082076871032691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15236279229552204989420509 5713604711082076871032691)
          ·
            refine ⟨8570407066623115306549037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5713604711082076871032691 8570407066623115306549037)
            ·
              refine ⟨3213902649983668239955889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8570407066623115306549037 3213902649983668239955889)
              ·
                refine ⟨2410426987487751179966917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3213902649983668239955889 2410426987487751179966917)
                ·
                  refine ⟨451955060153953346243797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2410426987487751179966917 451955060153953346243797)
                  ·
                    rfl

theorem cell22_3960807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 3, 2, 4].length) (baseStart_3960807 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3960807 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3960807 prefixEnd_3960807 := by exact prefixLift 3960807
  have htrace : WordTrace (prefixWord ++ tailWord_3960807) baseStart_3960807 baseEnd_3960807 := by
    simpa [prefixWord, tailWord_3960807, baseEnd_3960807] using wordTrace_append hprefix tailTrace_3960807
  have hstable : (prefixWord ++ tailWord_3960807).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3960807).length < 2 ^ (prefixWord ++ tailWord_3960807).sum := by decide
  have hdescent : baseEnd_3960807 < baseStart_3960807 := by decide
  rcases family_descends (prefixWord ++ tailWord_3960807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3960822 : List Nat := [5, 1, 1, 1, 4, 1, 1, 3, 2, 3]
def baseStart_3960822 : Nat := 118140960795 + 3960822 * 2 ^ 59
def prefixEnd_3960822 : Nat := 4983230072969 + 3 ^ 40 * 3960822 * 2
def baseEnd_3960822 : Nat := 1355870315268404999606345

theorem tailTrace_3960822 : CollatzResearch.WordTrace tailWord_3960822 prefixEnd_3960822 1355870315268404999606345 := by
  unfold tailWord_3960822
  simp only [CollatzResearch.WordTrace]
  refine ⟨9028940403539113961713295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 96308697637750548924941813 9028940403539113961713295)
  ·
    refine ⟨13543410605308670942569943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9028940403539113961713295 13543410605308670942569943)
    ·
      refine ⟨20315115907963006413854915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13543410605308670942569943 20315115907963006413854915)
      ·
        refine ⟨30472673861944509620782373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20315115907963006413854915 30472673861944509620782373)
        ·
          refine ⟨5713626349114595553896695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30472673861944509620782373 5713626349114595553896695)
          ·
            refine ⟨8570439523671893330845043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5713626349114595553896695 8570439523671893330845043)
            ·
              refine ⟨12855659285507839996267565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8570439523671893330845043 12855659285507839996267565)
              ·
                refine ⟨4820872232065439998600337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12855659285507839996267565 4820872232065439998600337)
                ·
                  refine ⟨3615654174049079998950253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4820872232065439998600337 3615654174049079998950253)
                  ·
                    refine ⟨1355870315268404999606345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3615654174049079998950253 1355870315268404999606345)
                    ·
                      rfl

theorem cell22_3960822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 1, 3, 2, 3].length) (baseStart_3960822 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3960822 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3960822 prefixEnd_3960822 := by exact prefixLift 3960822
  have htrace : WordTrace (prefixWord ++ tailWord_3960822) baseStart_3960822 baseEnd_3960822 := by
    simpa [prefixWord, tailWord_3960822, baseEnd_3960822] using wordTrace_append hprefix tailTrace_3960822
  have hstable : (prefixWord ++ tailWord_3960822).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3960822).length < 2 ^ (prefixWord ++ tailWord_3960822).sum := by decide
  have hdescent : baseEnd_3960822 < baseStart_3960822 := by decide
  rcases family_descends (prefixWord ++ tailWord_3960822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3960833 : List Nat := [1, 2, 4, 1, 2, 1, 2, 1, 5, 3]
def baseStart_3960833 : Nat := 118140960795 + 3960833 * 2 ^ 59
def prefixEnd_3960833 : Nat := 4983230072969 + 3 ^ 40 * 3960833 * 2
def baseEnd_3960833 : Nat := 1355874080793204637581311

theorem tailTrace_3960833 : CollatzResearch.WordTrace tailWord_3960833 prefixEnd_3960833 1355874080793204637581311 := by
  unfold tailWord_3960833
  simp only [CollatzResearch.WordTrace]
  refine ⟨144463447659585972266063153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96308965106390648177375435 144463447659585972266063153)
  ·
    refine ⟨108347585744689479199547365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144463447659585972266063153 108347585744689479199547365)
    ·
      refine ⟨20315172327129277349915131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 108347585744689479199547365 20315172327129277349915131)
      ·
        refine ⟨30472758490693916024872697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20315172327129277349915131 30472758490693916024872697)
        ·
          refine ⟨22854568868020437018654523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30472758490693916024872697 22854568868020437018654523)
          ·
            refine ⟨34281853302030655527981785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22854568868020437018654523 34281853302030655527981785)
            ·
              refine ⟨25711389976522991645986339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34281853302030655527981785 25711389976522991645986339)
              ·
                refine ⟨38567084964784487468979509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25711389976522991645986339 38567084964784487468979509)
                ·
                  refine ⟨3615664215448545700216829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 38567084964784487468979509 3615664215448545700216829)
                  ·
                    refine ⟨1355874080793204637581311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3615664215448545700216829 1355874080793204637581311)
                    ·
                      rfl

theorem cell22_3960833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 2, 1, 5, 3].length) (baseStart_3960833 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3960833 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3960833 prefixEnd_3960833 := by exact prefixLift 3960833
  have htrace : WordTrace (prefixWord ++ tailWord_3960833) baseStart_3960833 baseEnd_3960833 := by
    simpa [prefixWord, tailWord_3960833, baseEnd_3960833] using wordTrace_append hprefix tailTrace_3960833
  have hstable : (prefixWord ++ tailWord_3960833).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3960833).length < 2 ^ (prefixWord ++ tailWord_3960833).sum := by decide
  have hdescent : baseEnd_3960833 < baseStart_3960833 := by decide
  rcases family_descends (prefixWord ++ tailWord_3960833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3960863 : List Nat := [1, 1, 2, 4, 1, 2, 4, 2, 5]
def baseStart_3960863 : Nat := 118140960795 + 3960863 * 2 ^ 59
def prefixEnd_3960863 : Nat := 4983230072969 + 3 ^ 40 * 3960863 * 2
def baseEnd_3960863 : Nat := 451961450135431519777073

theorem tailTrace_3960863 : CollatzResearch.WordTrace tailWord_3960863 prefixEnd_3960863 451961450135431519777073 := by
  unfold tailWord_3960863
  simp only [CollatzResearch.WordTrace]
  refine ⟨144464541849477287389655243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96309694566318191593103495 144464541849477287389655243)
  ·
    refine ⟨216696812774215931084482865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144464541849477287389655243 216696812774215931084482865)
    ·
      refine ⟨162522609580661948313362149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 216696812774215931084482865 162522609580661948313362149)
      ·
        refine ⟨30472989296374115308755403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 162522609580661948313362149 30472989296374115308755403)
        ·
          refine ⟨45709483944561172963133105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30472989296374115308755403 45709483944561172963133105)
          ·
            refine ⟨34282112958420879722349829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45709483944561172963133105 34282112958420879722349829)
            ·
              refine ⟨6427896179703914947940593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34282112958420879722349829 6427896179703914947940593)
              ·
                refine ⟨4820922134777936210955445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6427896179703914947940593 4820922134777936210955445)
                ·
                  refine ⟨451961450135431519777073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4820922134777936210955445 451961450135431519777073)
                  ·
                    rfl

theorem cell22_3960863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 4, 2, 5].length) (baseStart_3960863 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3960863 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3960863 prefixEnd_3960863 := by exact prefixLift 3960863
  have htrace : WordTrace (prefixWord ++ tailWord_3960863) baseStart_3960863 baseEnd_3960863 := by
    simpa [prefixWord, tailWord_3960863, baseEnd_3960863] using wordTrace_append hprefix tailTrace_3960863
  have hstable : (prefixWord ++ tailWord_3960863).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3960863).length < 2 ^ (prefixWord ++ tailWord_3960863).sum := by decide
  have hdescent : baseEnd_3960863 < baseStart_3960863 := by decide
  rcases family_descends (prefixWord ++ tailWord_3960863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3960878 : List Nat := [4, 1, 3, 1, 1, 2, 1, 1, 1, 7]
def baseStart_3960878 : Nat := 118140960795 + 3960878 * 2 ^ 59
def prefixEnd_3960878 : Nat := 4983230072969 + 3 ^ 40 * 3960878 * 2
def baseEnd_3960878 : Nat := 1355889485212839520206173

theorem tailTrace_3960878 : CollatzResearch.WordTrace tailWord_3960878 prefixEnd_3960878 1355889485212839520206173 := by
  unfold tailWord_3960878
  simp only [CollatzResearch.WordTrace]
  refine ⟨18058136118052868118931411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 96310059296281963300967525 18058136118052868118931411)
  ·
    refine ⟨27087204177079302178397117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18058136118052868118931411 27087204177079302178397117)
    ·
      refine ⟨10157701566404738316898919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27087204177079302178397117 10157701566404738316898919)
      ·
        refine ⟨15236552349607107475348379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10157701566404738316898919 15236552349607107475348379)
        ·
          refine ⟨22854828524410661213022569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15236552349607107475348379 22854828524410661213022569)
          ·
            refine ⟨17141121393307995909766927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22854828524410661213022569 17141121393307995909766927)
            ·
              refine ⟨25711682089961993864650391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17141121393307995909766927 25711682089961993864650391)
              ·
                refine ⟨38567523134942990796975587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25711682089961993864650391 38567523134942990796975587)
                ·
                  refine ⟨57851284702414486195463381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38567523134942990796975587 57851284702414486195463381)
                  ·
                    refine ⟨1355889485212839520206173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 57851284702414486195463381 1355889485212839520206173)
                    ·
                      rfl

theorem cell22_3960878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 1, 1, 1, 7].length) (baseStart_3960878 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3960878 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3960878 prefixEnd_3960878 := by exact prefixLift 3960878
  have htrace : WordTrace (prefixWord ++ tailWord_3960878) baseStart_3960878 baseEnd_3960878 := by
    simpa [prefixWord, tailWord_3960878, baseEnd_3960878] using wordTrace_append hprefix tailTrace_3960878
  have hstable : (prefixWord ++ tailWord_3960878).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3960878).length < 2 ^ (prefixWord ++ tailWord_3960878).sum := by decide
  have hdescent : baseEnd_3960878 < baseStart_3960878 := by decide
  rcases family_descends (prefixWord ++ tailWord_3960878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3960891 : List Nat := [1, 1, 1, 1, 1, 2, 1, 8, 6]
def baseStart_3960891 : Nat := 118140960795 + 3960891 * 2 ^ 59
def prefixEnd_3960891 : Nat := 4983230072969 + 3 ^ 40 * 3960891 * 2
def baseEnd_3960891 : Nat := 451964645126170606543711

theorem tailTrace_3960891 : CollatzResearch.WordTrace tailWord_3960891 prefixEnd_3960891 451964645126170606543711 := by
  unfold tailWord_3960891
  simp only [CollatzResearch.WordTrace]
  refine ⟨144465563093375848171674527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96310375395583898781116351 144465563093375848171674527)
  ·
    refine ⟨216698344640063772257511791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144465563093375848171674527 216698344640063772257511791)
    ·
      refine ⟨325047516960095658386267687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216698344640063772257511791 325047516960095658386267687)
      ·
        refine ⟨487571275440143487579401531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 325047516960095658386267687 487571275440143487579401531)
        ·
          refine ⟨731356913160215231369102297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 487571275440143487579401531 731356913160215231369102297)
          ·
            refine ⟨548517684870161423526826723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 731356913160215231369102297 548517684870161423526826723)
            ·
              refine ⟨822776527305242135290240085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 548517684870161423526826723 822776527305242135290240085)
              ·
                refine ⟨9641912429358306272932501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 822776527305242135290240085 9641912429358306272932501)
                ·
                  refine ⟨451964645126170606543711, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9641912429358306272932501 451964645126170606543711)
                  ·
                    rfl

theorem cell22_3960891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 8, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 8, 6].length) (baseStart_3960891 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3960891 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3960891 prefixEnd_3960891 := by exact prefixLift 3960891
  have htrace : WordTrace (prefixWord ++ tailWord_3960891) baseStart_3960891 baseEnd_3960891 := by
    simpa [prefixWord, tailWord_3960891, baseEnd_3960891] using wordTrace_append hprefix tailTrace_3960891
  have hstable : (prefixWord ++ tailWord_3960891).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3960891).length < 2 ^ (prefixWord ++ tailWord_3960891).sum := by decide
  have hdescent : baseEnd_3960891 < baseStart_3960891 := by decide
  rcases family_descends (prefixWord ++ tailWord_3960891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3960893 : List Nat := [1, 4, 1, 3, 1, 1, 1, 3, 3, 4]
def baseStart_3960893 : Nat := 118140960795 + 3960893 * 2 ^ 59
def prefixEnd_3960893 : Nat := 4983230072969 + 3 ^ 40 * 3960893 * 2
def baseEnd_3960893 : Nat := 1355894620019384481081127

theorem tailTrace_3960893 : CollatzResearch.WordTrace tailWord_3960893 prefixEnd_3960893 1355894620019384481081127 := by
  unfold tailWord_3960893
  simp only [CollatzResearch.WordTrace]
  refine ⟨144465636039368602513247333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96310424026245735008831555 144465636039368602513247333)
  ·
    refine ⟨27087306757381612971233875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 144465636039368602513247333 27087306757381612971233875)
    ·
      refine ⟨40630960136072419456850813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27087306757381612971233875 40630960136072419456850813)
      ·
        refine ⟨15236610051027157296319055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40630960136072419456850813 15236610051027157296319055)
        ·
          refine ⟨22854915076540735944478583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15236610051027157296319055 22854915076540735944478583)
          ·
            refine ⟨34282372614811103916717875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22854915076540735944478583 34282372614811103916717875)
            ·
              refine ⟨51423558922216655875076813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34282372614811103916717875 51423558922216655875076813)
              ·
                refine ⟨19283834595831245953153805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51423558922216655875076813 19283834595831245953153805)
                ·
                  refine ⟨7231437973436717232432677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19283834595831245953153805 7231437973436717232432677)
                  ·
                    refine ⟨1355894620019384481081127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7231437973436717232432677 1355894620019384481081127)
                    ·
                      rfl

theorem cell22_3960893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 3, 3, 4].length) (baseStart_3960893 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3960893 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3960893 prefixEnd_3960893 := by exact prefixLift 3960893
  have htrace : WordTrace (prefixWord ++ tailWord_3960893) baseStart_3960893 baseEnd_3960893 := by
    simpa [prefixWord, tailWord_3960893, baseEnd_3960893] using wordTrace_append hprefix tailTrace_3960893
  have hstable : (prefixWord ++ tailWord_3960893).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3960893).length < 2 ^ (prefixWord ++ tailWord_3960893).sum := by decide
  have hdescent : baseEnd_3960893 < baseStart_3960893 := by decide
  rcases family_descends (prefixWord ++ tailWord_3960893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3960910 : List Nat := [4, 1, 1, 1, 1, 5, 1, 3, 1, 4]
def baseStart_3960910 : Nat := 118140960795 + 3960910 * 2 ^ 59
def prefixEnd_3960910 : Nat := 4983230072969 + 3 ^ 40 * 3960910 * 2
def baseEnd_3960910 : Nat := 1355900439466802103406075

theorem tailTrace_3960910 : CollatzResearch.WordTrace tailWord_3960910 prefixEnd_3960910 1355900439466802103406075 := by
  unfold tailWord_3960910
  simp only [CollatzResearch.WordTrace]
  refine ⟨18058282010038376802077023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 96310837386871342944410789 18058282010038376802077023)
  ·
    refine ⟨27087423015057565203115535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18058282010038376802077023 27087423015057565203115535)
    ·
      refine ⟨40631134522586347804673303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27087423015057565203115535 40631134522586347804673303)
      ·
        refine ⟨60946701783879521707009955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40631134522586347804673303 60946701783879521707009955)
        ·
          refine ⟨91420052675819282560514933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60946701783879521707009955 91420052675819282560514933)
          ·
            refine ⟨8570629938358057740048275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 91420052675819282560514933 8570629938358057740048275)
            ·
              refine ⟨12855944907537086610072413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8570629938358057740048275 12855944907537086610072413)
              ·
                refine ⟨4820979340326407478777155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12855944907537086610072413 4820979340326407478777155)
                ·
                  refine ⟨7231469010489611218165733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4820979340326407478777155 7231469010489611218165733)
                  ·
                    refine ⟨1355900439466802103406075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7231469010489611218165733 1355900439466802103406075)
                    ·
                      rfl

theorem cell22_3960910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 1, 3, 1, 4].length) (baseStart_3960910 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3960910 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3960910 prefixEnd_3960910 := by exact prefixLift 3960910
  have htrace : WordTrace (prefixWord ++ tailWord_3960910) baseStart_3960910 baseEnd_3960910 := by
    simpa [prefixWord, tailWord_3960910, baseEnd_3960910] using wordTrace_append hprefix tailTrace_3960910
  have hstable : (prefixWord ++ tailWord_3960910).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3960910).length < 2 ^ (prefixWord ++ tailWord_3960910).sum := by decide
  have hdescent : baseEnd_3960910 < baseStart_3960910 := by decide
  rcases family_descends (prefixWord ++ tailWord_3960910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3960925 : List Nat := [1, 4, 4, 1, 1, 1, 1, 3, 6]
def baseStart_3960925 : Nat := 118140960795 + 3960925 * 2 ^ 59
def prefixEnd_3960925 : Nat := 4983230072969 + 3 ^ 40 * 3960925 * 2
def baseEnd_3960925 : Nat := 451968524757782354760343

theorem tailTrace_3960925 : CollatzResearch.WordTrace tailWord_3960925 prefixEnd_3960925 451968524757782354760343 := by
  unfold tailWord_3960925
  simp only [CollatzResearch.WordTrace]
  refine ⟨144466803175252671978412229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96311202116835114652274819 144466803175252671978412229)
  ·
    refine ⟨27087525595359875995952293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 144466803175252671978412229 27087525595359875995952293)
    ·
      refine ⟨5078911049129976749241055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27087525595359875995952293 5078911049129976749241055)
      ·
        refine ⟨7618366573694965123861583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5078911049129976749241055 7618366573694965123861583)
        ·
          refine ⟨11427549860542447685792375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7618366573694965123861583 11427549860542447685792375)
          ·
            refine ⟨17141324790813671528688563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11427549860542447685792375 17141324790813671528688563)
            ·
              refine ⟨25711987186220507293032845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17141324790813671528688563 25711987186220507293032845)
              ·
                refine ⟨9641995194832690234887317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25711987186220507293032845 9641995194832690234887317)
                ·
                  refine ⟨451968524757782354760343, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9641995194832690234887317 451968524757782354760343)
                  ·
                    rfl

theorem cell22_3960925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 1, 3, 6].length) (baseStart_3960925 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3960925 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3960925 prefixEnd_3960925 := by exact prefixLift 3960925
  have htrace : WordTrace (prefixWord ++ tailWord_3960925) baseStart_3960925 baseEnd_3960925 := by
    simpa [prefixWord, tailWord_3960925, baseEnd_3960925] using wordTrace_append hprefix tailTrace_3960925
  have hstable : (prefixWord ++ tailWord_3960925).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3960925).length < 2 ^ (prefixWord ++ tailWord_3960925).sum := by decide
  have hdescent : baseEnd_3960925 < baseStart_3960925 := by decide
  rcases family_descends (prefixWord ++ tailWord_3960925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3960940 : List Nat := [2, 2, 1, 1, 3, 5, 1, 1, 1, 5]
def baseStart_3960940 : Nat := 118140960795 + 3960940 * 2 ^ 59
def prefixEnd_3960940 : Nat := 4983230072969 + 3 ^ 40 * 3960940 * 2
def baseEnd_3960940 : Nat := 1355910709079892025155983

theorem tailTrace_3960940 : CollatzResearch.WordTrace tailWord_3960940 prefixEnd_3960940 1355910709079892025155983 := by
  unfold tailWord_3960940
  simp only [CollatzResearch.WordTrace]
  refine ⟨72233675135099164770104137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96311566846798886360138849 72233675135099164770104137)
  ·
    refine ⟨54175256351324373577578103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72233675135099164770104137 54175256351324373577578103)
    ·
      refine ⟨81262884526986560366367155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54175256351324373577578103 81262884526986560366367155)
      ·
        refine ⟨121894326790479840549550733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81262884526986560366367155 121894326790479840549550733)
        ·
          refine ⟨45710372546429940206081525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 121894326790479840549550733 45710372546429940206081525)
          ·
            refine ⟨4285347426227806894320143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 45710372546429940206081525 4285347426227806894320143)
            ·
              refine ⟨6428021139341710341480215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4285347426227806894320143 6428021139341710341480215)
              ·
                refine ⟨9642031709012565512220323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6428021139341710341480215 9642031709012565512220323)
                ·
                  refine ⟨14463047563518848268330485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9642031709012565512220323 14463047563518848268330485)
                  ·
                    refine ⟨1355910709079892025155983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14463047563518848268330485 1355910709079892025155983)
                    ·
                      rfl

theorem cell22_3960940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 5].length) (baseStart_3960940 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3960940 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3960940 prefixEnd_3960940 := by exact prefixLift 3960940
  have htrace : WordTrace (prefixWord ++ tailWord_3960940) baseStart_3960940 baseEnd_3960940 := by
    simpa [prefixWord, tailWord_3960940, baseEnd_3960940] using wordTrace_append hprefix tailTrace_3960940
  have hstable : (prefixWord ++ tailWord_3960940).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3960940).length < 2 ^ (prefixWord ++ tailWord_3960940).sum := by decide
  have hdescent : baseEnd_3960940 < baseStart_3960940 := by decide
  rcases family_descends (prefixWord ++ tailWord_3960940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3960953 : List Nat := [1, 2, 1, 3, 4, 2, 1, 8]
def baseStart_3960953 : Nat := 118140960795 + 3960953 * 2 ^ 59
def prefixEnd_3960953 : Nat := 4983230072969 + 3 ^ 40 * 3960953 * 2
def baseEnd_3960953 : Nat := 150657239916173813842327

theorem tailTrace_3960953 : CollatzResearch.WordTrace tailWord_3960953 prefixEnd_3960953 150657239916173813842327 := by
  unfold tailWord_3960953
  simp only [CollatzResearch.WordTrace]
  refine ⟨144467824419151232760431513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96311882946100821840287675 144467824419151232760431513)
  ·
    refine ⟨108350868314363424570323635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144467824419151232760431513 108350868314363424570323635)
    ·
      refine ⟨162526302471545136855485453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108350868314363424570323635 162526302471545136855485453)
      ·
        refine ⟨60947363426829426320807045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 162526302471545136855485453 60947363426829426320807045)
        ·
          refine ⟨11427630642530517435151321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 60947363426829426320807045 11427630642530517435151321)
          ·
            refine ⟨8570722981897888076363491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11427630642530517435151321 8570722981897888076363491)
            ·
              refine ⟨12856084472846832114545237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8570722981897888076363491 12856084472846832114545237)
              ·
                refine ⟨150657239916173813842327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12856084472846832114545237 150657239916173813842327)
                ·
                  rfl

theorem cell22_3960953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 1, 8].length) (baseStart_3960953 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3960953 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3960953 prefixEnd_3960953 := by exact prefixLift 3960953
  have htrace : WordTrace (prefixWord ++ tailWord_3960953) baseStart_3960953 baseEnd_3960953 := by
    simpa [prefixWord, tailWord_3960953, baseEnd_3960953] using wordTrace_append hprefix tailTrace_3960953
  have hstable : (prefixWord ++ tailWord_3960953).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3960953).length < 2 ^ (prefixWord ++ tailWord_3960953).sum := by decide
  have hdescent : baseEnd_3960953 < baseStart_3960953 := by decide
  rcases family_descends (prefixWord ++ tailWord_3960953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3961036 : List Nat := [2, 2, 1, 6, 1, 1, 1, 4, 1, 3]
def baseStart_3961036 : Nat := 118140960795 + 3961036 * 2 ^ 59
def prefixEnd_3961036 : Nat := 4983230072969 + 3 ^ 40 * 3961036 * 2
def baseEnd_3961036 : Nat := 1355943571841779774755689

theorem tailTrace_3961036 : CollatzResearch.WordTrace tailWord_3961036 prefixEnd_3961036 1355943571841779774755689 := by
  unfold tailWord_3961036
  simp only [CollatzResearch.WordTrace]
  refine ⟨72235425838925268967851481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96313901118567025290468641 72235425838925268967851481)
  ·
    refine ⟨54176569379193951725888611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72235425838925268967851481 54176569379193951725888611)
    ·
      refine ⟨81264854068790927588832917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54176569379193951725888611 81264854068790927588832917)
      ·
        refine ⟨3809290034474574730726543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 81264854068790927588832917 3809290034474574730726543)
        ·
          refine ⟨5713935051711862096089815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3809290034474574730726543 5713935051711862096089815)
          ·
            refine ⟨8570902577567793144134723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5713935051711862096089815 8570902577567793144134723)
            ·
              refine ⟨12856353866351689716202085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8570902577567793144134723 12856353866351689716202085)
              ·
                refine ⟨2410566349940941821787891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12856353866351689716202085 2410566349940941821787891)
                ·
                  refine ⟨3615849524911412732681837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2410566349940941821787891 3615849524911412732681837)
                  ·
                    refine ⟨1355943571841779774755689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3615849524911412732681837 1355943571841779774755689)
                    ·
                      rfl

theorem cell22_3961036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 1, 4, 1, 3].length) (baseStart_3961036 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3961036 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3961036 prefixEnd_3961036 := by exact prefixLift 3961036
  have htrace : WordTrace (prefixWord ++ tailWord_3961036) baseStart_3961036 baseEnd_3961036 := by
    simpa [prefixWord, tailWord_3961036, baseEnd_3961036] using wordTrace_append hprefix tailTrace_3961036
  have hstable : (prefixWord ++ tailWord_3961036).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3961036).length < 2 ^ (prefixWord ++ tailWord_3961036).sum := by decide
  have hdescent : baseEnd_3961036 < baseStart_3961036 := by decide
  rcases family_descends (prefixWord ++ tailWord_3961036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3961075 : List Nat := [1, 1, 1, 2, 2, 4, 2, 2, 4, 3]
def baseStart_3961075 : Nat := 118140960795 + 3961075 * 2 ^ 59
def prefixEnd_3961075 : Nat := 4983230072969 + 3 ^ 40 * 3961075 * 2
def baseEnd_3961075 : Nat := 1355956922338796673030569

theorem tailTrace_3961075 : CollatzResearch.WordTrace tailWord_3961075 prefixEnd_3961075 1355956922338796673030569 := by
  unfold tailWord_3961075
  simp only [CollatzResearch.WordTrace]
  refine ⟨144472274124709247596372679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96314849416472831730915119 144472274124709247596372679)
  ·
    refine ⟨216708411187063871394559019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144472274124709247596372679 216708411187063871394559019)
    ·
      refine ⟨325062616780595807091838529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216708411187063871394559019 325062616780595807091838529)
      ·
        refine ⟨243796962585446855318878897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 325062616780595807091838529 243796962585446855318878897)
        ·
          refine ⟨182847721939085141489159173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 243796962585446855318878897 182847721939085141489159173)
          ·
            refine ⟨34283947863578464029217345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 182847721939085141489159173 34283947863578464029217345)
            ·
              refine ⟨25712960897683848021913009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34283947863578464029217345 25712960897683848021913009)
              ·
                refine ⟨19284720673262886016434757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25712960897683848021913009 19284720673262886016434757)
                ·
                  refine ⟨3615885126236791128081517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19284720673262886016434757 3615885126236791128081517)
                  ·
                    refine ⟨1355956922338796673030569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3615885126236791128081517 1355956922338796673030569)
                    ·
                      rfl

theorem cell22_3961075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 2, 2, 4, 3].length) (baseStart_3961075 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3961075 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3961075 prefixEnd_3961075 := by exact prefixLift 3961075
  have htrace : WordTrace (prefixWord ++ tailWord_3961075) baseStart_3961075 baseEnd_3961075 := by
    simpa [prefixWord, tailWord_3961075, baseEnd_3961075] using wordTrace_append hprefix tailTrace_3961075
  have hstable : (prefixWord ++ tailWord_3961075).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3961075).length < 2 ^ (prefixWord ++ tailWord_3961075).sum := by decide
  have hdescent : baseEnd_3961075 < baseStart_3961075 := by decide
  rcases family_descends (prefixWord ++ tailWord_3961075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3961122 : List Nat := [3, 3, 1, 1, 3, 1, 4, 6]
def baseStart_3961122 : Nat := 118140960795 + 3961122 * 2 ^ 59
def prefixEnd_3961122 : Nat := 4983230072969 + 3 ^ 40 * 3961122 * 2
def baseEnd_3961122 : Nat := 150663667933256024122825

theorem tailTrace_3961122 : CollatzResearch.WordTrace tailWord_3961122 prefixEnd_3961122 150663667933256024122825 := by
  unfold tailWord_3961122
  simp only [CollatzResearch.WordTrace]
  refine ⟨36118497088884743655833405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96315992237025983082222413 36118497088884743655833405)
  ·
    refine ⟨13544436408331778870937527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36118497088884743655833405 13544436408331778870937527)
    ·
      refine ⟨20316654612497668306406291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13544436408331778870937527 20316654612497668306406291)
      ·
        refine ⟨30474981918746502459609437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20316654612497668306406291 30474981918746502459609437)
        ·
          refine ⟨11428118219529938422353539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30474981918746502459609437 11428118219529938422353539)
          ·
            refine ⟨17142177329294907633530309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11428118219529938422353539 17142177329294907633530309)
            ·
              refine ⟨3214158249242795181286933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17142177329294907633530309 3214158249242795181286933)
              ·
                refine ⟨150663667933256024122825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3214158249242795181286933 150663667933256024122825)
                ·
                  rfl

theorem cell22_3961122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 4, 6].length) (baseStart_3961122 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3961122 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3961122 prefixEnd_3961122 := by exact prefixLift 3961122
  have htrace : WordTrace (prefixWord ++ tailWord_3961122) baseStart_3961122 baseEnd_3961122 := by
    simpa [prefixWord, tailWord_3961122, baseEnd_3961122] using wordTrace_append hprefix tailTrace_3961122
  have hstable : (prefixWord ++ tailWord_3961122).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3961122).length < 2 ^ (prefixWord ++ tailWord_3961122).sum := by decide
  have hdescent : baseEnd_3961122 < baseStart_3961122 := by decide
  rcases family_descends (prefixWord ++ tailWord_3961122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3961227 : List Nat := [1, 1, 1, 1, 4, 5, 2, 1, 1, 5]
def baseStart_3961227 : Nat := 118140960795 + 3961227 * 2 ^ 59
def prefixEnd_3961227 : Nat := 4983230072969 + 3 ^ 40 * 3961227 * 2
def baseEnd_3961227 : Nat := 1356008955045118943230103

theorem tailTrace_3961227 : CollatzResearch.WordTrace tailWord_3961227 prefixEnd_3961227 1356008955045118943230103 := by
  unfold tailWord_3961227
  simp only [CollatzResearch.WordTrace]
  refine ⟨144477818020158577555905935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96318545346772385037270623 144477818020158577555905935)
  ·
    refine ⟨216716727030237866333858903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144477818020158577555905935 216716727030237866333858903)
    ·
      refine ⟨325075090545356799500788355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216716727030237866333858903 325075090545356799500788355)
      ·
        refine ⟨487612635818035199251182533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 325075090545356799500788355 487612635818035199251182533)
        ·
          refine ⟨91427369215881599859596725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 487612635818035199251182533 91427369215881599859596725)
          ·
            refine ⟨8571315863988899986837193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 91427369215881599859596725 8571315863988899986837193)
            ·
              refine ⟨6428486897991674990127895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8571315863988899986837193 6428486897991674990127895)
              ·
                refine ⟨9642730346987512485191843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6428486897991674990127895 9642730346987512485191843)
                ·
                  refine ⟨14464095520481268727787765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9642730346987512485191843 14464095520481268727787765)
                  ·
                    refine ⟨1356008955045118943230103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14464095520481268727787765 1356008955045118943230103)
                    ·
                      rfl

theorem cell22_3961227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 2, 1, 1, 5].length) (baseStart_3961227 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3961227 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3961227 prefixEnd_3961227 := by exact prefixLift 3961227
  have htrace : WordTrace (prefixWord ++ tailWord_3961227) baseStart_3961227 baseEnd_3961227 := by
    simpa [prefixWord, tailWord_3961227, baseEnd_3961227] using wordTrace_append hprefix tailTrace_3961227
  have hstable : (prefixWord ++ tailWord_3961227).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3961227).length < 2 ^ (prefixWord ++ tailWord_3961227).sum := by decide
  have hdescent : baseEnd_3961227 < baseStart_3961227 := by decide
  rcases family_descends (prefixWord ++ tailWord_3961227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3961242 : List Nat := [3, 1, 1, 4, 1, 3, 1, 1, 1, 6]
def baseStart_3961242 : Nat := 118140960795 + 3961242 * 2 ^ 59
def prefixEnd_3961242 : Nat := 4983230072969 + 3 ^ 40 * 3961242 * 2
def baseEnd_3961242 : Nat := 1356014089851663904105057

theorem tailTrace_3961242 : CollatzResearch.WordTrace tailWord_3961242 prefixEnd_3961242 1356014089851663904105057 := by
  unfold tailWord_3961242
  simp only [CollatzResearch.WordTrace]
  refine ⟨36119591278776058779425495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96318910076736156745134653 36119591278776058779425495)
  ·
    refine ⟨54179386918164088169138243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36119591278776058779425495 54179386918164088169138243)
    ·
      refine ⟨81269080377246132253707365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54179386918164088169138243 81269080377246132253707365)
      ·
        refine ⟨15237952570733649797570131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 81269080377246132253707365 15237952570733649797570131)
        ·
          refine ⟨22856928856100474696355197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15237952570733649797570131 22856928856100474696355197)
          ·
            refine ⟨8571348321037678011133199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22856928856100474696355197 8571348321037678011133199)
            ·
              refine ⟨12857022481556517016699799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8571348321037678011133199 12857022481556517016699799)
              ·
                refine ⟨19285533722334775525049699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12857022481556517016699799 19285533722334775525049699)
                ·
                  refine ⟨28928300583502163287574549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19285533722334775525049699 28928300583502163287574549)
                  ·
                    refine ⟨1356014089851663904105057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28928300583502163287574549 1356014089851663904105057)
                    ·
                      rfl

theorem cell22_3961242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 1, 1, 1, 6].length) (baseStart_3961242 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3961242 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3961242 prefixEnd_3961242 := by exact prefixLift 3961242
  have htrace : WordTrace (prefixWord ++ tailWord_3961242) baseStart_3961242 baseEnd_3961242 := by
    simpa [prefixWord, tailWord_3961242, baseEnd_3961242] using wordTrace_append hprefix tailTrace_3961242
  have hstable : (prefixWord ++ tailWord_3961242).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3961242).length < 2 ^ (prefixWord ++ tailWord_3961242).sum := by decide
  have hdescent : baseEnd_3961242 < baseStart_3961242 := by decide
  rcases family_descends (prefixWord ++ tailWord_3961242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3961246 : List Nat := [4, 3, 1, 2, 1, 1, 1, 5, 4]
def baseStart_3961246 : Nat := 118140960795 + 3961246 * 2 ^ 59
def prefixEnd_3961246 : Nat := 4983230072969 + 3 ^ 40 * 3961246 * 2
def baseEnd_3961246 : Nat := 452005153044469742335015

theorem tailTrace_3961246 : CollatzResearch.WordTrace tailWord_3961246 prefixEnd_3961246 452005153044469742335015 := by
  unfold tailWord_3961246
  simp only [CollatzResearch.WordTrace]
  refine ⟨18059813875886217975105949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 96319007338059829200565061 18059813875886217975105949)
  ·
    refine ⟨6772430203457331740664731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18059813875886217975105949 6772430203457331740664731)
    ·
      refine ⟨10158645305185997610997097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6772430203457331740664731 10158645305185997610997097)
      ·
        refine ⟨7618983978889498208247823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10158645305185997610997097 7618983978889498208247823)
        ·
          refine ⟨11428475968334247312371735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7618983978889498208247823 11428475968334247312371735)
          ·
            refine ⟨17142713952501370968557603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11428475968334247312371735 17142713952501370968557603)
            ·
              refine ⟨25714070928752056452836405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17142713952501370968557603 25714070928752056452836405)
              ·
                refine ⟨2410694149570505292453413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 25714070928752056452836405 2410694149570505292453413)
                ·
                  refine ⟨452005153044469742335015, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2410694149570505292453413 452005153044469742335015)
                  ·
                    rfl

theorem cell22_3961246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 1, 5, 4].length) (baseStart_3961246 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3961246 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3961246 prefixEnd_3961246 := by exact prefixLift 3961246
  have htrace : WordTrace (prefixWord ++ tailWord_3961246) baseStart_3961246 baseEnd_3961246 := by
    simpa [prefixWord, tailWord_3961246, baseEnd_3961246] using wordTrace_append hprefix tailTrace_3961246
  have hstable : (prefixWord ++ tailWord_3961246).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3961246).length < 2 ^ (prefixWord ++ tailWord_3961246).sum := by decide
  have hdescent : baseEnd_3961246 < baseStart_3961246 := by decide
  rcases family_descends (prefixWord ++ tailWord_3961246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3961261 : List Nat := [1, 5, 2, 2, 2, 1, 1, 1, 4, 3]
def baseStart_3961261 : Nat := 118140960795 + 3961261 * 2 ^ 59
def prefixEnd_3961261 : Nat := 4983230072969 + 3 ^ 40 * 3961261 * 2
def baseEnd_3961261 : Nat := 1356020593939954187879999

theorem tailTrace_3961261 : CollatzResearch.WordTrace tailWord_3961261 prefixEnd_3961261 1356020593939954187879999 := by
  unfold tailWord_3961261
  simp only [CollatzResearch.WordTrace]
  refine ⟨144479058102035401362643637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96319372068023600908429091 144479058102035401362643637)
  ·
    refine ⟨13544911697065818877747841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 144479058102035401362643637 13544911697065818877747841)
    ·
      refine ⟨10158683772799364158310881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13544911697065818877747841 10158683772799364158310881)
      ·
        refine ⟨7619012829599523118733161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10158683772799364158310881 7619012829599523118733161)
        ·
          refine ⟨5714259622199642339049871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7619012829599523118733161 5714259622199642339049871)
          ·
            refine ⟨8571389433299463508574807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5714259622199642339049871 8571389433299463508574807)
            ·
              refine ⟨12857084149949195262862211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8571389433299463508574807 12857084149949195262862211)
              ·
                refine ⟨19285626224923792894293317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12857084149949195262862211 19285626224923792894293317)
                ·
                  refine ⟨3616054917173211167679997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19285626224923792894293317 3616054917173211167679997)
                  ·
                    refine ⟨1356020593939954187879999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3616054917173211167679997 1356020593939954187879999)
                    ·
                      rfl

theorem cell22_3961261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 1, 1, 4, 3].length) (baseStart_3961261 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3961261 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3961261 prefixEnd_3961261 := by exact prefixLift 3961261
  have htrace : WordTrace (prefixWord ++ tailWord_3961261) baseStart_3961261 baseEnd_3961261 := by
    simpa [prefixWord, tailWord_3961261, baseEnd_3961261] using wordTrace_append hprefix tailTrace_3961261
  have hstable : (prefixWord ++ tailWord_3961261).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3961261).length < 2 ^ (prefixWord ++ tailWord_3961261).sum := by decide
  have hdescent : baseEnd_3961261 < baseStart_3961261 := by decide
  rcases family_descends (prefixWord ++ tailWord_3961261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3961349 : List Nat := [1, 3, 1, 1, 2, 2, 5, 2, 1, 4]
def baseStart_3961349 : Nat := 118140960795 + 3961349 * 2 ^ 59
def prefixEnd_3961349 : Nat := 4983230072969 + 3 ^ 40 * 3961349 * 2
def baseEnd_3961349 : Nat := 1356050718138351291679729

theorem tailTrace_3961349 : CollatzResearch.WordTrace tailWord_3961349 prefixEnd_3961349 1356050718138351291679729 := by
  unfold tailWord_3961349
  simp only [CollatzResearch.WordTrace]
  refine ⟨144482267725716592391847101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96321511817144394927898067 144482267725716592391847101)
  ·
    refine ⟨54180850397143722146942663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 144482267725716592391847101 54180850397143722146942663)
    ·
      refine ⟨81271275595715583220413995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54180850397143722146942663 81271275595715583220413995)
      ·
        refine ⟨121906913393573374830620993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81271275595715583220413995 121906913393573374830620993)
        ·
          refine ⟨91430185045180031122965745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 121906913393573374830620993 91430185045180031122965745)
          ·
            refine ⟨68572638783885023342224309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91430185045180031122965745 68572638783885023342224309)
            ·
              refine ⟨6428684885989220938333529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 68572638783885023342224309 6428684885989220938333529)
              ·
                refine ⟨4821513664491915703750147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6428684885989220938333529 4821513664491915703750147)
                ·
                  refine ⟨7232270496737873555625221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4821513664491915703750147 7232270496737873555625221)
                  ·
                    refine ⟨1356050718138351291679729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7232270496737873555625221 1356050718138351291679729)
                    ·
                      rfl

theorem cell22_3961349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 5, 2, 1, 4].length) (baseStart_3961349 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3961349 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3961349 prefixEnd_3961349 := by exact prefixLift 3961349
  have htrace : WordTrace (prefixWord ++ tailWord_3961349) baseStart_3961349 baseEnd_3961349 := by
    simpa [prefixWord, tailWord_3961349, baseEnd_3961349] using wordTrace_append hprefix tailTrace_3961349
  have hstable : (prefixWord ++ tailWord_3961349).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3961349).length < 2 ^ (prefixWord ++ tailWord_3961349).sum := by decide
  have hdescent : baseEnd_3961349 < baseStart_3961349 := by decide
  rcases family_descends (prefixWord ++ tailWord_3961349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3961381 : List Nat := [1, 3, 1, 2, 2, 1, 6, 2, 4]
def baseStart_3961381 : Nat := 118140960795 + 3961381 * 2 ^ 59
def prefixEnd_3961381 : Nat := 4983230072969 + 3 ^ 40 * 3961381 * 2
def baseEnd_3961381 : Nat := 452020557464104624959877

theorem tailTrace_3961381 : CollatzResearch.WordTrace tailWord_3961381 prefixEnd_3961381 452020557464104624959877 := by
  unfold tailWord_3961381
  simp only [CollatzResearch.WordTrace]
  refine ⟨144483434861600661857011997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96322289907733774571341331 144483434861600661857011997)
  ·
    refine ⟨54181288073100248196379499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 144483434861600661857011997 54181288073100248196379499)
    ·
      refine ⟨81271932109650372294569249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54181288073100248196379499 81271932109650372294569249)
      ·
        refine ⟨60953949082237779220926937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81271932109650372294569249 60953949082237779220926937)
        ·
          refine ⟨45715461811678334415695203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60953949082237779220926937 45715461811678334415695203)
          ·
            refine ⟨68573192717517501623542805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45715461811678334415695203 68573192717517501623542805)
            ·
              refine ⟨3214368408633632888603569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 68573192717517501623542805 3214368408633632888603569)
              ·
                refine ⟨2410776306475224666452677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3214368408633632888603569 2410776306475224666452677)
                ·
                  refine ⟨452020557464104624959877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2410776306475224666452677 452020557464104624959877)
                  ·
                    rfl

theorem cell22_3961381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 6, 2, 4].length) (baseStart_3961381 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3961381 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3961381 prefixEnd_3961381 := by exact prefixLift 3961381
  have htrace : WordTrace (prefixWord ++ tailWord_3961381) baseStart_3961381 baseEnd_3961381 := by
    simpa [prefixWord, tailWord_3961381, baseEnd_3961381] using wordTrace_append hprefix tailTrace_3961381
  have hstable : (prefixWord ++ tailWord_3961381).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3961381).length < 2 ^ (prefixWord ++ tailWord_3961381).sum := by decide
  have hdescent : baseEnd_3961381 < baseStart_3961381 := by decide
  rcases family_descends (prefixWord ++ tailWord_3961381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3961392 : List Nat := [2, 1, 1, 1, 2, 3, 5, 7]
def baseStart_3961392 : Nat := 118140960795 + 3961392 * 2 ^ 59
def prefixEnd_3961392 : Nat := 4983230072969 + 3 ^ 40 * 3961392 * 2
def baseEnd_3961392 : Nat := 150673937546345945872733

theorem tailTrace_3961392 : CollatzResearch.WordTrace tailWord_3961392 prefixEnd_3961392 150673937546345945872733 := by
  unfold tailWord_3961392
  simp only [CollatzResearch.WordTrace]
  refine ⟨72241918032280405367831215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96322557376373873823774953 72241918032280405367831215)
  ·
    refine ⟨108362877048420608051746823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72241918032280405367831215 108362877048420608051746823)
    ·
      refine ⟨162544315572630912077620235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108362877048420608051746823 162544315572630912077620235)
      ·
        refine ⟨243816473358946368116430353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162544315572630912077620235 243816473358946368116430353)
        ·
          refine ⟨182862355019209776087322765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 243816473358946368116430353 182862355019209776087322765)
          ·
            refine ⟨68573383132203666032746037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 182862355019209776087322765 68573383132203666032746037)
            ·
              refine ⟨6428754668644093690569941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 68573383132203666032746037 6428754668644093690569941)
              ·
                refine ⟨150673937546345945872733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6428754668644093690569941 150673937546345945872733)
                ·
                  rfl

theorem cell22_3961392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 5, 7].length) (baseStart_3961392 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3961392 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3961392 prefixEnd_3961392 := by exact prefixLift 3961392
  have htrace : WordTrace (prefixWord ++ tailWord_3961392) baseStart_3961392 baseEnd_3961392 := by
    simpa [prefixWord, tailWord_3961392, baseEnd_3961392] using wordTrace_append hprefix tailTrace_3961392
  have hstable : (prefixWord ++ tailWord_3961392).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3961392).length < 2 ^ (prefixWord ++ tailWord_3961392).sum := by decide
  have hdescent : baseEnd_3961392 < baseStart_3961392 := by decide
  rcases family_descends (prefixWord ++ tailWord_3961392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3961441 : List Nat := [1, 2, 3, 1, 1, 5, 2, 1, 3, 3]
def baseStart_3961441 : Nat := 118140960795 + 3961441 * 2 ^ 59
def prefixEnd_3961441 : Nat := 4983230072969 + 3 ^ 40 * 3961441 * 2
def baseEnd_3961441 : Nat := 1356082211618493718379447

theorem tailTrace_3961441 : CollatzResearch.WordTrace tailWord_3961441 prefixEnd_3961441 1356082211618493718379447 := by
  unfold tailWord_3961441
  simp only [CollatzResearch.WordTrace]
  refine ⟨144485623241383292104196177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96323748827588861402797451 144485623241383292104196177)
  ·
    refine ⟨108364217431037469078147133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144485623241383292104196177 108364217431037469078147133)
    ·
      refine ⟨40636581536639050904305175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 108364217431037469078147133 40636581536639050904305175)
      ·
        refine ⟨60954872304958576356457763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40636581536639050904305175 60954872304958576356457763)
        ·
          refine ⟨91432308457437864534686645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60954872304958576356457763 91432308457437864534686645)
          ·
            refine ⟨8571778917884799800126873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 91432308457437864534686645 8571778917884799800126873)
            ·
              refine ⟨6428834188413599850095155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8571778917884799800126873 6428834188413599850095155)
              ·
                refine ⟨9643251282620399775142733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6428834188413599850095155 9643251282620399775142733)
                ·
                  refine ⟨3616219230982649915678525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9643251282620399775142733 3616219230982649915678525)
                  ·
                    refine ⟨1356082211618493718379447, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3616219230982649915678525 1356082211618493718379447)
                    ·
                      rfl

theorem cell22_3961441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 2, 1, 3, 3].length) (baseStart_3961441 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3961441 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3961441 prefixEnd_3961441 := by exact prefixLift 3961441
  have htrace : WordTrace (prefixWord ++ tailWord_3961441) baseStart_3961441 baseEnd_3961441 := by
    simpa [prefixWord, tailWord_3961441, baseEnd_3961441] using wordTrace_append hprefix tailTrace_3961441
  have hstable : (prefixWord ++ tailWord_3961441).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3961441).length < 2 ^ (prefixWord ++ tailWord_3961441).sum := by decide
  have hdescent : baseEnd_3961441 < baseStart_3961441 := by decide
  rcases family_descends (prefixWord ++ tailWord_3961441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3961492 : List Nat := [2, 4, 2, 2, 1, 2, 3, 2, 1, 3]
def baseStart_3961492 : Nat := 118140960795 + 3961492 * 2 ^ 59
def prefixEnd_3961492 : Nat := 4983230072969 + 3 ^ 40 * 3961492 * 2
def baseEnd_3961492 : Nat := 1356099669960746585354291

theorem tailTrace_3961492 : CollatzResearch.WordTrace tailWord_3961492 prefixEnd_3961492 1356099669960746585354291 := by
  unfold tailWord_3961492
  simp only [CollatzResearch.WordTrace]
  refine ⟨72243741682099263907151365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96324988909465685209535153 72243741682099263907151365)
  ·
    refine ⟨13545701565393611982590881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 72243741682099263907151365 13545701565393611982590881)
    ·
      refine ⟨10159276174045208986943161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13545701565393611982590881 10159276174045208986943161)
      ·
        refine ⟨7619457130533906740207371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10159276174045208986943161 7619457130533906740207371)
        ·
          refine ⟨11429185695800860110311057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7619457130533906740207371 11429185695800860110311057)
          ·
            refine ⟨8571889271850645082733293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11429185695800860110311057 8571889271850645082733293)
            ·
              refine ⟨3214458476943991906024985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8571889271850645082733293 3214458476943991906024985)
              ·
                refine ⟨2410843857707993929518739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3214458476943991906024985 2410843857707993929518739)
                ·
                  refine ⟨3616265786561990894278109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2410843857707993929518739 3616265786561990894278109)
                  ·
                    refine ⟨1356099669960746585354291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3616265786561990894278109 1356099669960746585354291)
                    ·
                      rfl

theorem cell22_3961492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 3, 2, 1, 3].length) (baseStart_3961492 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3961492 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3961492 prefixEnd_3961492 := by exact prefixLift 3961492
  have htrace : WordTrace (prefixWord ++ tailWord_3961492) baseStart_3961492 baseEnd_3961492 := by
    simpa [prefixWord, tailWord_3961492, baseEnd_3961492] using wordTrace_append hprefix tailTrace_3961492
  have hstable : (prefixWord ++ tailWord_3961492).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3961492).length < 2 ^ (prefixWord ++ tailWord_3961492).sum := by decide
  have hdescent : baseEnd_3961492 < baseStart_3961492 := by decide
  rcases family_descends (prefixWord ++ tailWord_3961492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3961505 : List Nat := [1, 2, 3, 3, 4, 1, 2, 1, 5]
def baseStart_3961505 : Nat := 118140960795 + 3961505 * 2 ^ 59
def prefixEnd_3961505 : Nat := 4983230072969 + 3 ^ 40 * 3961505 * 2
def baseEnd_3961505 : Nat := 452034706708806294926417

theorem tailTrace_3961505 : CollatzResearch.WordTrace tailWord_3961505 prefixEnd_3961505 452034706708806294926417 := by
  unfold tailWord_3961505
  simp only [CollatzResearch.WordTrace]
  refine ⟨144487957513151431034525969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96325305008767620689683979 144487957513151431034525969)
  ·
    refine ⟨108365968134863573275894477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144487957513151431034525969 108365968134863573275894477)
    ·
      refine ⟨40637238050573839978460429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 108365968134863573275894477 40637238050573839978460429)
      ·
        refine ⟨15238964268965189991922661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40637238050573839978460429 15238964268965189991922661)
        ·
          refine ⟨2857305800430973123485499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15238964268965189991922661 2857305800430973123485499)
          ·
            refine ⟨4285958700646459685228249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2857305800430973123485499 4285958700646459685228249)
            ·
              refine ⟨3214469025484844763921187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4285958700646459685228249 3214469025484844763921187)
              ·
                refine ⟨4821703538227267145881781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3214469025484844763921187 4821703538227267145881781)
                ·
                  refine ⟨452034706708806294926417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4821703538227267145881781 452034706708806294926417)
                  ·
                    rfl

theorem cell22_3961505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 4, 1, 2, 1, 5].length) (baseStart_3961505 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3961505 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3961505 prefixEnd_3961505 := by exact prefixLift 3961505
  have htrace : WordTrace (prefixWord ++ tailWord_3961505) baseStart_3961505 baseEnd_3961505 := by
    simpa [prefixWord, tailWord_3961505, baseEnd_3961505] using wordTrace_append hprefix tailTrace_3961505
  have hstable : (prefixWord ++ tailWord_3961505).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3961505).length < 2 ^ (prefixWord ++ tailWord_3961505).sum := by decide
  have hdescent : baseEnd_3961505 < baseStart_3961505 := by decide
  rcases family_descends (prefixWord ++ tailWord_3961505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3961518 : List Nat := [4, 1, 4, 1, 1, 2, 1, 1, 3, 4]
def baseStart_3961518 : Nat := 118140960795 + 3961518 * 2 ^ 59
def prefixEnd_3961518 : Nat := 4983230072969 + 3 ^ 40 * 3961518 * 2
def baseEnd_3961518 : Nat := 1356108570292091184204211

theorem tailTrace_3961518 : CollatzResearch.WordTrace tailWord_3961518 prefixEnd_3961518 1356108570292091184204211 := by
  unfold tailWord_3961518
  simp only [CollatzResearch.WordTrace]
  refine ⟨18061053957763041781843651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 96325621108069556169832805 18061053957763041781843651)
  ·
    refine ⟨27091580936644562672765477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18061053957763041781843651 27091580936644562672765477)
    ·
      refine ⟨5079671425620855501143527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27091580936644562672765477 5079671425620855501143527)
      ·
        refine ⟨7619507138431283251715291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5079671425620855501143527 7619507138431283251715291)
        ·
          refine ⟨11429260707646924877572937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7619507138431283251715291 11429260707646924877572937)
          ·
            refine ⟨8571945530735193658179703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11429260707646924877572937 8571945530735193658179703)
            ·
              refine ⟨12857918296102790487269555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8571945530735193658179703 12857918296102790487269555)
              ·
                refine ⟨19286877444154185730904333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12857918296102790487269555 19286877444154185730904333)
                ·
                  refine ⟨7232579041557819649089125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19286877444154185730904333 7232579041557819649089125)
                  ·
                    refine ⟨1356108570292091184204211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7232579041557819649089125 1356108570292091184204211)
                    ·
                      rfl

theorem cell22_3961518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 1, 1, 3, 4].length) (baseStart_3961518 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3961518 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3961518 prefixEnd_3961518 := by exact prefixLift 3961518
  have htrace : WordTrace (prefixWord ++ tailWord_3961518) baseStart_3961518 baseEnd_3961518 := by
    simpa [prefixWord, tailWord_3961518, baseEnd_3961518] using wordTrace_append hprefix tailTrace_3961518
  have hstable : (prefixWord ++ tailWord_3961518).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3961518).length < 2 ^ (prefixWord ++ tailWord_3961518).sum := by decide
  have hdescent : baseEnd_3961518 < baseStart_3961518 := by decide
  rcases family_descends (prefixWord ++ tailWord_3961518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3961546 : List Nat := [3, 1, 2, 1, 4, 1, 2, 2, 2, 4]
def baseStart_3961546 : Nat := 118140960795 + 3961546 * 2 ^ 59
def prefixEnd_3961546 : Nat := 4983230072969 + 3 ^ 40 * 3961546 * 2
def baseEnd_3961546 : Nat := 1356118155264308444504125

theorem tailTrace_3961546 : CollatzResearch.WordTrace tailWord_3961546 prefixEnd_3961546 1356118155264308444504125 := by
  unfold tailWord_3961546
  simp only [CollatzResearch.WordTrace]
  refine ⟨36122363226500723759192123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96326301937335263357845661 36122363226500723759192123)
  ·
    refine ⟨54183544839751085638788185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36122363226500723759192123 54183544839751085638788185)
    ·
      refine ⟨40637658629813314229091139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54183544839751085638788185 40637658629813314229091139)
      ·
        refine ⟨60956487944719971343636709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40637658629813314229091139 60956487944719971343636709)
        ·
          refine ⟨11429341489634994626931883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 60956487944719971343636709 11429341489634994626931883)
          ·
            refine ⟨17144012234452491940397825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11429341489634994626931883 17144012234452491940397825)
            ·
              refine ⟨12858009175839368955298369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17144012234452491940397825 12858009175839368955298369)
              ·
                refine ⟨9643506881879526716473777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12858009175839368955298369 9643506881879526716473777)
                ·
                  refine ⟨7232630161409645037355333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9643506881879526716473777 7232630161409645037355333)
                  ·
                    refine ⟨1356118155264308444504125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7232630161409645037355333 1356118155264308444504125)
                    ·
                      rfl

theorem cell22_3961546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 2, 2, 2, 4].length) (baseStart_3961546 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3961546 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3961546 prefixEnd_3961546 := by exact prefixLift 3961546
  have htrace : WordTrace (prefixWord ++ tailWord_3961546) baseStart_3961546 baseEnd_3961546 := by
    simpa [prefixWord, tailWord_3961546, baseEnd_3961546] using wordTrace_append hprefix tailTrace_3961546
  have hstable : (prefixWord ++ tailWord_3961546).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3961546).length < 2 ^ (prefixWord ++ tailWord_3961546).sum := by decide
  have hdescent : baseEnd_3961546 < baseStart_3961546 := by decide
  rcases family_descends (prefixWord ++ tailWord_3961546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3961548 : List Nat := [2, 2, 1, 5, 1, 1, 1, 4, 2, 3]
def baseStart_3961548 : Nat := 118140960795 + 3961548 * 2 ^ 59
def prefixEnd_3961548 : Nat := 4983230072969 + 3 ^ 40 * 3961548 * 2
def baseEnd_3961548 : Nat := 1356118839905181105954119

theorem tailTrace_3961548 : CollatzResearch.WordTrace tailWord_3961548 prefixEnd_3961548 1356118839905181105954119 := by
  unfold tailWord_3961548
  simp only [CollatzResearch.WordTrace]
  refine ⟨72244762925997824689170649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96326350567997099585560865 72244762925997824689170649)
  ·
    refine ⟨54183572194498368516877987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72244762925997824689170649 54183572194498368516877987)
    ·
      refine ⟨81275358291747552775316981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54183572194498368516877987 81275358291747552775316981)
      ·
        refine ⟨7619564839851333072685967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 81275358291747552775316981 7619564839851333072685967)
        ·
          refine ⟨11429347259776999609028951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7619564839851333072685967 11429347259776999609028951)
          ·
            refine ⟨17144020889665499413543427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11429347259776999609028951 17144020889665499413543427)
            ·
              refine ⟨25716031334498249120315141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17144020889665499413543427 25716031334498249120315141)
              ·
                refine ⟨4821755875218421710059089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25716031334498249120315141 4821755875218421710059089)
                ·
                  refine ⟨3616316906413816282544317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4821755875218421710059089 3616316906413816282544317)
                  ·
                    refine ⟨1356118839905181105954119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3616316906413816282544317 1356118839905181105954119)
                    ·
                      rfl

theorem cell22_3961548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 1, 4, 2, 3].length) (baseStart_3961548 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3961548 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3961548 prefixEnd_3961548 := by exact prefixLift 3961548
  have htrace : WordTrace (prefixWord ++ tailWord_3961548) baseStart_3961548 baseEnd_3961548 := by
    simpa [prefixWord, tailWord_3961548, baseEnd_3961548] using wordTrace_append hprefix tailTrace_3961548
  have hstable : (prefixWord ++ tailWord_3961548).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3961548).length < 2 ^ (prefixWord ++ tailWord_3961548).sum := by decide
  have hdescent : baseEnd_3961548 < baseStart_3961548 := by decide
  rcases family_descends (prefixWord ++ tailWord_3961548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3961550 : List Nat := [4, 1, 1, 1, 3, 4, 2, 2, 4]
def baseStart_3961550 : Nat := 118140960795 + 3961550 * 2 ^ 59
def prefixEnd_3961550 : Nat := 4983230072969 + 3 ^ 40 * 3961550 * 2
def baseEnd_3961550 : Nat := 452039841515351255801371

theorem tailTrace_3961550 : CollatzResearch.WordTrace tailWord_3961550 prefixEnd_3961550 452039841515351255801371 := by
  unfold tailWord_3961550
  simp only [CollatzResearch.WordTrace]
  refine ⟨18061199849748550464989263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 96326399198658935813276069 18061199849748550464989263)
  ·
    refine ⟨27091799774622825697483895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18061199849748550464989263 27091799774622825697483895)
    ·
      refine ⟨40637699661934238546225843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27091799774622825697483895 40637699661934238546225843)
      ·
        refine ⟨60956549492901357819338765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40637699661934238546225843 60956549492901357819338765)
        ·
          refine ⟨22858706059838009182252037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60956549492901357819338765 22858706059838009182252037)
          ·
            refine ⟨4286007386219626721672257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22858706059838009182252037 4286007386219626721672257)
            ·
              refine ⟨3214505539664720041254193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4286007386219626721672257 3214505539664720041254193)
              ·
                refine ⟨2410879154748540030940645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3214505539664720041254193 2410879154748540030940645)
                ·
                  refine ⟨452039841515351255801371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2410879154748540030940645 452039841515351255801371)
                  ·
                    rfl

theorem cell22_3961550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 4, 2, 2, 4].length) (baseStart_3961550 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3961550 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3961550 prefixEnd_3961550 := by exact prefixLift 3961550
  have htrace : WordTrace (prefixWord ++ tailWord_3961550) baseStart_3961550 baseEnd_3961550 := by
    simpa [prefixWord, tailWord_3961550, baseEnd_3961550] using wordTrace_append hprefix tailTrace_3961550
  have hstable : (prefixWord ++ tailWord_3961550).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3961550).length < 2 ^ (prefixWord ++ tailWord_3961550).sum := by decide
  have hdescent : baseEnd_3961550 < baseStart_3961550 := by decide
  rcases family_descends (prefixWord ++ tailWord_3961550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3961653 : List Nat := [1, 3, 3, 1, 3, 1, 2, 3, 1, 4]
def baseStart_3961653 : Nat := 118140960795 + 3961653 * 2 ^ 59
def prefixEnd_3961653 : Nat := 4983230072969 + 3 ^ 40 * 3961653 * 2
def baseEnd_3961653 : Nat := 1356154783550995832078797

theorem tailTrace_3961653 : CollatzResearch.WordTrace tailWord_3961653 prefixEnd_3961653 1356154783550995832078797 := by
  unfold tailWord_3961653
  simp only [CollatzResearch.WordTrace]
  refine ⟨144493355516615252310913613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96328903677743501540609075 144493355516615252310913613)
  ·
    refine ⟨54185008318730719616592605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 144493355516615252310913613 54185008318730719616592605)
    ·
      refine ⟨20319378119524019856222227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54185008318730719616592605 20319378119524019856222227)
      ·
        refine ⟨30479067179286029784333341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20319378119524019856222227 30479067179286029784333341)
        ·
          refine ⟨11429650192232261169125003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30479067179286029784333341 11429650192232261169125003)
          ·
            refine ⟨17144475288348391753687505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11429650192232261169125003 17144475288348391753687505)
            ·
              refine ⟨12858356466261293815265629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17144475288348391753687505 12858356466261293815265629)
              ·
                refine ⟨4821883674847985180724611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12858356466261293815265629 4821883674847985180724611)
                ·
                  refine ⟨7232825512271977771086917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4821883674847985180724611 7232825512271977771086917)
                  ·
                    refine ⟨1356154783550995832078797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7232825512271977771086917 1356154783550995832078797)
                    ·
                      rfl

theorem cell22_3961653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 2, 3, 1, 4].length) (baseStart_3961653 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3961653 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3961653 prefixEnd_3961653 := by exact prefixLift 3961653
  have htrace : WordTrace (prefixWord ++ tailWord_3961653) baseStart_3961653 baseEnd_3961653 := by
    simpa [prefixWord, tailWord_3961653, baseEnd_3961653] using wordTrace_append hprefix tailTrace_3961653
  have hstable : (prefixWord ++ tailWord_3961653).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3961653).length < 2 ^ (prefixWord ++ tailWord_3961653).sum := by decide
  have hdescent : baseEnd_3961653 < baseStart_3961653 := by decide
  rcases family_descends (prefixWord ++ tailWord_3961653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3961762 : List Nat := [3, 3, 1, 2, 2, 1, 1, 5, 1, 3]
def baseStart_3961762 : Nat := 118140960795 + 3961762 * 2 ^ 59
def prefixEnd_3961762 : Nat := 4983230072969 + 3 ^ 40 * 3961762 * 2
def baseEnd_3961762 : Nat := 1356192096478555881103463

theorem tailTrace_3961762 : CollatzResearch.WordTrace tailWord_3961762 prefixEnd_3961762 1356192096478555881103463 := by
  unfold tailWord_3961762
  simp only [CollatzResearch.WordTrace]
  refine ⟨36124332768305090981657885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96331554048813575951087693 36124332768305090981657885)
  ·
    refine ⟨13546624788114409118121707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36124332768305090981657885 13546624788114409118121707)
    ·
      refine ⟨20319937182171613677182561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13546624788114409118121707 20319937182171613677182561)
      ·
        refine ⟨15239952886628710257886921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20319937182171613677182561 15239952886628710257886921)
        ·
          refine ⟨11429964664971532693415191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15239952886628710257886921 11429964664971532693415191)
          ·
            refine ⟨17144946997457299040122787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11429964664971532693415191 17144946997457299040122787)
            ·
              refine ⟨25717420496185948560184181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17144946997457299040122787 25717420496185948560184181)
              ·
                refine ⟨2411008171517432677517267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 25717420496185948560184181 2411008171517432677517267)
                ·
                  refine ⟨3616512257276149016275901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2411008171517432677517267 3616512257276149016275901)
                  ·
                    refine ⟨1356192096478555881103463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3616512257276149016275901 1356192096478555881103463)
                    ·
                      rfl

theorem cell22_3961762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 1, 5, 1, 3].length) (baseStart_3961762 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3961762 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3961762 prefixEnd_3961762 := by exact prefixLift 3961762
  have htrace : WordTrace (prefixWord ++ tailWord_3961762) baseStart_3961762 baseEnd_3961762 := by
    simpa [prefixWord, tailWord_3961762, baseEnd_3961762] using wordTrace_append hprefix tailTrace_3961762
  have hstable : (prefixWord ++ tailWord_3961762).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3961762).length < 2 ^ (prefixWord ++ tailWord_3961762).sum := by decide
  have hdescent : baseEnd_3961762 < baseStart_3961762 := by decide
  rcases family_descends (prefixWord ++ tailWord_3961762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3961798 : List Nat := [6, 1, 3, 1, 2, 1, 2, 6]
def baseStart_3961798 : Nat := 118140960795 + 3961798 * 2 ^ 59
def prefixEnd_3961798 : Nat := 4983230072969 + 3 ^ 40 * 3961798 * 2
def baseEnd_3961798 : Nat := 150689380001584865244817

theorem tailTrace_3961798 : CollatzResearch.WordTrace tailWord_3961798 prefixEnd_3961798 150689380001584865244817 := by
  unfold tailWord_3961798
  simp only [CollatzResearch.WordTrace]
  refine ⟨4515582628159060689841939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 96332429400726628049961365 4515582628159060689841939)
  ·
    refine ⟨6773373942238591034762909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4515582628159060689841939 6773373942238591034762909)
    ·
      refine ⟨2540015228339471638036091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6773373942238591034762909 2540015228339471638036091)
      ·
        refine ⟨3810022842509207457054137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2540015228339471638036091 3810022842509207457054137)
        ·
          refine ⟨2857517131881905592790603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3810022842509207457054137 2857517131881905592790603)
          ·
            refine ⟨4286275697822858389185905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2857517131881905592790603 4286275697822858389185905)
            ·
              refine ⟨3214706773367143791889429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4286275697822858389185905 3214706773367143791889429)
              ·
                refine ⟨150689380001584865244817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3214706773367143791889429 150689380001584865244817)
                ·
                  rfl

theorem cell22_3961798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 2, 1, 2, 6].length) (baseStart_3961798 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3961798 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3961798 prefixEnd_3961798 := by exact prefixLift 3961798
  have htrace : WordTrace (prefixWord ++ tailWord_3961798) baseStart_3961798 baseEnd_3961798 := by
    simpa [prefixWord, tailWord_3961798, baseEnd_3961798] using wordTrace_append hprefix tailTrace_3961798
  have hstable : (prefixWord ++ tailWord_3961798).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3961798).length < 2 ^ (prefixWord ++ tailWord_3961798).sum := by decide
  have hdescent : baseEnd_3961798 < baseStart_3961798 := by decide
  rcases family_descends (prefixWord ++ tailWord_3961798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3961852 : List Nat := [2, 2, 2, 1, 2, 3, 4, 1, 2, 3]
def baseStart_3961852 : Nat := 118140960795 + 3961852 * 2 ^ 59
def prefixEnd_3961852 : Nat := 4983230072969 + 3 ^ 40 * 3961852 * 2
def baseEnd_3961852 : Nat := 1356222905317825646353187

theorem tailTrace_3961852 : CollatzResearch.WordTrace tailWord_3961852 prefixEnd_3961852 1356222905317825646353187 := by
  unfold tailWord_3961852
  simp only [CollatzResearch.WordTrace]
  refine ⟨72250306821447154648703905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96333742428596206198271873 72250306821447154648703905)
  ·
    refine ⟨54187730116085365986527929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72250306821447154648703905 54187730116085365986527929)
    ·
      refine ⟨40640797587064024489895947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54187730116085365986527929 40640797587064024489895947)
      ·
        refine ⟨60961196380596036734843921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40640797587064024489895947 60961196380596036734843921)
        ·
          refine ⟨45720897285447027551132941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60961196380596036734843921 45720897285447027551132941)
          ·
            refine ⟨17145336482042635331674853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45720897285447027551132941 17145336482042635331674853)
            ·
              refine ⟨3214750590382994124689035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17145336482042635331674853 3214750590382994124689035)
              ·
                refine ⟨4822125885574491187033553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3214750590382994124689035 4822125885574491187033553)
                ·
                  refine ⟨3616594414180868390275165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4822125885574491187033553 3616594414180868390275165)
                  ·
                    refine ⟨1356222905317825646353187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3616594414180868390275165 1356222905317825646353187)
                    ·
                      rfl

theorem cell22_3961852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 4, 1, 2, 3].length) (baseStart_3961852 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3961852 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3961852 prefixEnd_3961852 := by exact prefixLift 3961852
  have htrace : WordTrace (prefixWord ++ tailWord_3961852) baseStart_3961852 baseEnd_3961852 := by
    simpa [prefixWord, tailWord_3961852, baseEnd_3961852] using wordTrace_append hprefix tailTrace_3961852
  have hstable : (prefixWord ++ tailWord_3961852).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3961852).length < 2 ^ (prefixWord ++ tailWord_3961852).sum := by decide
  have hdescent : baseEnd_3961852 < baseStart_3961852 := by decide
  rcases family_descends (prefixWord ++ tailWord_3961852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3961895 : List Nat := [1, 1, 7, 1, 1, 1, 1, 1, 2, 6]
def baseStart_3961895 : Nat := 118140960795 + 3961895 * 2 ^ 59
def prefixEnd_3961895 : Nat := 4983230072969 + 3 ^ 40 * 3961895 * 2
def baseEnd_3961895 : Nat := 1356237625096587867528055

theorem tailTrace_3961895 : CollatzResearch.WordTrace tailWord_3961895 prefixEnd_3961895 1356237625096587867528055 := by
  unfold tailWord_3961895
  simp only [CollatzResearch.WordTrace]
  refine ⟨144502181981738527641223139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96334787987825685094148759 144502181981738527641223139)
  ·
    refine ⟨216753272972607791461834709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144502181981738527641223139 216753272972607791461834709)
    ·
      refine ⟨5080154835295495112386751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 216753272972607791461834709 5080154835295495112386751)
      ·
        refine ⟨7620232252943242668580127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5080154835295495112386751 7620232252943242668580127)
        ·
          refine ⟨11430348379414864002870191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7620232252943242668580127 11430348379414864002870191)
          ·
            refine ⟨17145522569122296004305287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11430348379414864002870191 17145522569122296004305287)
            ·
              refine ⟨25718283853683444006457931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17145522569122296004305287 25718283853683444006457931)
              ·
                refine ⟨38577425780525166009686897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25718283853683444006457931 38577425780525166009686897)
                ·
                  refine ⟨28933069335393874507265173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38577425780525166009686897 28933069335393874507265173)
                  ·
                    refine ⟨1356237625096587867528055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28933069335393874507265173 1356237625096587867528055)
                    ·
                      rfl

theorem cell22_3961895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 1, 1, 2, 6].length) (baseStart_3961895 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3961895 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3961895 prefixEnd_3961895 := by exact prefixLift 3961895
  have htrace : WordTrace (prefixWord ++ tailWord_3961895) baseStart_3961895 baseEnd_3961895 := by
    simpa [prefixWord, tailWord_3961895, baseEnd_3961895] using wordTrace_append hprefix tailTrace_3961895
  have hstable : (prefixWord ++ tailWord_3961895).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3961895).length < 2 ^ (prefixWord ++ tailWord_3961895).sum := by decide
  have hdescent : baseEnd_3961895 < baseStart_3961895 := by decide
  rcases family_descends (prefixWord ++ tailWord_3961895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3961923 : List Nat := [1, 1, 1, 3, 1, 2, 3, 3, 3, 4]
def baseStart_3961923 : Nat := 118140960795 + 3961923 * 2 ^ 59
def prefixEnd_3961923 : Nat := 4983230072969 + 3 ^ 40 * 3961923 * 2
def baseEnd_3961923 : Nat := 1356247210068805127827969

theorem tailTrace_3961923 : CollatzResearch.WordTrace tailWord_3961923 prefixEnd_3961923 1356247210068805127827969 := by
  unfold tailWord_3961923
  simp only [CollatzResearch.WordTrace]
  refine ⟨144503203225637088423242423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96335468817091392282161615 144503203225637088423242423)
  ·
    refine ⟨216754804838455632634863635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144503203225637088423242423 216754804838455632634863635)
    ·
      refine ⟨325132207257683448952295453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216754804838455632634863635 325132207257683448952295453)
      ·
        refine ⟨121924577721631293357110795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 325132207257683448952295453 121924577721631293357110795)
        ·
          refine ⟨182886866582446940035666193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121924577721631293357110795 182886866582446940035666193)
          ·
            refine ⟨137165149936835205026749645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 182886866582446940035666193 137165149936835205026749645)
            ·
              refine ⟨51436931226313201885031117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 137165149936835205026749645 51436931226313201885031117)
              ·
                refine ⟨19288849209867450706886669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51436931226313201885031117 19288849209867450706886669)
                ·
                  refine ⟨7233318453700294015082501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19288849209867450706886669 7233318453700294015082501)
                  ·
                    refine ⟨1356247210068805127827969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7233318453700294015082501 1356247210068805127827969)
                    ·
                      rfl

theorem cell22_3961923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 3, 3, 4].length) (baseStart_3961923 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3961923 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3961923 prefixEnd_3961923 := by exact prefixLift 3961923
  have htrace : WordTrace (prefixWord ++ tailWord_3961923) baseStart_3961923 baseEnd_3961923 := by
    simpa [prefixWord, tailWord_3961923, baseEnd_3961923] using wordTrace_append hprefix tailTrace_3961923
  have hstable : (prefixWord ++ tailWord_3961923).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3961923).length < 2 ^ (prefixWord ++ tailWord_3961923).sum := by decide
  have hdescent : baseEnd_3961923 < baseStart_3961923 := by decide
  rcases family_descends (prefixWord ++ tailWord_3961923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3961953 : List Nat := [1, 2, 3, 1, 1, 2, 2, 2, 3, 5]
def baseStart_3961953 : Nat := 118140960795 + 3961953 * 2 ^ 59
def prefixEnd_3961953 : Nat := 4983230072969 + 3 ^ 40 * 3961953 * 2
def baseEnd_3961953 : Nat := 1356257479681895049577877

theorem tailTrace_3961953 : CollatzResearch.WordTrace tailWord_3961953 prefixEnd_3961953 1356257479681895049577877 := by
  unfold tailWord_3961953
  simp only [CollatzResearch.WordTrace]
  refine ⟨144504297415528403546834513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96336198277018935697889675 144504297415528403546834513)
  ·
    refine ⟨108378223061646302660125885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144504297415528403546834513 108378223061646302660125885)
    ·
      refine ⟨40641833648117363497547207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 108378223061646302660125885 40641833648117363497547207)
      ·
        refine ⟨60962750472176045246320811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40641833648117363497547207 60962750472176045246320811)
        ·
          refine ⟨91444125708264067869481217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60962750472176045246320811 91444125708264067869481217)
          ·
            refine ⟨68583094281198050902110913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91444125708264067869481217 68583094281198050902110913)
            ·
              refine ⟨51437320710898538176583185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68583094281198050902110913 51437320710898538176583185)
              ·
                refine ⟨38577990533173903632437389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51437320710898538176583185 38577990533173903632437389)
                ·
                  refine ⟨14466746449940213862164021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38577990533173903632437389 14466746449940213862164021)
                  ·
                    refine ⟨1356257479681895049577877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14466746449940213862164021 1356257479681895049577877)
                    ·
                      rfl

theorem cell22_3961953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 2, 3, 5].length) (baseStart_3961953 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3961953 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3961953 prefixEnd_3961953 := by exact prefixLift 3961953
  have htrace : WordTrace (prefixWord ++ tailWord_3961953) baseStart_3961953 baseEnd_3961953 := by
    simpa [prefixWord, tailWord_3961953, baseEnd_3961953] using wordTrace_append hprefix tailTrace_3961953
  have hstable : (prefixWord ++ tailWord_3961953).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3961953).length < 2 ^ (prefixWord ++ tailWord_3961953).sum := by decide
  have hdescent : baseEnd_3961953 < baseStart_3961953 := by decide
  rcases family_descends (prefixWord ++ tailWord_3961953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3961968 : List Nat := [2, 1, 1, 1, 5, 1, 1, 1, 3, 6]
def baseStart_3961968 : Nat := 118140960795 + 3961968 * 2 ^ 59
def prefixEnd_3961968 : Nat := 4983230072969 + 3 ^ 40 * 3961968 * 2
def baseEnd_3961968 : Nat := 1356262614488440010452831

theorem tailTrace_3961968 : CollatzResearch.WordTrace tailWord_3961968 prefixEnd_3961968 1356262614488440010452831 := by
  unfold tailWord_3961968
  simp only [CollatzResearch.WordTrace]
  refine ⟨72252422255237030554315279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96336563006982707405753705 72252422255237030554315279)
  ·
    refine ⟨108378633382855545831472919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72252422255237030554315279 108378633382855545831472919)
    ·
      refine ⟨162567950074283318747209379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108378633382855545831472919 162567950074283318747209379)
      ·
        refine ⟨243851925111424978120814069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162567950074283318747209379 243851925111424978120814069)
        ·
          refine ⟨22861117979196091698826319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 243851925111424978120814069 22861117979196091698826319)
          ·
            refine ⟨34291676968794137548239479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22861117979196091698826319 34291676968794137548239479)
            ·
              refine ⟨51437515453191206322359219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34291676968794137548239479 51437515453191206322359219)
              ·
                refine ⟨77156273179786809483538829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51437515453191206322359219 77156273179786809483538829)
                ·
                  refine ⟨28933602442420053556327061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 77156273179786809483538829 28933602442420053556327061)
                  ·
                    refine ⟨1356262614488440010452831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28933602442420053556327061 1356262614488440010452831)
                    ·
                      rfl

theorem cell22_3961968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 1, 3, 6].length) (baseStart_3961968 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3961968 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3961968 prefixEnd_3961968 := by exact prefixLift 3961968
  have htrace : WordTrace (prefixWord ++ tailWord_3961968) baseStart_3961968 baseEnd_3961968 := by
    simpa [prefixWord, tailWord_3961968, baseEnd_3961968] using wordTrace_append hprefix tailTrace_3961968
  have hstable : (prefixWord ++ tailWord_3961968).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3961968).length < 2 ^ (prefixWord ++ tailWord_3961968).sum := by decide
  have hdescent : baseEnd_3961968 < baseStart_3961968 := by decide
  rcases family_descends (prefixWord ++ tailWord_3961968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3961982 : List Nat := [4, 2, 4, 1, 2, 1, 1, 3, 1, 3]
def baseStart_3961982 : Nat := 118140960795 + 3961982 * 2 ^ 59
def prefixEnd_3961982 : Nat := 4983230072969 + 3 ^ 40 * 3961982 * 2
def baseEnd_3961982 : Nat := 1356267406974548640602789

theorem tailTrace_3961982 : CollatzResearch.WordTrace tailWord_3961982 prefixEnd_3961982 1356267406974548640602789 := by
  unfold tailWord_3961982
  simp only [CollatzResearch.WordTrace]
  refine ⟨18063169391552917687455025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 96336903421615560999760133 18063169391552917687455025)
  ·
    refine ⟨13547377043664688265591269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18063169391552917687455025 13547377043664688265591269)
    ·
      refine ⟨2540133195687129049798363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13547377043664688265591269 2540133195687129049798363)
      ·
        refine ⟨3810199793530693574697545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2540133195687129049798363 3810199793530693574697545)
        ·
          refine ⟨2857649845148020181023159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3810199793530693574697545 2857649845148020181023159)
          ·
            refine ⟨4286474767722030271534739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2857649845148020181023159 4286474767722030271534739)
            ·
              refine ⟨6429712151583045407302109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4286474767722030271534739 6429712151583045407302109)
              ·
                refine ⟨2411142056843642027738291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6429712151583045407302109 2411142056843642027738291)
                ·
                  refine ⟨3616713085265463041607437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2411142056843642027738291 3616713085265463041607437)
                  ·
                    refine ⟨1356267406974548640602789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3616713085265463041607437 1356267406974548640602789)
                    ·
                      rfl

theorem cell22_3961982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 2, 1, 1, 3, 1, 3].length) (baseStart_3961982 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3961982 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3961982 prefixEnd_3961982 := by exact prefixLift 3961982
  have htrace : WordTrace (prefixWord ++ tailWord_3961982) baseStart_3961982 baseEnd_3961982 := by
    simpa [prefixWord, tailWord_3961982, baseEnd_3961982] using wordTrace_append hprefix tailTrace_3961982
  have hstable : (prefixWord ++ tailWord_3961982).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3961982).length < 2 ^ (prefixWord ++ tailWord_3961982).sum := by decide
  have hdescent : baseEnd_3961982 < baseStart_3961982 := by decide
  rcases family_descends (prefixWord ++ tailWord_3961982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3961985 : List Nat := [1, 2, 4, 2, 2, 1, 2, 1, 1, 6]
def baseStart_3961985 : Nat := 118140960795 + 3961985 * 2 ^ 59
def prefixEnd_3961985 : Nat := 4983230072969 + 3 ^ 40 * 3961985 * 2
def baseEnd_3961985 : Nat := 1356268433935857632777779

theorem tailTrace_3961985 : CollatzResearch.WordTrace tailWord_3961985 prefixEnd_3961985 1356268433935857632777779 := by
  unfold tailWord_3961985
  simp only [CollatzResearch.WordTrace]
  refine ⟨144505464551412473011999409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96336976367608315341332939 144505464551412473011999409)
  ·
    refine ⟨108379098413559354758999557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144505464551412473011999409 108379098413559354758999557)
    ·
      refine ⟨20321080952542379017312417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 108379098413559354758999557 20321080952542379017312417)
      ·
        refine ⟨15240810714406784262984313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20321080952542379017312417 15240810714406784262984313)
        ·
          refine ⟨11430608035805088197238235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15240810714406784262984313 11430608035805088197238235)
          ·
            refine ⟨17145912053707632295857353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11430608035805088197238235 17145912053707632295857353)
            ·
              refine ⟨12859434040280724221893015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17145912053707632295857353 12859434040280724221893015)
              ·
                refine ⟨19289151060421086332839523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12859434040280724221893015 19289151060421086332839523)
                ·
                  refine ⟨28933726590631629499259285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19289151060421086332839523 28933726590631629499259285)
                  ·
                    refine ⟨1356268433935857632777779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28933726590631629499259285 1356268433935857632777779)
                    ·
                      rfl

theorem cell22_3961985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 2, 1, 1, 6].length) (baseStart_3961985 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3961985 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3961985 prefixEnd_3961985 := by exact prefixLift 3961985
  have htrace : WordTrace (prefixWord ++ tailWord_3961985) baseStart_3961985 baseEnd_3961985 := by
    simpa [prefixWord, tailWord_3961985, baseEnd_3961985] using wordTrace_append hprefix tailTrace_3961985
  have hstable : (prefixWord ++ tailWord_3961985).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3961985).length < 2 ^ (prefixWord ++ tailWord_3961985).sum := by decide
  have hdescent : baseEnd_3961985 < baseStart_3961985 := by decide
  rcases family_descends (prefixWord ++ tailWord_3961985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3961989 : List Nat := [1, 3, 1, 1, 6, 2, 1, 3, 4]
def baseStart_3961989 : Nat := 118140960795 + 3961989 * 2 ^ 59
def prefixEnd_3961989 : Nat := 4983230072969 + 3 ^ 40 * 3961989 * 2
def baseEnd_3961989 : Nat := 452089934405867651892589

theorem tailTrace_3961989 : CollatzResearch.WordTrace tailWord_3961989 prefixEnd_3961989 452089934405867651892589 := by
  unfold tailWord_3961989
  simp only [CollatzResearch.WordTrace]
  refine ⟨144505610443397981695145021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96337073628931987796763347 144505610443397981695145021)
  ·
    refine ⟨54189603916274243135679383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 144505610443397981695145021 54189603916274243135679383)
    ·
      refine ⟨81284405874411364703519075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54189603916274243135679383 81284405874411364703519075)
      ·
        refine ⟨121926608811617047055278613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81284405874411364703519075 121926608811617047055278613)
        ·
          refine ⟨5715309788044549080716185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 121926608811617047055278613 5715309788044549080716185)
          ·
            refine ⟨4286482341033411810537139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5715309788044549080716185 4286482341033411810537139)
            ·
              refine ⟨6429723511550117715805709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4286482341033411810537139 6429723511550117715805709)
              ·
                refine ⟨2411146316831294143427141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6429723511550117715805709 2411146316831294143427141)
                ·
                  refine ⟨452089934405867651892589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2411146316831294143427141 452089934405867651892589)
                  ·
                    rfl

theorem cell22_3961989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 2, 1, 3, 4].length) (baseStart_3961989 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3961989 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3961989 prefixEnd_3961989 := by exact prefixLift 3961989
  have htrace : WordTrace (prefixWord ++ tailWord_3961989) baseStart_3961989 baseEnd_3961989 := by
    simpa [prefixWord, tailWord_3961989, baseEnd_3961989] using wordTrace_append hprefix tailTrace_3961989
  have hstable : (prefixWord ++ tailWord_3961989).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3961989).length < 2 ^ (prefixWord ++ tailWord_3961989).sum := by decide
  have hdescent : baseEnd_3961989 < baseStart_3961989 := by decide
  rcases family_descends (prefixWord ++ tailWord_3961989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3962002 : List Nat := [3, 2, 3, 1, 1, 3, 1, 2, 2, 4]
def baseStart_3962002 : Nat := 118140960795 + 3962002 * 2 ^ 59
def prefixEnd_3962002 : Nat := 4983230072969 + 3 ^ 40 * 3962002 * 2
def baseEnd_3962002 : Nat := 1356274253383275255102727

theorem tailTrace_3962002 : CollatzResearch.WordTrace tailWord_3962002 prefixEnd_3962002 1356274253383275255102727 := by
  unfold tailWord_3962002
  simp only [CollatzResearch.WordTrace]
  refine ⟨36126521148087721228842065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96337389728233923276912173 36126521148087721228842065)
  ·
    refine ⟨27094890861065790921631549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36126521148087721228842065 27094890861065790921631549)
    ·
      refine ⟨10160584072899671595611831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27094890861065790921631549 10160584072899671595611831)
      ·
        refine ⟨15240876109349507393417747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10160584072899671595611831 15240876109349507393417747)
        ·
          refine ⟨22861314164024261090126621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15240876109349507393417747 22861314164024261090126621)
          ·
            refine ⟨8572992811509097908797483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22861314164024261090126621 8572992811509097908797483)
            ·
              refine ⟨12859489217263646863196225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8572992811509097908797483 12859489217263646863196225)
              ·
                refine ⟨9644616912947735147397169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12859489217263646863196225 9644616912947735147397169)
                ·
                  refine ⟨7233462684710801360547877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9644616912947735147397169 7233462684710801360547877)
                  ·
                    refine ⟨1356274253383275255102727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7233462684710801360547877 1356274253383275255102727)
                    ·
                      rfl

theorem cell22_3962002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 1, 2, 2, 4].length) (baseStart_3962002 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3962002 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3962002 prefixEnd_3962002 := by exact prefixLift 3962002
  have htrace : WordTrace (prefixWord ++ tailWord_3962002) baseStart_3962002 baseEnd_3962002 := by
    simpa [prefixWord, tailWord_3962002, baseEnd_3962002] using wordTrace_append hprefix tailTrace_3962002
  have hstable : (prefixWord ++ tailWord_3962002).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3962002).length < 2 ^ (prefixWord ++ tailWord_3962002).sum := by decide
  have hdescent : baseEnd_3962002 < baseStart_3962002 := by decide
  rcases family_descends (prefixWord ++ tailWord_3962002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3962028 : List Nat := [2, 2, 1, 1, 1, 1, 1, 4, 9]
def baseStart_3962028 : Nat := 118140960795 + 3962028 * 2 ^ 59
def prefixEnd_3962028 : Nat := 4983230072969 + 3 ^ 40 * 3962028 * 2
def baseEnd_3962028 : Nat := 452094384571539951317549

theorem tailTrace_3962028 : CollatzResearch.WordTrace tailWord_3962028 prefixEnd_3962028 452094384571539951317549 := by
  unfold tailWord_3962028
  simp only [CollatzResearch.WordTrace]
  refine ⟨72253516445128345677907369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96338021926837794237209825 72253516445128345677907369)
  ·
    refine ⟨54190137333846259258430527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72253516445128345677907369 54190137333846259258430527)
    ·
      refine ⟨81285206000769388887645791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54190137333846259258430527 81285206000769388887645791)
      ·
        refine ⟨121927809001154083331468687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81285206000769388887645791 121927809001154083331468687)
        ·
          refine ⟨182891713501731124997203031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121927809001154083331468687 182891713501731124997203031)
          ·
            refine ⟨274337570252596687495804547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 182891713501731124997203031 274337570252596687495804547)
            ·
              refine ⟨411506355378895031243706821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 274337570252596687495804547 411506355378895031243706821)
              ·
                refine ⟨77157441633542818358195029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 411506355378895031243706821 77157441633542818358195029)
                ·
                  refine ⟨452094384571539951317549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 77157441633542818358195029 452094384571539951317549)
                  ·
                    rfl

theorem cell22_3962028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 9].length) (baseStart_3962028 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3962028 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3962028 prefixEnd_3962028 := by exact prefixLift 3962028
  have htrace : WordTrace (prefixWord ++ tailWord_3962028) baseStart_3962028 baseEnd_3962028 := by
    simpa [prefixWord, tailWord_3962028, baseEnd_3962028] using wordTrace_append hprefix tailTrace_3962028
  have hstable : (prefixWord ++ tailWord_3962028).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3962028).length < 2 ^ (prefixWord ++ tailWord_3962028).sum := by decide
  have hdescent : baseEnd_3962028 < baseStart_3962028 := by decide
  rcases family_descends (prefixWord ++ tailWord_3962028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3962043 : List Nat := [1, 1, 1, 1, 1, 2, 4, 1, 3, 7]
def baseStart_3962043 : Nat := 118140960795 + 3962043 * 2 ^ 59
def prefixEnd_3962043 : Nat := 4983230072969 + 3 ^ 40 * 3962043 * 2
def baseEnd_3962043 : Nat := 1356288288521164814827601

theorem tailTrace_3962043 : CollatzResearch.WordTrace tailWord_3962043 prefixEnd_3962043 1356288288521164814827601 := by
  unfold tailWord_3962043
  simp only [CollatzResearch.WordTrace]
  refine ⟨144507579985202348917610783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96338386656801565945073855 144507579985202348917610783)
  ·
    refine ⟨216761369977803523376416175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144507579985202348917610783 216761369977803523376416175)
    ·
      refine ⟨325142054966705285064624263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216761369977803523376416175 325142054966705285064624263)
      ·
        refine ⟨487713082450057927596936395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 325142054966705285064624263 487713082450057927596936395)
        ·
          refine ⟨731569623675086891395404593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 487713082450057927596936395 731569623675086891395404593)
          ·
            refine ⟨548677217756315168546553445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 731569623675086891395404593 548677217756315168546553445)
            ·
              refine ⟨102876978329309094102478771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 548677217756315168546553445 102876978329309094102478771)
              ·
                refine ⟨154315467493963641153718157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 102876978329309094102478771 154315467493963641153718157)
                ·
                  refine ⟨57868300310236365432644309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 154315467493963641153718157 57868300310236365432644309)
                  ·
                    refine ⟨1356288288521164814827601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 57868300310236365432644309 1356288288521164814827601)
                    ·
                      rfl

theorem cell22_3962043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 1, 3, 7].length) (baseStart_3962043 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3962043 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3962043 prefixEnd_3962043 := by exact prefixLift 3962043
  have htrace : WordTrace (prefixWord ++ tailWord_3962043) baseStart_3962043 baseEnd_3962043 := by
    simpa [prefixWord, tailWord_3962043, baseEnd_3962043] using wordTrace_append hprefix tailTrace_3962043
  have hstable : (prefixWord ++ tailWord_3962043).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3962043).length < 2 ^ (prefixWord ++ tailWord_3962043).sum := by decide
  have hdescent : baseEnd_3962043 < baseStart_3962043 := by decide
  rcases family_descends (prefixWord ++ tailWord_3962043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3962090 : List Nat := [3, 1, 3, 1, 1, 3, 1, 1, 8]
def baseStart_3962090 : Nat := 118140960795 + 3962090 * 2 ^ 59
def prefixEnd_3962090 : Nat := 4983230072969 + 3 ^ 40 * 3962090 * 2
def baseEnd_3962090 : Nat := 452101459193890786300819

theorem tailTrace_3962090 : CollatzResearch.WordTrace tailWord_3962090 prefixEnd_3962090 452101459193890786300819 := by
  unfold tailWord_3962090
  simp only [CollatzResearch.WordTrace]
  refine ⟨36127323554008018986142931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96339529477354717296381149 36127323554008018986142931)
  ·
    refine ⟨54190985331012028479214397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36127323554008018986142931 54190985331012028479214397)
    ·
      refine ⟨20321619499129510679705399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54190985331012028479214397 20321619499129510679705399)
      ·
        refine ⟨30482429248694266019558099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20321619499129510679705399 30482429248694266019558099)
        ·
          refine ⟨45723643873041399029337149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30482429248694266019558099 45723643873041399029337149)
          ·
            refine ⟨17146366452390524636001431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45723643873041399029337149 17146366452390524636001431)
            ·
              refine ⟨25719549678585786954002147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17146366452390524636001431 25719549678585786954002147)
              ·
                refine ⟨38579324517878680431003221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25719549678585786954002147 38579324517878680431003221)
                ·
                  refine ⟨452101459193890786300819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 38579324517878680431003221 452101459193890786300819)
                  ·
                    rfl

theorem cell22_3962090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 1, 1, 8].length) (baseStart_3962090 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3962090 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3962090 prefixEnd_3962090 := by exact prefixLift 3962090
  have htrace : WordTrace (prefixWord ++ tailWord_3962090) baseStart_3962090 baseEnd_3962090 := by
    simpa [prefixWord, tailWord_3962090, baseEnd_3962090] using wordTrace_append hprefix tailTrace_3962090
  have hstable : (prefixWord ++ tailWord_3962090).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3962090).length < 2 ^ (prefixWord ++ tailWord_3962090).sum := by decide
  have hdescent : baseEnd_3962090 < baseStart_3962090 := by decide
  rcases family_descends (prefixWord ++ tailWord_3962090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3962105 : List Nat := [1, 2, 1, 3, 1, 1, 3, 4, 1, 5]
def baseStart_3962105 : Nat := 118140960795 + 3962105 * 2 ^ 59
def prefixEnd_3962105 : Nat := 4983230072969 + 3 ^ 40 * 3962105 * 2
def baseEnd_3962105 : Nat := 1356309512388217319777411

theorem tailTrace_3962105 : CollatzResearch.WordTrace tailWord_3962105 prefixEnd_3962105 1356309512388217319777411 := by
  unfold tailWord_3962105
  simp only [CollatzResearch.WordTrace]
  refine ⟨144509841310977733506367769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96339894207318489004245179 144509841310977733506367769)
  ·
    refine ⟨108382380983233300129775827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144509841310977733506367769 108382380983233300129775827)
    ·
      refine ⟨162573571474849950194663741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108382380983233300129775827 162573571474849950194663741)
      ·
        refine ⟨60965089303068731322998903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 162573571474849950194663741 60965089303068731322998903)
        ·
          refine ⟨91447633954603096984498355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60965089303068731322998903 91447633954603096984498355)
          ·
            refine ⟨137171450931904645476747533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91447633954603096984498355 137171450931904645476747533)
            ·
              refine ⟨51439294099464242053780325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 137171450931904645476747533 51439294099464242053780325)
              ·
                refine ⟨9644867643649545385083811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 51439294099464242053780325 9644867643649545385083811)
                ·
                  refine ⟨14467301465474318077625717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9644867643649545385083811 14467301465474318077625717)
                  ·
                    refine ⟨1356309512388217319777411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14467301465474318077625717 1356309512388217319777411)
                    ·
                      rfl

theorem cell22_3962105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 4, 1, 5].length) (baseStart_3962105 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3962105 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3962105 prefixEnd_3962105 := by exact prefixLift 3962105
  have htrace : WordTrace (prefixWord ++ tailWord_3962105) baseStart_3962105 baseEnd_3962105 := by
    simpa [prefixWord, tailWord_3962105, baseEnd_3962105] using wordTrace_append hprefix tailTrace_3962105
  have hstable : (prefixWord ++ tailWord_3962105).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3962105).length < 2 ^ (prefixWord ++ tailWord_3962105).sum := by decide
  have hdescent : baseEnd_3962105 < baseStart_3962105 := by decide
  rcases family_descends (prefixWord ++ tailWord_3962105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3962135 : List Nat := [1, 1, 3, 4, 1, 1, 2, 9]
def baseStart_3962135 : Nat := 118140960795 + 3962135 * 2 ^ 59
def prefixEnd_3962135 : Nat := 4983230072969 + 3 ^ 40 * 3962135 * 2
def baseEnd_3962135 : Nat := 150702198000145249058591

theorem tailTrace_3962135 : CollatzResearch.WordTrace tailWord_3962135 prefixEnd_3962135 150702198000145249058591 := by
  unfold tailWord_3962135
  simp only [CollatzResearch.WordTrace]
  refine ⟨144510935500869048629959859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96340623667246032419973239 144510935500869048629959859)
  ·
    refine ⟨216766403251303572944939789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144510935500869048629959859 216766403251303572944939789)
    ·
      refine ⟨81287401219238839854352421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 216766403251303572944939789 81287401219238839854352421)
      ·
        refine ⟨15241387728607282472691079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 81287401219238839854352421 15241387728607282472691079)
        ·
          refine ⟨22862081592910923709036619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15241387728607282472691079 22862081592910923709036619)
          ·
            refine ⟨34293122389366385563554929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22862081592910923709036619 34293122389366385563554929)
            ·
              refine ⟨25719841792024789172666197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34293122389366385563554929 25719841792024789172666197)
              ·
                refine ⟨150702198000145249058591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 25719841792024789172666197 150702198000145249058591)
                ·
                  rfl

theorem cell22_3962135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 2, 9].length) (baseStart_3962135 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3962135 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3962135 prefixEnd_3962135 := by exact prefixLift 3962135
  have htrace : WordTrace (prefixWord ++ tailWord_3962135) baseStart_3962135 baseEnd_3962135 := by
    simpa [prefixWord, tailWord_3962135, baseEnd_3962135] using wordTrace_append hprefix tailTrace_3962135
  have hstable : (prefixWord ++ tailWord_3962135).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3962135).length < 2 ^ (prefixWord ++ tailWord_3962135).sum := by decide
  have hdescent : baseEnd_3962135 < baseStart_3962135 := by decide
  rcases family_descends (prefixWord ++ tailWord_3962135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3962152 : List Nat := [2, 1, 5, 1, 2, 2, 1, 8]
def baseStart_3962152 : Nat := 118140960795 + 3962152 * 2 ^ 59
def prefixEnd_3962152 : Nat := 4983230072969 + 3 ^ 40 * 3962152 * 2
def baseEnd_3962152 : Nat := 150702844605413873761363

theorem tailTrace_3962152 : CollatzResearch.WordTrace tailWord_3962152 prefixEnd_3962152 150702844605413873761363 := by
  unfold tailWord_3962152
  simp only [CollatzResearch.WordTrace]
  refine ⟨72255777770903730266664355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96341037027871640355552473 72255777770903730266664355)
  ·
    refine ⟨108383666656355595399996533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72255777770903730266664355 108383666656355595399996533)
    ·
      refine ⟨10160968749033337068749675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 108383666656355595399996533 10160968749033337068749675)
      ·
        refine ⟨15241453123550005603124513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10160968749033337068749675 15241453123550005603124513)
        ·
          refine ⟨11431089842662504202343385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15241453123550005603124513 11431089842662504202343385)
          ·
            refine ⟨8573317381996878151757539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11431089842662504202343385 8573317381996878151757539)
            ·
              refine ⟨12859976072995317227636309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8573317381996878151757539 12859976072995317227636309)
              ·
                refine ⟨150702844605413873761363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12859976072995317227636309 150702844605413873761363)
                ·
                  rfl

theorem cell22_3962152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 1, 8].length) (baseStart_3962152 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3962152 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3962152 prefixEnd_3962152 := by exact prefixLift 3962152
  have htrace : WordTrace (prefixWord ++ tailWord_3962152) baseStart_3962152 baseEnd_3962152 := by
    simpa [prefixWord, tailWord_3962152, baseEnd_3962152] using wordTrace_append hprefix tailTrace_3962152
  have hstable : (prefixWord ++ tailWord_3962152).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3962152).length < 2 ^ (prefixWord ++ tailWord_3962152).sum := by decide
  have hdescent : baseEnd_3962152 < baseStart_3962152 := by decide
  rcases family_descends (prefixWord ++ tailWord_3962152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3962169 : List Nat := [1, 2, 1, 6, 3, 1, 8]
def baseStart_3962169 : Nat := 118140960795 + 3962169 * 2 ^ 59
def prefixEnd_3962169 : Nat := 4983230072969 + 3 ^ 40 * 3962169 * 2
def baseEnd_3962169 : Nat := 50234497070227499488045

theorem tailTrace_3962169 : CollatzResearch.WordTrace tailWord_3962169 prefixEnd_3962169 50234497070227499488045 := by
  unfold tailWord_3962169
  simp only [CollatzResearch.WordTrace]
  refine ⟨144512175582745872436697561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96341450388497248291131707 144512175582745872436697561)
  ·
    refine ⟨108384131687059404327523171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144512175582745872436697561 108384131687059404327523171)
    ·
      refine ⟨162576197530589106491284757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108384131687059404327523171 162576197530589106491284757)
      ·
        refine ⟨7620759259246364366778973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 162576197530589106491284757 7620759259246364366778973)
        ·
          refine ⟨2857784722217386637542115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7620759259246364366778973 2857784722217386637542115)
          ·
            refine ⟨4286677083326079956313173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2857784722217386637542115 4286677083326079956313173)
            ·
              refine ⟨50234497070227499488045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4286677083326079956313173 50234497070227499488045)
              ·
                rfl

theorem cell22_3962169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 3, 1, 8].length) (baseStart_3962169 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3962169 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3962169 prefixEnd_3962169 := by exact prefixLift 3962169
  have htrace : WordTrace (prefixWord ++ tailWord_3962169) baseStart_3962169 baseEnd_3962169 := by
    simpa [prefixWord, tailWord_3962169, baseEnd_3962169] using wordTrace_append hprefix tailTrace_3962169
  have hstable : (prefixWord ++ tailWord_3962169).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3962169).length < 2 ^ (prefixWord ++ tailWord_3962169).sum := by decide
  have hdescent : baseEnd_3962169 < baseStart_3962169 := by decide
  rcases family_descends (prefixWord ++ tailWord_3962169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3962195 : List Nat := [1, 1, 1, 2, 1, 1, 6, 1, 1, 7]
def baseStart_3962195 : Nat := 118140960795 + 3962195 * 2 ^ 59
def prefixEnd_3962195 : Nat := 4983230072969 + 3 ^ 40 * 3962195 * 2
def baseEnd_3962195 : Nat := 1356340321227487085027135

theorem tailTrace_3962195 : CollatzResearch.WordTrace tailWord_3962195 prefixEnd_3962195 1356340321227487085027135 := by
  unfold tailWord_3962195
  simp only [CollatzResearch.WordTrace]
  refine ⟨144513123880651678877144039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96342082587101119251429359 144513123880651678877144039)
  ·
    refine ⟨216769685820977518315716059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144513123880651678877144039 216769685820977518315716059)
    ·
      refine ⟨325154528731466277473574089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216769685820977518315716059 325154528731466277473574089)
      ·
        refine ⟨243865896548599708105180567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 325154528731466277473574089 243865896548599708105180567)
        ·
          refine ⟨365798844822899562157770851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 243865896548599708105180567 365798844822899562157770851)
          ·
            refine ⟨548698267234349343236656277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 365798844822899562157770851 548698267234349343236656277)
            ·
              refine ⟨25720231276610125464218263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 548698267234349343236656277 25720231276610125464218263)
              ·
                refine ⟨38580346914915188196327395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25720231276610125464218263 38580346914915188196327395)
                ·
                  refine ⟨57870520372372782294491093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38580346914915188196327395 57870520372372782294491093)
                  ·
                    refine ⟨1356340321227487085027135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 57870520372372782294491093 1356340321227487085027135)
                    ·
                      rfl

theorem cell22_3962195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 6, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 6, 1, 1, 7].length) (baseStart_3962195 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3962195 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3962195 prefixEnd_3962195 := by exact prefixLift 3962195
  have htrace : WordTrace (prefixWord ++ tailWord_3962195) baseStart_3962195 baseEnd_3962195 := by
    simpa [prefixWord, tailWord_3962195, baseEnd_3962195] using wordTrace_append hprefix tailTrace_3962195
  have hstable : (prefixWord ++ tailWord_3962195).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3962195).length < 2 ^ (prefixWord ++ tailWord_3962195).sum := by decide
  have hdescent : baseEnd_3962195 < baseStart_3962195 := by decide
  rcases family_descends (prefixWord ++ tailWord_3962195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3962272 : List Nat := [2, 1, 1, 4, 1, 2, 3, 1, 1, 6]
def baseStart_3962272 : Nat := 118140960795 + 3962272 * 2 ^ 59
def prefixEnd_3962272 : Nat := 4983230072969 + 3 ^ 40 * 3962272 * 2
def baseEnd_3962272 : Nat := 1356366679901084550851899

theorem tailTrace_3962272 : CollatzResearch.WordTrace tailWord_3962272 prefixEnd_3962272 1356366679901084550851899 := by
  unfold tailWord_3962272
  simp only [CollatzResearch.WordTrace]
  refine ⟨72257966150686360513848535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96343954867581814018464713 72257966150686360513848535)
  ·
    refine ⟨108386949226029540770772803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72257966150686360513848535 108386949226029540770772803)
    ·
      refine ⟨162580423839044311156159205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108386949226029540770772803 162580423839044311156159205)
      ·
        refine ⟨30483829469820808341779851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 162580423839044311156159205 30483829469820808341779851)
        ·
          refine ⟨45725744204731212512669777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30483829469820808341779851 45725744204731212512669777)
          ·
            refine ⟨34294308153548409384502333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45725744204731212512669777 34294308153548409384502333)
            ·
              refine ⟨12860365557580653519188375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34294308153548409384502333 12860365557580653519188375)
              ·
                refine ⟨19290548336370980278782563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12860365557580653519188375 19290548336370980278782563)
                ·
                  refine ⟨28935822504556470418173845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19290548336370980278782563 28935822504556470418173845)
                  ·
                    refine ⟨1356366679901084550851899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28935822504556470418173845 1356366679901084550851899)
                    ·
                      rfl

theorem cell22_3962272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 3, 1, 1, 6].length) (baseStart_3962272 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3962272 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3962272 prefixEnd_3962272 := by exact prefixLift 3962272
  have htrace : WordTrace (prefixWord ++ tailWord_3962272) baseStart_3962272 baseEnd_3962272 := by
    simpa [prefixWord, tailWord_3962272, baseEnd_3962272] using wordTrace_append hprefix tailTrace_3962272
  have hstable : (prefixWord ++ tailWord_3962272).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3962272).length < 2 ^ (prefixWord ++ tailWord_3962272).sum := by decide
  have hdescent : baseEnd_3962272 < baseStart_3962272 := by decide
  rcases family_descends (prefixWord ++ tailWord_3962272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3962274 : List Nat := [3, 3, 1, 2, 1, 2, 2, 2, 1, 5]
def baseStart_3962274 : Nat := 118140960795 + 3962274 * 2 ^ 59
def prefixEnd_3962274 : Nat := 4983230072969 + 3 ^ 40 * 3962274 * 2
def baseEnd_3962274 : Nat := 1356367364541957212301893

theorem tailTrace_3962274 : CollatzResearch.WordTrace tailWord_3962274 prefixEnd_3962274 1356367364541957212301893 := by
  unfold tailWord_3962274
  simp only [CollatzResearch.WordTrace]
  refine ⟨36129001311841368842317469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96344003498243650246179917 36129001311841368842317469)
  ·
    refine ⟨13548375491940513315869051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36129001311841368842317469 13548375491940513315869051)
    ·
      refine ⟨20322563237910769973803577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13548375491940513315869051 20322563237910769973803577)
      ·
        refine ⟨15241922428433077480352683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20322563237910769973803577 15241922428433077480352683)
        ·
          refine ⟨22862883642649616220529025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15241922428433077480352683 22862883642649616220529025)
          ·
            refine ⟨17147162731987212165396769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22862883642649616220529025 17147162731987212165396769)
            ·
              refine ⟨12860372048990409124047577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17147162731987212165396769 12860372048990409124047577)
              ·
                refine ⟨9645279036742806843035683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12860372048990409124047577 9645279036742806843035683)
                ·
                  refine ⟨14467918555114210264553525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9645279036742806843035683 14467918555114210264553525)
                  ·
                    refine ⟨1356367364541957212301893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14467918555114210264553525 1356367364541957212301893)
                    ·
                      rfl

theorem cell22_3962274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 2, 2, 1, 5].length) (baseStart_3962274 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3962274 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3962274 prefixEnd_3962274 := by exact prefixLift 3962274
  have htrace : WordTrace (prefixWord ++ tailWord_3962274) baseStart_3962274 baseEnd_3962274 := by
    simpa [prefixWord, tailWord_3962274, baseEnd_3962274] using wordTrace_append hprefix tailTrace_3962274
  have hstable : (prefixWord ++ tailWord_3962274).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3962274).length < 2 ^ (prefixWord ++ tailWord_3962274).sum := by decide
  have hdescent : baseEnd_3962274 < baseStart_3962274 := by decide
  rcases family_descends (prefixWord ++ tailWord_3962274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3962319 : List Nat := [1, 1, 2, 1, 1, 4, 4, 2, 3, 3]
def baseStart_3962319 : Nat := 118140960795 + 3962319 * 2 ^ 59
def prefixEnd_3962319 : Nat := 4983230072969 + 3 ^ 40 * 3962319 * 2
def baseEnd_3962319 : Nat := 1356382768961592094926755

theorem tailTrace_3962319 : CollatzResearch.WordTrace tailWord_3962319 prefixEnd_3962319 1356382768961592094926755 := by
  unfold tailWord_3962319
  simp only [CollatzResearch.WordTrace]
  refine ⟨144517646532202448054658011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96345097688134965369772007 144517646532202448054658011)
  ·
    refine ⟨216776469798303672081987017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144517646532202448054658011 216776469798303672081987017)
    ·
      refine ⟨162582352348727754061490263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 216776469798303672081987017 162582352348727754061490263)
      ·
        refine ⟨243873528523091631092235395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162582352348727754061490263 243873528523091631092235395)
        ·
          refine ⟨365810292784637446638353093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 243873528523091631092235395 365810292784637446638353093)
          ·
            refine ⟨68589429897119521244691205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 365810292784637446638353093 68589429897119521244691205)
            ·
              refine ⟨12860518105709910233379601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 68589429897119521244691205 12860518105709910233379601)
              ·
                refine ⟨9645388579282432675034701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12860518105709910233379601 9645388579282432675034701)
                ·
                  refine ⟨3617020717230912253138013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9645388579282432675034701 3617020717230912253138013)
                  ·
                    refine ⟨1356382768961592094926755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3617020717230912253138013 1356382768961592094926755)
                    ·
                      rfl

theorem cell22_3962319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 4, 2, 3, 3].length) (baseStart_3962319 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3962319 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3962319 prefixEnd_3962319 := by exact prefixLift 3962319
  have htrace : WordTrace (prefixWord ++ tailWord_3962319) baseStart_3962319 baseEnd_3962319 := by
    simpa [prefixWord, tailWord_3962319, baseEnd_3962319] using wordTrace_append hprefix tailTrace_3962319
  have hstable : (prefixWord ++ tailWord_3962319).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3962319).length < 2 ^ (prefixWord ++ tailWord_3962319).sum := by decide
  have hdescent : baseEnd_3962319 < baseStart_3962319 := by decide
  rcases family_descends (prefixWord ++ tailWord_3962319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3962336 : List Nat := [2, 1, 1, 3, 1, 1, 2, 7, 1, 3]
def baseStart_3962336 : Nat := 118140960795 + 3962336 * 2 ^ 59
def prefixEnd_3962336 : Nat := 4983230072969 + 3 ^ 40 * 3962336 * 2
def baseEnd_3962336 : Nat := 1356388588409009717251703

theorem tailTrace_3962336 : CollatzResearch.WordTrace tailWord_3962336 prefixEnd_3962336 1356388588409009717251703 := by
  unfold tailWord_3962336
  simp only [CollatzResearch.WordTrace]
  refine ⟨72259133286570429979013431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96345511048760573305351241 72259133286570429979013431)
  ·
    refine ⟨108388699929855644968520147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72259133286570429979013431 108388699929855644968520147)
    ·
      refine ⟨162583049894783467452780221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108388699929855644968520147 162583049894783467452780221)
      ·
        refine ⟨60968643710543800294792583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 162583049894783467452780221 60968643710543800294792583)
        ·
          refine ⟨91452965565815700442188875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60968643710543800294792583 91452965565815700442188875)
          ·
            refine ⟨137179448348723550663283313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91452965565815700442188875 137179448348723550663283313)
            ·
              refine ⟨102884586261542662997462485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 137179448348723550663283313 102884586261542662997462485)
              ·
                refine ⟨2411357490504906164003027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 102884586261542662997462485 2411357490504906164003027)
                ·
                  refine ⟨3617036235757359246004541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2411357490504906164003027 3617036235757359246004541)
                  ·
                    refine ⟨1356388588409009717251703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3617036235757359246004541 1356388588409009717251703)
                    ·
                      rfl

theorem cell22_3962336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 7, 1, 3].length) (baseStart_3962336 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3962336 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3962336 prefixEnd_3962336 := by exact prefixLift 3962336
  have htrace : WordTrace (prefixWord ++ tailWord_3962336) baseStart_3962336 baseEnd_3962336 := by
    simpa [prefixWord, tailWord_3962336, baseEnd_3962336] using wordTrace_append hprefix tailTrace_3962336
  have hstable : (prefixWord ++ tailWord_3962336).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3962336).length < 2 ^ (prefixWord ++ tailWord_3962336).sum := by decide
  have hdescent : baseEnd_3962336 < baseStart_3962336 := by decide
  rcases family_descends (prefixWord ++ tailWord_3962336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3962347 : List Nat := [1, 1, 1, 1, 2, 3, 2, 4, 2, 5]
def baseStart_3962347 : Nat := 118140960795 + 3962347 * 2 ^ 59
def prefixEnd_3962347 : Nat := 4983230072969 + 3 ^ 40 * 3962347 * 2
def baseEnd_3962347 : Nat := 1356392353933809355226669

theorem tailTrace_3962347 : CollatzResearch.WordTrace tailWord_3962347 prefixEnd_3962347 1356392353933809355226669 := by
  unfold tailWord_3962347
  simp only [CollatzResearch.WordTrace]
  refine ⟨144518667776101008836677295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96345778517400672557784863 144518667776101008836677295)
  ·
    refine ⟨216778001664151513255015943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144518667776101008836677295 216778001664151513255015943)
    ·
      refine ⟨325167002496227269882523915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216778001664151513255015943 325167002496227269882523915)
      ·
        refine ⟨487750503744340904823785873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 325167002496227269882523915 487750503744340904823785873)
        ·
          refine ⟨365812877808255678617839405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 487750503744340904823785873 365812877808255678617839405)
          ·
            refine ⟨137179829178095879481689777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 365812877808255678617839405 137179829178095879481689777)
            ·
              refine ⟨102884871883571909611267333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 137179829178095879481689777 102884871883571909611267333)
              ·
                refine ⟨19290913478169733052112625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 102884871883571909611267333 19290913478169733052112625)
                ·
                  refine ⟨14468185108627299789084469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19290913478169733052112625 14468185108627299789084469)
                  ·
                    refine ⟨1356392353933809355226669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14468185108627299789084469 1356392353933809355226669)
                    ·
                      rfl

theorem cell22_3962347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 4, 2, 5].length) (baseStart_3962347 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3962347 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3962347 prefixEnd_3962347 := by exact prefixLift 3962347
  have htrace : WordTrace (prefixWord ++ tailWord_3962347) baseStart_3962347 baseEnd_3962347 := by
    simpa [prefixWord, tailWord_3962347, baseEnd_3962347] using wordTrace_append hprefix tailTrace_3962347
  have hstable : (prefixWord ++ tailWord_3962347).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3962347).length < 2 ^ (prefixWord ++ tailWord_3962347).sum := by decide
  have hdescent : baseEnd_3962347 < baseStart_3962347 := by decide
  rcases family_descends (prefixWord ++ tailWord_3962347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3962377 : List Nat := [1, 2, 1, 1, 3, 1, 4, 1, 8]
def baseStart_3962377 : Nat := 118140960795 + 3962377 * 2 ^ 59
def prefixEnd_3962377 : Nat := 4983230072969 + 3 ^ 40 * 3962377 * 2
def baseEnd_3962377 : Nat := 452134207848966425658859

theorem tailTrace_3962377 : CollatzResearch.WordTrace tailWord_3962377 prefixEnd_3962377 452134207848966425658859 := by
  unfold tailWord_3962377
  simp only [CollatzResearch.WordTrace]
  refine ⟨144519761965992323960269385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96346507977328215973512923 144519761965992323960269385)
  ·
    refine ⟨108389821474494242970202039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144519761965992323960269385 108389821474494242970202039)
    ·
      refine ⟨162584732211741364455303059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108389821474494242970202039 162584732211741364455303059)
      ·
        refine ⟨243877098317612046682954589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162584732211741364455303059 243877098317612046682954589)
        ·
          refine ⟨91453911869104517506107971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 243877098317612046682954589 91453911869104517506107971)
          ·
            refine ⟨137180867803656776259161957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91453911869104517506107971 137180867803656776259161957)
            ·
              refine ⟨25721412713185645548592867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 137180867803656776259161957 25721412713185645548592867)
              ·
                refine ⟨38582119069778468322889301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25721412713185645548592867 38582119069778468322889301)
                ·
                  refine ⟨452134207848966425658859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 38582119069778468322889301 452134207848966425658859)
                  ·
                    rfl

theorem cell22_3962377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 4, 1, 8].length) (baseStart_3962377 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3962377 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3962377 prefixEnd_3962377 := by exact prefixLift 3962377
  have htrace : WordTrace (prefixWord ++ tailWord_3962377) baseStart_3962377 baseEnd_3962377 := by
    simpa [prefixWord, tailWord_3962377, baseEnd_3962377] using wordTrace_append hprefix tailTrace_3962377
  have hstable : (prefixWord ++ tailWord_3962377).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3962377).length < 2 ^ (prefixWord ++ tailWord_3962377).sum := by decide
  have hdescent : baseEnd_3962377 < baseStart_3962377 := by decide
  rcases family_descends (prefixWord ++ tailWord_3962377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3962426 : List Nat := [3, 1, 1, 1, 3, 2, 1, 5, 2, 3]
def baseStart_3962426 : Nat := 118140960795 + 3962426 * 2 ^ 59
def prefixEnd_3962426 : Nat := 4983230072969 + 3 ^ 40 * 3962426 * 2
def baseEnd_3962426 : Nat := 1356419397248279482501427

theorem tailTrace_3962426 : CollatzResearch.WordTrace tailWord_3962426 prefixEnd_3962426 1356419397248279482501427 := by
  unfold tailWord_3962426
  simp only [CollatzResearch.WordTrace]
  refine ⟨36130387285703701332200783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96347699428543203552535421 36130387285703701332200783)
  ·
    refine ⟨54195580928555551998301175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36130387285703701332200783 54195580928555551998301175)
    ·
      refine ⟨81293371392833327997451763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54195580928555551998301175 81293371392833327997451763)
      ·
        refine ⟨121940057089249991996177645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81293371392833327997451763 121940057089249991996177645)
        ·
          refine ⟨45727521408468746998566617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 121940057089249991996177645 45727521408468746998566617)
          ·
            refine ⟨34295641056351560248924963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45727521408468746998566617 34295641056351560248924963)
            ·
              refine ⟨51443461584527340373387445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34295641056351560248924963 51443461584527340373387445)
              ·
                refine ⟨4822824523549438160005073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 51443461584527340373387445 4822824523549438160005073)
                ·
                  refine ⟨3617118392662078620003805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4822824523549438160005073 3617118392662078620003805)
                  ·
                    refine ⟨1356419397248279482501427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3617118392662078620003805 1356419397248279482501427)
                    ·
                      rfl

theorem cell22_3962426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 5, 2, 3].length) (baseStart_3962426 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3962426 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3962426 prefixEnd_3962426 := by exact prefixLift 3962426
  have htrace : WordTrace (prefixWord ++ tailWord_3962426) baseStart_3962426 baseEnd_3962426 := by
    simpa [prefixWord, tailWord_3962426, baseEnd_3962426] using wordTrace_append hprefix tailTrace_3962426
  have hstable : (prefixWord ++ tailWord_3962426).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3962426).length < 2 ^ (prefixWord ++ tailWord_3962426).sum := by decide
  have hdescent : baseEnd_3962426 < baseStart_3962426 := by decide
  rcases family_descends (prefixWord ++ tailWord_3962426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3962445 : List Nat := [1, 6, 1, 1, 3, 1, 2, 3, 4]
def baseStart_3962445 : Nat := 118140960795 + 3962445 * 2 ^ 59
def prefixEnd_3962445 : Nat := 4983230072969 + 3 ^ 40 * 3962445 * 2
def baseEnd_3962445 : Nat := 452141967112189922092123

theorem tailTrace_3962445 : CollatzResearch.WordTrace tailWord_3962445 prefixEnd_3962445 452141967112189922092123 := by
  unfold tailWord_3962445
  simp only [CollatzResearch.WordTrace]
  refine ⟨144522242129745971573744789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96348161419830647715829859 144522242129745971573744789)
  ·
    refine ⟨6774480099831842417519287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 144522242129745971573744789 6774480099831842417519287)
    ·
      refine ⟨10161720149747763626278931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6774480099831842417519287 10161720149747763626278931)
      ·
        refine ⟨15242580224621645439418397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10161720149747763626278931 15242580224621645439418397)
        ·
          refine ⟨5715967584233117039781899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15242580224621645439418397 5715967584233117039781899)
          ·
            refine ⟨8573951376349675559672849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5715967584233117039781899 8573951376349675559672849)
            ·
              refine ⟨6430463532262256669754637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8573951376349675559672849 6430463532262256669754637)
              ·
                refine ⟨2411423824598346251157989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6430463532262256669754637 2411423824598346251157989)
                ·
                  refine ⟨452141967112189922092123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2411423824598346251157989 452141967112189922092123)
                  ·
                    rfl

theorem cell22_3962445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 2, 3, 4].length) (baseStart_3962445 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3962445 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3962445 prefixEnd_3962445 := by exact prefixLift 3962445
  have htrace : WordTrace (prefixWord ++ tailWord_3962445) baseStart_3962445 baseEnd_3962445 := by
    simpa [prefixWord, tailWord_3962445, baseEnd_3962445] using wordTrace_append hprefix tailTrace_3962445
  have hstable : (prefixWord ++ tailWord_3962445).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3962445).length < 2 ^ (prefixWord ++ tailWord_3962445).sum := by decide
  have hdescent : baseEnd_3962445 < baseStart_3962445 := by decide
  rcases family_descends (prefixWord ++ tailWord_3962445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3962460 : List Nat := [2, 2, 4, 1, 2, 3, 1, 2, 2, 3]
def baseStart_3962460 : Nat := 118140960795 + 3962460 * 2 ^ 59
def prefixEnd_3962460 : Nat := 4983230072969 + 3 ^ 40 * 3962460 * 2
def baseEnd_3962460 : Nat := 1356431036143114727151323

theorem tailTrace_3962460 : CollatzResearch.WordTrace tailWord_3962460 prefixEnd_3962460 1356431036143114727151323 := by
  unfold tailWord_3962460
  simp only [CollatzResearch.WordTrace]
  refine ⟨72261394612345814567770417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96348526149794419423693889 72261394612345814567770417)
  ·
    refine ⟨54196045959259360925827813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72261394612345814567770417 54196045959259360925827813)
    ·
      refine ⟨10161758617361130173592715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 54196045959259360925827813 10161758617361130173592715)
      ·
        refine ⟨15242637926041695260389073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10161758617361130173592715 15242637926041695260389073)
        ·
          refine ⟨11431978444531271445291805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15242637926041695260389073 11431978444531271445291805)
          ·
            refine ⟨4286991916699226791984427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11431978444531271445291805 4286991916699226791984427)
            ·
              refine ⟨6430487875048840187976641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4286991916699226791984427 6430487875048840187976641)
              ·
                refine ⟨4822865906286630140982481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6430487875048840187976641 4822865906286630140982481)
                ·
                  refine ⟨3617149429714972605736861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4822865906286630140982481 3617149429714972605736861)
                  ·
                    refine ⟨1356431036143114727151323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3617149429714972605736861 1356431036143114727151323)
                    ·
                      rfl

theorem cell22_3962460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 3, 1, 2, 2, 3].length) (baseStart_3962460 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3962460 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3962460 prefixEnd_3962460 := by exact prefixLift 3962460
  have htrace : WordTrace (prefixWord ++ tailWord_3962460) baseStart_3962460 baseEnd_3962460 := by
    simpa [prefixWord, tailWord_3962460, baseEnd_3962460] using wordTrace_append hprefix tailTrace_3962460
  have hstable : (prefixWord ++ tailWord_3962460).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3962460).length < 2 ^ (prefixWord ++ tailWord_3962460).sum := by decide
  have hdescent : baseEnd_3962460 < baseStart_3962460 := by decide
  rcases family_descends (prefixWord ++ tailWord_3962460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3962471 : List Nat := [1, 1, 5, 1, 1, 1, 3, 3, 3, 3]
def baseStart_3962471 : Nat := 118140960795 + 3962471 * 2 ^ 59
def prefixEnd_3962471 : Nat := 4983230072969 + 3 ^ 40 * 3962471 * 2
def baseEnd_3962471 : Nat := 1356434801667914365126289

theorem tailTrace_3962471 : CollatzResearch.WordTrace tailWord_3962471 prefixEnd_3962471 1356434801667914365126289 := by
  unfold tailWord_3962471
  simp only [CollatzResearch.WordTrace]
  refine ⟨144523190427651778014191267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96348793618434518676127511 144523190427651778014191267)
  ·
    refine ⟨216784785641477667021286901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144523190427651778014191267 216784785641477667021286901)
    ·
      refine ⟨20323573653888531283245647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 216784785641477667021286901 20323573653888531283245647)
      ·
        refine ⟨30485360480832796924868471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20323573653888531283245647 30485360480832796924868471)
        ·
          refine ⟨45728040721249195387302707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30485360480832796924868471 45728040721249195387302707)
          ·
            refine ⟨68592061081873793080954061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45728040721249195387302707 68592061081873793080954061)
            ·
              refine ⟨25722022905702672405357773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68592061081873793080954061 25722022905702672405357773)
              ·
                refine ⟨9645758589638502152009165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25722022905702672405357773 9645758589638502152009165)
                ·
                  refine ⟨3617159471114438307003437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9645758589638502152009165 3617159471114438307003437)
                  ·
                    refine ⟨1356434801667914365126289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3617159471114438307003437 1356434801667914365126289)
                    ·
                      rfl

theorem cell22_3962471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 3, 3, 3, 3].length) (baseStart_3962471 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3962471 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3962471 prefixEnd_3962471 := by exact prefixLift 3962471
  have htrace : WordTrace (prefixWord ++ tailWord_3962471) baseStart_3962471 baseEnd_3962471 := by
    simpa [prefixWord, tailWord_3962471, baseEnd_3962471] using wordTrace_append hprefix tailTrace_3962471
  have hstable : (prefixWord ++ tailWord_3962471).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3962471).length < 2 ^ (prefixWord ++ tailWord_3962471).sum := by decide
  have hdescent : baseEnd_3962471 < baseStart_3962471 := by decide
  rcases family_descends (prefixWord ++ tailWord_3962471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3962580 : List Nat := [2, 4, 1, 3, 1, 2, 1, 4, 4]
def baseStart_3962580 : Nat := 118140960795 + 3962580 * 2 ^ 59
def prefixEnd_3962580 : Nat := 4983230072969 + 3 ^ 40 * 3962580 * 2
def baseEnd_3962580 : Nat := 452157371531824804716985

theorem tailTrace_3962580 : CollatzResearch.WordTrace tailWord_3962580 prefixEnd_3962580 452157371531824804716985 := by
  unfold tailWord_3962580
  simp only [CollatzResearch.WordTrace]
  refine ⟨72263582992128444814954597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96351443989504593086606129 72263582992128444814954597)
  ·
    refine ⟨13549421811024083402803987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 72263582992128444814954597 13549421811024083402803987)
    ·
      refine ⟨20324132716536125104205981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13549421811024083402803987 20324132716536125104205981)
      ·
        refine ⟨7621549768701046914077243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20324132716536125104205981 7621549768701046914077243)
        ·
          refine ⟨11432324653051570371115865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7621549768701046914077243 11432324653051570371115865)
          ·
            refine ⟨8574243489788677778336899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11432324653051570371115865 8574243489788677778336899)
            ·
              refine ⟨12861365234683016667505349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8574243489788677778336899 12861365234683016667505349)
              ·
                refine ⟨2411505981503065625157253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12861365234683016667505349 2411505981503065625157253)
                ·
                  refine ⟨452157371531824804716985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2411505981503065625157253 452157371531824804716985)
                  ·
                    rfl

theorem cell22_3962580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 1, 4, 4].length) (baseStart_3962580 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3962580 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3962580 prefixEnd_3962580 := by exact prefixLift 3962580
  have htrace : WordTrace (prefixWord ++ tailWord_3962580) baseStart_3962580 baseEnd_3962580 := by
    simpa [prefixWord, tailWord_3962580, baseEnd_3962580] using wordTrace_append hprefix tailTrace_3962580
  have hstable : (prefixWord ++ tailWord_3962580).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3962580).length < 2 ^ (prefixWord ++ tailWord_3962580).sum := by decide
  have hdescent : baseEnd_3962580 < baseStart_3962580 := by decide
  rcases family_descends (prefixWord ++ tailWord_3962580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3962760 : List Nat := [2, 1, 3, 3, 3, 2, 1, 7]
def baseStart_3962760 : Nat := 118140960795 + 3962760 * 2 ^ 59
def prefixEnd_3962760 : Nat := 4983230072969 + 3 ^ 40 * 3962760 * 2
def baseEnd_3962760 : Nat := 150725970252668216072267

theorem tailTrace_3962760 : CollatzResearch.WordTrace tailWord_3962760 prefixEnd_3962760 150725970252668216072267 := by
  unfold tailWord_3962760
  simp only [CollatzResearch.WordTrace]
  refine ⟨72266865561802390185730867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96355820749069853580974489 72266865561802390185730867)
  ·
    refine ⟨108400298342703585278596301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72266865561802390185730867 108400298342703585278596301)
    ·
      refine ⟨40650111878513844479473613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 108400298342703585278596301 40650111878513844479473613)
      ·
        refine ⟨15243791954442691679802605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40650111878513844479473613 15243791954442691679802605)
        ·
          refine ⟨5716421982916009379925977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15243791954442691679802605 5716421982916009379925977)
          ·
            refine ⟨4287316487187007034944483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5716421982916009379925977 4287316487187007034944483)
            ·
              refine ⟨6430974730780510552416725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4287316487187007034944483 6430974730780510552416725)
              ·
                refine ⟨150725970252668216072267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6430974730780510552416725 150725970252668216072267)
                ·
                  rfl

theorem cell22_3962760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 2, 1, 7].length) (baseStart_3962760 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3962760 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3962760 prefixEnd_3962760 := by exact prefixLift 3962760
  have htrace : WordTrace (prefixWord ++ tailWord_3962760) baseStart_3962760 baseEnd_3962760 := by
    simpa [prefixWord, tailWord_3962760, baseEnd_3962760] using wordTrace_append hprefix tailTrace_3962760
  have hstable : (prefixWord ++ tailWord_3962760).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3962760).length < 2 ^ (prefixWord ++ tailWord_3962760).sum := by decide
  have hdescent : baseEnd_3962760 < baseStart_3962760 := by decide
  rcases family_descends (prefixWord ++ tailWord_3962760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3962775 : List Nat := [1, 1, 3, 3, 1, 4, 1, 2, 3, 3]
def baseStart_3962775 : Nat := 118140960795 + 3962775 * 2 ^ 59
def prefixEnd_3962775 : Nat := 4983230072969 + 3 ^ 40 * 3962775 * 2
def baseEnd_3962775 : Nat := 1356538867080558905525357

theorem tailTrace_3962775 : CollatzResearch.WordTrace tailWord_3962775 prefixEnd_3962775 1356538867080558905525357 := by
  unfold tailWord_3962775
  simp only [CollatzResearch.WordTrace]
  refine ⟨144534278218550437933257779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96356185479033625288838519 144534278218550437933257779)
  ·
    refine ⟨216801417327825656899886669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144534278218550437933257779 216801417327825656899886669)
    ·
      refine ⟨81300531497934621337457501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 216801417327825656899886669 81300531497934621337457501)
      ·
        refine ⟨30487699311725483001546563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81300531497934621337457501 30487699311725483001546563)
        ·
          refine ⟨45731548967588224502319845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30487699311725483001546563 45731548967588224502319845)
          ·
            refine ⟨8574665431422792094184971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45731548967588224502319845 8574665431422792094184971)
            ·
              refine ⟨12861998147134188141277457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8574665431422792094184971 12861998147134188141277457)
              ·
                refine ⟨9646498610350641105958093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12861998147134188141277457 9646498610350641105958093)
                ·
                  refine ⟨3617436978881490414734285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9646498610350641105958093 3617436978881490414734285)
                  ·
                    refine ⟨1356538867080558905525357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3617436978881490414734285 1356538867080558905525357)
                    ·
                      rfl

theorem cell22_3962775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 1, 2, 3, 3].length) (baseStart_3962775 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3962775 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3962775 prefixEnd_3962775 := by exact prefixLift 3962775
  have htrace : WordTrace (prefixWord ++ tailWord_3962775) baseStart_3962775 baseEnd_3962775 := by
    simpa [prefixWord, tailWord_3962775, baseEnd_3962775] using wordTrace_append hprefix tailTrace_3962775
  have hstable : (prefixWord ++ tailWord_3962775).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3962775).length < 2 ^ (prefixWord ++ tailWord_3962775).sum := by decide
  have hdescent : baseEnd_3962775 < baseStart_3962775 := by decide
  rcases family_descends (prefixWord ++ tailWord_3962775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3962798 : List Nat := [4, 1, 5, 1, 1, 2, 1, 2, 2, 3]
def baseStart_3962798 : Nat := 118140960795 + 3962798 * 2 ^ 59
def prefixEnd_3962798 : Nat := 4983230072969 + 3 ^ 40 * 3962798 * 2
def baseEnd_3962798 : Nat := 1356546740450594512200287

theorem tailTrace_3962798 : CollatzResearch.WordTrace tailWord_3962798 prefixEnd_3962798 1356546740450594512200287 := by
  unfold tailWord_3962798
  simp only [CollatzResearch.WordTrace]
  refine ⟨18066889637183389107668131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 96356744731644741907563365 18066889637183389107668131)
  ·
    refine ⟨27100334455775083661502197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18066889637183389107668131 27100334455775083661502197)
    ·
      refine ⟨2540656355228914093265831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 27100334455775083661502197 2540656355228914093265831)
      ·
        refine ⟨3810984532843371139898747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2540656355228914093265831 3810984532843371139898747)
        ·
          refine ⟨5716476799265056709848121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3810984532843371139898747 5716476799265056709848121)
          ·
            refine ⟨4287357599448792532386091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5716476799265056709848121 4287357599448792532386091)
            ·
              refine ⟨6431036399173188798579137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4287357599448792532386091 6431036399173188798579137)
              ·
                refine ⟨4823277299379891598934353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6431036399173188798579137 4823277299379891598934353)
                ·
                  refine ⟨3617457974534918699200765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4823277299379891598934353 3617457974534918699200765)
                  ·
                    refine ⟨1356546740450594512200287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3617457974534918699200765 1356546740450594512200287)
                    ·
                      rfl

theorem cell22_3962798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 2, 1, 2, 2, 3].length) (baseStart_3962798 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3962798 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3962798 prefixEnd_3962798 := by exact prefixLift 3962798
  have htrace : WordTrace (prefixWord ++ tailWord_3962798) baseStart_3962798 baseEnd_3962798 := by
    simpa [prefixWord, tailWord_3962798, baseEnd_3962798] using wordTrace_append hprefix tailTrace_3962798
  have hstable : (prefixWord ++ tailWord_3962798).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3962798).length < 2 ^ (prefixWord ++ tailWord_3962798).sum := by decide
  have hdescent : baseEnd_3962798 < baseStart_3962798 := by decide
  rcases family_descends (prefixWord ++ tailWord_3962798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3962805 : List Nat := [1, 3, 3, 2, 1, 2, 3, 2, 5]
def baseStart_3962805 : Nat := 118140960795 + 3962805 * 2 ^ 59
def prefixEnd_3962805 : Nat := 4983230072969 + 3 ^ 40 * 3962805 * 2
def baseEnd_3962805 : Nat := 452183045564549609091755

theorem tailTrace_3962805 : CollatzResearch.WordTrace tailWord_3962805 prefixEnd_3962805 452183045564549609091755 := by
  unfold tailWord_3962805
  simp only [CollatzResearch.WordTrace]
  refine ⟨144535372408441753056849869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96356914938961168704566579 144535372408441753056849869)
  ·
    refine ⟨54200764653165657396318701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 144535372408441753056849869 54200764653165657396318701)
    ·
      refine ⟨20325286744937121523619513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54200764653165657396318701 20325286744937121523619513)
      ·
        refine ⟨15243965058702841142714635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20325286744937121523619513 15243965058702841142714635)
        ·
          refine ⟨22865947588054261714071953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15243965058702841142714635 22865947588054261714071953)
          ·
            refine ⟨17149460691040696285553965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22865947588054261714071953 17149460691040696285553965)
            ·
              refine ⟨6431047759140261107082737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17149460691040696285553965 6431047759140261107082737)
              ·
                refine ⟨4823285819355195830312053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6431047759140261107082737 4823285819355195830312053)
                ·
                  refine ⟨452183045564549609091755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4823285819355195830312053 452183045564549609091755)
                  ·
                    rfl

theorem cell22_3962805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 3, 2, 5].length) (baseStart_3962805 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3962805 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3962805 prefixEnd_3962805 := by exact prefixLift 3962805
  have htrace : WordTrace (prefixWord ++ tailWord_3962805) baseStart_3962805 baseEnd_3962805 := by
    simpa [prefixWord, tailWord_3962805, baseEnd_3962805] using wordTrace_append hprefix tailTrace_3962805
  have hstable : (prefixWord ++ tailWord_3962805).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3962805).length < 2 ^ (prefixWord ++ tailWord_3962805).sum := by decide
  have hdescent : baseEnd_3962805 < baseStart_3962805 := by decide
  rcases family_descends (prefixWord ++ tailWord_3962805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3962848 : List Nat := [2, 1, 1, 3, 1, 1, 1, 6, 1, 5]
def baseStart_3962848 : Nat := 118140960795 + 3962848 * 2 ^ 59
def prefixEnd_3962848 : Nat := 4983230072969 + 3 ^ 40 * 3962848 * 2
def baseEnd_3962848 : Nat := 1356563856472411048450133

theorem tailTrace_3962848 : CollatzResearch.WordTrace tailWord_3962848 prefixEnd_3962848 1356563856472411048450133 := by
  unfold tailWord_3962848
  simp only [CollatzResearch.WordTrace]
  refine ⟨72268470373642985700332599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96357960498190647600443465 72268470373642985700332599)
  ·
    refine ⟨108402705560464478550498899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72268470373642985700332599 108402705560464478550498899)
    ·
      refine ⟨162604058340696717825748349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108402705560464478550498899 162604058340696717825748349)
      ·
        refine ⟨60976521877761269184655631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 162604058340696717825748349 60976521877761269184655631)
        ·
          refine ⟨91464782816641903776983447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60976521877761269184655631 91464782816641903776983447)
          ·
            refine ⟨137197174224962855665475171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91464782816641903776983447 137197174224962855665475171)
            ·
              refine ⟨205795761337444283498212757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 137197174224962855665475171 205795761337444283498212757)
              ·
                refine ⟨9646676312692700788978723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 205795761337444283498212757 9646676312692700788978723)
                ·
                  refine ⟨14470014469039051183468085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9646676312692700788978723 14470014469039051183468085)
                  ·
                    refine ⟨1356563856472411048450133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14470014469039051183468085 1356563856472411048450133)
                    ·
                      rfl

theorem cell22_3962848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 6, 1, 5].length) (baseStart_3962848 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3962848 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3962848 prefixEnd_3962848 := by exact prefixLift 3962848
  have htrace : WordTrace (prefixWord ++ tailWord_3962848) baseStart_3962848 baseEnd_3962848 := by
    simpa [prefixWord, tailWord_3962848, baseEnd_3962848] using wordTrace_append hprefix tailTrace_3962848
  have hstable : (prefixWord ++ tailWord_3962848).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3962848).length < 2 ^ (prefixWord ++ tailWord_3962848).sum := by decide
  have hdescent : baseEnd_3962848 < baseStart_3962848 := by decide
  rcases family_descends (prefixWord ++ tailWord_3962848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3962940 : List Nat := [2, 2, 2, 2, 2, 1, 1, 5, 5]
def baseStart_3962940 : Nat := 118140960795 + 3962940 * 2 ^ 59
def prefixEnd_3962940 : Nat := 4983230072969 + 3 ^ 40 * 3962940 * 2
def baseEnd_3962940 : Nat := 452198449984184491716617

theorem tailTrace_3962940 : CollatzResearch.WordTrace tailWord_3962940 prefixEnd_3962940 452198449984184491716617 := by
  unfold tailWord_3962940
  simp only [CollatzResearch.WordTrace]
  refine ⟨72270148131476335556507137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96360197508635114075342849 72270148131476335556507137)
  ·
    refine ⟨54202611098607251667380353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72270148131476335556507137 54202611098607251667380353)
    ·
      refine ⟨40651958323955438750535265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54202611098607251667380353 40651958323955438750535265)
      ·
        refine ⟨30488968742966579062901449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40651958323955438750535265 30488968742966579062901449)
        ·
          refine ⟨22866726557224934297176087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30488968742966579062901449 22866726557224934297176087)
          ·
            refine ⟨34300089835837401445764131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22866726557224934297176087 34300089835837401445764131)
            ·
              refine ⟨51450134753756102168646197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34300089835837401445764131 51450134753756102168646197)
              ·
                refine ⟨4823450133164634578310581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 51450134753756102168646197 4823450133164634578310581)
                ·
                  refine ⟨452198449984184491716617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4823450133164634578310581 452198449984184491716617)
                  ·
                    rfl

theorem cell22_3962940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 5, 5].length) (baseStart_3962940 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3962940 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3962940 prefixEnd_3962940 := by exact prefixLift 3962940
  have htrace : WordTrace (prefixWord ++ tailWord_3962940) baseStart_3962940 baseEnd_3962940 := by
    simpa [prefixWord, tailWord_3962940, baseEnd_3962940] using wordTrace_append hprefix tailTrace_3962940
  have hstable : (prefixWord ++ tailWord_3962940).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3962940).length < 2 ^ (prefixWord ++ tailWord_3962940).sum := by decide
  have hdescent : baseEnd_3962940 < baseStart_3962940 := by decide
  rcases family_descends (prefixWord ++ tailWord_3962940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3962985 : List Nat := [1, 2, 1, 1, 1, 5, 4, 1, 6]
def baseStart_3962985 : Nat := 118140960795 + 3962985 * 2 ^ 59
def prefixEnd_3962985 : Nat := 4983230072969 + 3 ^ 40 * 3962985 * 2
def baseEnd_3962985 : Nat := 452203584790729452591571

theorem tailTrace_3962985 : CollatzResearch.WordTrace tailWord_3962985 prefixEnd_3962985 452203584790729452591571 := by
  unfold tailWord_3962985
  simp only [CollatzResearch.WordTrace]
  refine ⟨144541937547789643798402409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96361291698526429198934939 144541937547789643798402409)
  ·
    refine ⟨108406453160842232848801807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144541937547789643798402409 108406453160842232848801807)
    ·
      refine ⟨162609679741263349273202711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108406453160842232848801807 162609679741263349273202711)
      ·
        refine ⟨243914519611895023909804067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162609679741263349273202711 243914519611895023909804067)
        ·
          refine ⟨365871779417842535864706101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 243914519611895023909804067 365871779417842535864706101)
          ·
            refine ⟨34300479320422737737316197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 365871779417842535864706101 34300479320422737737316197)
            ·
              refine ⟨6431339872579263325746787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34300479320422737737316197 6431339872579263325746787)
              ·
                refine ⟨9647009808868894988620181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6431339872579263325746787 9647009808868894988620181)
                ·
                  refine ⟨452203584790729452591571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9647009808868894988620181 452203584790729452591571)
                  ·
                    rfl

theorem cell22_3962985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 4, 1, 6].length) (baseStart_3962985 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3962985 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3962985 prefixEnd_3962985 := by exact prefixLift 3962985
  have htrace : WordTrace (prefixWord ++ tailWord_3962985) baseStart_3962985 baseEnd_3962985 := by
    simpa [prefixWord, tailWord_3962985, baseEnd_3962985] using wordTrace_append hprefix tailTrace_3962985
  have hstable : (prefixWord ++ tailWord_3962985).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3962985).length < 2 ^ (prefixWord ++ tailWord_3962985).sum := by decide
  have hdescent : baseEnd_3962985 < baseStart_3962985 := by decide
  rcases family_descends (prefixWord ++ tailWord_3962985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3963015 : List Nat := [1, 1, 4, 2, 1, 1, 4, 1, 1, 6]
def baseStart_3963015 : Nat := 118140960795 + 3963015 * 2 ^ 59
def prefixEnd_3963015 : Nat := 4983230072969 + 3 ^ 40 * 3963015 * 2
def baseEnd_3963015 : Nat := 1356621023985278279524621

theorem tailTrace_3963015 : CollatzResearch.WordTrace tailWord_3963015 prefixEnd_3963015 1356621023985278279524621 := by
  unfold tailWord_3963015
  simp only [CollatzResearch.WordTrace]
  refine ⟨144543031737680958921994499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96362021158453972614662999 144543031737680958921994499)
  ·
    refine ⟨216814547606521438382991749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144543031737680958921994499 216814547606521438382991749)
    ·
      refine ⟨40652727676222769696810953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 216814547606521438382991749 40652727676222769696810953)
      ·
        refine ⟨30489545757167077272608215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40652727676222769696810953 30489545757167077272608215)
        ·
          refine ⟨45734318635750615908912323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30489545757167077272608215 45734318635750615908912323)
          ·
            refine ⟨68601477953625923863368485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45734318635750615908912323 68601477953625923863368485)
            ·
              refine ⟨12862777116304860724381591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 68601477953625923863368485 12862777116304860724381591)
              ·
                refine ⟨19294165674457291086572387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12862777116304860724381591 19294165674457291086572387)
                ·
                  refine ⟨28941248511685936629858581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19294165674457291086572387 28941248511685936629858581)
                  ·
                    refine ⟨1356621023985278279524621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28941248511685936629858581 1356621023985278279524621)
                    ·
                      rfl

theorem cell22_3963015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 4, 1, 1, 6].length) (baseStart_3963015 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3963015 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3963015 prefixEnd_3963015 := by exact prefixLift 3963015
  have htrace : WordTrace (prefixWord ++ tailWord_3963015) baseStart_3963015 baseEnd_3963015 := by
    simpa [prefixWord, tailWord_3963015, baseEnd_3963015] using wordTrace_append hprefix tailTrace_3963015
  have hstable : (prefixWord ++ tailWord_3963015).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3963015).length < 2 ^ (prefixWord ++ tailWord_3963015).sum := by decide
  have hdescent : baseEnd_3963015 < baseStart_3963015 := by decide
  rcases family_descends (prefixWord ++ tailWord_3963015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3963094 : List Nat := [5, 2, 1, 2, 1, 1, 1, 1, 2, 6]
def baseStart_3963094 : Nat := 118140960795 + 3963094 * 2 ^ 59
def prefixEnd_3963094 : Nat := 4983230072969 + 3 ^ 40 * 3963094 * 2
def baseEnd_3963094 : Nat := 1356648067299748406799379

theorem tailTrace_3963094 : CollatzResearch.WordTrace tailWord_3963094 prefixEnd_3963094 1356648067299748406799379 := by
  unfold tailWord_3963094
  simp only [CollatzResearch.WordTrace]
  refine ⟨9034119569024672213382521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 96363942069596503609413557 9034119569024672213382521)
  ·
    refine ⟨6775589676768504160036891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9034119569024672213382521 6775589676768504160036891)
    ·
      refine ⟨10163384515152756240055337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6775589676768504160036891 10163384515152756240055337)
      ·
        refine ⟨7622538386364567180041503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10163384515152756240055337 7622538386364567180041503)
        ·
          refine ⟨11433807579546850770062255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7622538386364567180041503 11433807579546850770062255)
          ·
            refine ⟨17150711369320276155093383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11433807579546850770062255 17150711369320276155093383)
            ·
              refine ⟨25726067053980414232640075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17150711369320276155093383 25726067053980414232640075)
              ·
                refine ⟨38589100580970621348960113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25726067053980414232640075 38589100580970621348960113)
                ·
                  refine ⟨28941825435727966011720085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38589100580970621348960113 28941825435727966011720085)
                  ·
                    refine ⟨1356648067299748406799379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28941825435727966011720085 1356648067299748406799379)
                    ·
                      rfl

theorem cell22_3963094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 1, 1, 2, 6].length) (baseStart_3963094 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3963094 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3963094 prefixEnd_3963094 := by exact prefixLift 3963094
  have htrace : WordTrace (prefixWord ++ tailWord_3963094) baseStart_3963094 baseEnd_3963094 := by
    simpa [prefixWord, tailWord_3963094, baseEnd_3963094] using wordTrace_append hprefix tailTrace_3963094
  have hstable : (prefixWord ++ tailWord_3963094).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3963094).length < 2 ^ (prefixWord ++ tailWord_3963094).sum := by decide
  have hdescent : baseEnd_3963094 < baseStart_3963094 := by decide
  rcases family_descends (prefixWord ++ tailWord_3963094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3963096 : List Nat := [2, 1, 2, 2, 4, 2, 1, 4, 1, 3]
def baseStart_3963096 : Nat := 118140960795 + 3963096 * 2 ^ 59
def prefixEnd_3963096 : Nat := 4983230072969 + 3 ^ 40 * 3963096 * 2
def baseEnd_3963096 : Nat := 1356648751940621068249373

theorem tailTrace_3963096 : CollatzResearch.WordTrace tailWord_3963096 prefixEnd_3963096 1356648751940621068249373 := by
  unfold tailWord_3963096
  simp only [CollatzResearch.WordTrace]
  refine ⟨72272993025193754877846571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96363990700258339837128761 72272993025193754877846571)
  ·
    refine ⟨108409489537790632316769857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72272993025193754877846571 108409489537790632316769857)
    ·
      refine ⟨81307117153342974237577393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108409489537790632316769857 81307117153342974237577393)
      ·
        refine ⟨60980337865007230678183045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81307117153342974237577393 60980337865007230678183045)
        ·
          refine ⟨11433813349688855752159321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 60980337865007230678183045 11433813349688855752159321)
          ·
            refine ⟨8575360012266641814119491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11433813349688855752159321 8575360012266641814119491)
            ·
              refine ⟨12863040018399962721179237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8575360012266641814119491 12863040018399962721179237)
              ·
                refine ⟨2411820003449993010221107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12863040018399962721179237 2411820003449993010221107)
                ·
                  refine ⟨3617730005174989515331661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2411820003449993010221107 3617730005174989515331661)
                  ·
                    refine ⟨1356648751940621068249373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3617730005174989515331661 1356648751940621068249373)
                    ·
                      rfl

theorem cell22_3963096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 1, 4, 1, 3].length) (baseStart_3963096 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3963096 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3963096 prefixEnd_3963096 := by exact prefixLift 3963096
  have htrace : WordTrace (prefixWord ++ tailWord_3963096) baseStart_3963096 baseEnd_3963096 := by
    simpa [prefixWord, tailWord_3963096, baseEnd_3963096] using wordTrace_append hprefix tailTrace_3963096
  have hstable : (prefixWord ++ tailWord_3963096).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3963096).length < 2 ^ (prefixWord ++ tailWord_3963096).sum := by decide
  have hdescent : baseEnd_3963096 < baseStart_3963096 := by decide
  rcases family_descends (prefixWord ++ tailWord_3963096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3963143 : List Nat := [1, 1, 4, 5, 2, 1, 1, 2, 5]
def baseStart_3963143 : Nat := 118140960795 + 3963143 * 2 ^ 59
def prefixEnd_3963143 : Nat := 4983230072969 + 3 ^ 40 * 3963143 * 2
def baseEnd_3963143 : Nat := 452221613667042870774743

theorem tailTrace_3963143 : CollatzResearch.WordTrace tailWord_3963143 prefixEnd_3963143 452221613667042870774743 := by
  unfold tailWord_3963143
  simp only [CollatzResearch.WordTrace]
  refine ⟨144547700281217236782654083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96365133520811491188436055 144547700281217236782654083)
  ·
    refine ⟨216821550421825855173981125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144547700281217236782654083 216821550421825855173981125)
    ·
      refine ⟨40654040704092347845121461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 216821550421825855173981125 40654040704092347845121461)
      ·
        refine ⟨3811316316008657610480137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 40654040704092347845121461 3811316316008657610480137)
        ·
          refine ⟨2858487237006493207860103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3811316316008657610480137 2858487237006493207860103)
          ·
            refine ⟨4287730855509739811790155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2858487237006493207860103 4287730855509739811790155)
            ·
              refine ⟨6431596283264609717685233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4287730855509739811790155 6431596283264609717685233)
              ·
                refine ⟨4823697212448457288263925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6431596283264609717685233 4823697212448457288263925)
                ·
                  refine ⟨452221613667042870774743, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4823697212448457288263925 452221613667042870774743)
                  ·
                    rfl

theorem cell22_3963143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 2, 1, 1, 2, 5].length) (baseStart_3963143 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3963143 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3963143 prefixEnd_3963143 := by exact prefixLift 3963143
  have htrace : WordTrace (prefixWord ++ tailWord_3963143) baseStart_3963143 baseEnd_3963143 := by
    simpa [prefixWord, tailWord_3963143, baseEnd_3963143] using wordTrace_append hprefix tailTrace_3963143
  have hstable : (prefixWord ++ tailWord_3963143).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3963143).length < 2 ^ (prefixWord ++ tailWord_3963143).sum := by decide
  have hdescent : baseEnd_3963143 < baseStart_3963143 := by decide
  rcases family_descends (prefixWord ++ tailWord_3963143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3963167 : List Nat := [1, 1, 2, 4, 3, 1, 1, 2, 1, 6]
def baseStart_3963167 : Nat := 118140960795 + 3963167 * 2 ^ 59
def prefixEnd_3963167 : Nat := 4983230072969 + 3 ^ 40 * 3963167 * 2
def baseEnd_3963167 : Nat := 1356673056691600549724155

theorem tailTrace_3963167 : CollatzResearch.WordTrace tailWord_3963167 prefixEnd_3963167 1356673056691600549724155 := by
  unfold tailWord_3963167
  simp only [CollatzResearch.WordTrace]
  refine ⟨144548575633130288881527755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96365717088753525921018503 144548575633130288881527755)
  ·
    refine ⟨216822863449695433322291633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144548575633130288881527755 216822863449695433322291633)
    ·
      refine ⟨162617147587271574991718725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 216822863449695433322291633 162617147587271574991718725)
      ·
        refine ⟨30490715172613420310947261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 162617147587271574991718725 30490715172613420310947261)
        ·
          refine ⟨11434018189730032616605223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30490715172613420310947261 11434018189730032616605223)
          ·
            refine ⟨17151027284595048924907835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11434018189730032616605223 17151027284595048924907835)
            ·
              refine ⟨25726540926892573387361753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17151027284595048924907835 25726540926892573387361753)
              ·
                refine ⟨19294905695169430040521315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25726540926892573387361753 19294905695169430040521315)
                ·
                  refine ⟨28942358542754145060781973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19294905695169430040521315 28942358542754145060781973)
                  ·
                    refine ⟨1356673056691600549724155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28942358542754145060781973 1356673056691600549724155)
                    ·
                      rfl

theorem cell22_3963167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 1, 2, 1, 6].length) (baseStart_3963167 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3963167 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3963167 prefixEnd_3963167 := by exact prefixLift 3963167
  have htrace : WordTrace (prefixWord ++ tailWord_3963167) baseStart_3963167 baseEnd_3963167 := by
    simpa [prefixWord, tailWord_3963167, baseEnd_3963167] using wordTrace_append hprefix tailTrace_3963167
  have hstable : (prefixWord ++ tailWord_3963167).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3963167).length < 2 ^ (prefixWord ++ tailWord_3963167).sum := by decide
  have hdescent : baseEnd_3963167 < baseStart_3963167 := by decide
  rcases family_descends (prefixWord ++ tailWord_3963167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3963169 : List Nat := [1, 2, 3, 2, 1, 1, 2, 5, 2, 3]
def baseStart_3963169 : Nat := 118140960795 + 3963169 * 2 ^ 59
def prefixEnd_3963169 : Nat := 4983230072969 + 3 ^ 40 * 3963169 * 2
def baseEnd_3963169 : Nat := 1356673741332473211174149

theorem tailTrace_3963169 : CollatzResearch.WordTrace tailWord_3963169 prefixEnd_3963169 1356673741332473211174149 := by
  unfold tailWord_3963169
  simp only [CollatzResearch.WordTrace]
  refine ⟨144548648579123043223100561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96365765719415362148733707 144548648579123043223100561)
  ·
    refine ⟨108411486434342282417325421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144548648579123043223100561 108411486434342282417325421)
    ·
      refine ⟨40654307412878355906497033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 108411486434342282417325421 40654307412878355906497033)
      ·
        refine ⟨30490730559658766929872775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40654307412878355906497033 30490730559658766929872775)
        ·
          refine ⟨45736095839488150394809163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30490730559658766929872775 45736095839488150394809163)
          ·
            refine ⟨68604143759232225592213745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45736095839488150394809163 68604143759232225592213745)
            ·
              refine ⟨51453107819424169194160309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68604143759232225592213745 51453107819424169194160309)
              ·
                refine ⟨4823728858071015861952529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 51453107819424169194160309 4823728858071015861952529)
                ·
                  refine ⟨3617796643553261896464397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4823728858071015861952529 3617796643553261896464397)
                  ·
                    refine ⟨1356673741332473211174149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3617796643553261896464397 1356673741332473211174149)
                    ·
                      rfl

theorem cell22_3963169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 5, 2, 3].length) (baseStart_3963169 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3963169 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3963169 prefixEnd_3963169 := by exact prefixLift 3963169
  have htrace : WordTrace (prefixWord ++ tailWord_3963169) baseStart_3963169 baseEnd_3963169 := by
    simpa [prefixWord, tailWord_3963169, baseEnd_3963169] using wordTrace_append hprefix tailTrace_3963169
  have hstable : (prefixWord ++ tailWord_3963169).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3963169).length < 2 ^ (prefixWord ++ tailWord_3963169).sum := by decide
  have hdescent : baseEnd_3963169 < baseStart_3963169 := by decide
  rcases family_descends (prefixWord ++ tailWord_3963169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3963188 : List Nat := [2, 5, 1, 1, 1, 4, 1, 3, 4]
def baseStart_3963188 : Nat := 118140960795 + 3963188 * 2 ^ 59
def prefixEnd_3963188 : Nat := 4983230072969 + 3 ^ 40 * 3963188 * 2
def baseEnd_3963188 : Nat := 452226748473587831649697

theorem tailTrace_3963188 : CollatzResearch.WordTrace tailWord_3963188 prefixEnd_3963188 452226748473587831649697 := by
  unfold tailWord_3963188
  simp only [CollatzResearch.WordTrace]
  refine ⟨72274670783027104734021109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96366227710702806312028145 72274670783027104734021109)
  ·
    refine ⟨6775750385908791068814479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 72274670783027104734021109 6775750385908791068814479)
    ·
      refine ⟨10163625578863186603221719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6775750385908791068814479 10163625578863186603221719)
      ·
        refine ⟨15245438368294779904832579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10163625578863186603221719 15245438368294779904832579)
        ·
          refine ⟨22868157552442169857248869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15245438368294779904832579 22868157552442169857248869)
          ·
            refine ⟨4287779541082906848234163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22868157552442169857248869 4287779541082906848234163)
            ·
              refine ⟨6431669311624360272351245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4287779541082906848234163 6431669311624360272351245)
              ·
                refine ⟨2411875991859135102131717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6431669311624360272351245 2411875991859135102131717)
                ·
                  refine ⟨452226748473587831649697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2411875991859135102131717 452226748473587831649697)
                  ·
                    rfl

theorem cell22_3963188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 4, 1, 3, 4].length) (baseStart_3963188 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3963188 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3963188 prefixEnd_3963188 := by exact prefixLift 3963188
  have htrace : WordTrace (prefixWord ++ tailWord_3963188) baseStart_3963188 baseEnd_3963188 := by
    simpa [prefixWord, tailWord_3963188, baseEnd_3963188] using wordTrace_append hprefix tailTrace_3963188
  have hstable : (prefixWord ++ tailWord_3963188).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3963188).length < 2 ^ (prefixWord ++ tailWord_3963188).sum := by decide
  have hdescent : baseEnd_3963188 < baseStart_3963188 := by decide
  rcases family_descends (prefixWord ++ tailWord_3963188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3963201 : List Nat := [1, 2, 5, 2, 2, 1, 1, 2, 2, 4]
def baseStart_3963201 : Nat := 118140960795 + 3963201 * 2 ^ 59
def prefixEnd_3963201 : Nat := 4983230072969 + 3 ^ 40 * 3963201 * 2
def baseEnd_3963201 : Nat := 1356684695586435794374051

theorem tailTrace_3963201 : CollatzResearch.WordTrace tailWord_3963201 prefixEnd_3963201 1356684695586435794374051 := by
  unfold tailWord_3963201
  simp only [CollatzResearch.WordTrace]
  refine ⟨144549815715007112688265457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96366543810004741792176971 144549815715007112688265457)
  ·
    refine ⟨108412361786255334516199093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144549815715007112688265457 108412361786255334516199093)
    ·
      refine ⟨10163658917461437610893665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 108412361786255334516199093 10163658917461437610893665)
      ·
        refine ⟨7622744188096078208170249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10163658917461437610893665 7622744188096078208170249)
        ·
          refine ⟨5717058141072058656127687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7622744188096078208170249 5717058141072058656127687)
          ·
            refine ⟨8575587211608087984191531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5717058141072058656127687 8575587211608087984191531)
            ·
              refine ⟨12863380817412131976287297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8575587211608087984191531 12863380817412131976287297)
              ·
                refine ⟨9647535613059098982215473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12863380817412131976287297 9647535613059098982215473)
                ·
                  refine ⟨7235651709794324236661605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9647535613059098982215473 7235651709794324236661605)
                  ·
                    refine ⟨1356684695586435794374051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7235651709794324236661605 1356684695586435794374051)
                    ·
                      rfl

theorem cell22_3963201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 1, 2, 2, 4].length) (baseStart_3963201 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3963201 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3963201 prefixEnd_3963201 := by exact prefixLift 3963201
  have htrace : WordTrace (prefixWord ++ tailWord_3963201) baseStart_3963201 baseEnd_3963201 := by
    simpa [prefixWord, tailWord_3963201, baseEnd_3963201] using wordTrace_append hprefix tailTrace_3963201
  have hstable : (prefixWord ++ tailWord_3963201).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3963201).length < 2 ^ (prefixWord ++ tailWord_3963201).sum := by decide
  have hdescent : baseEnd_3963201 < baseStart_3963201 := by decide
  rcases family_descends (prefixWord ++ tailWord_3963201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3963212 : List Nat := [2, 2, 1, 3, 2, 1, 2, 1, 2, 6]
def baseStart_3963212 : Nat := 118140960795 + 3963212 * 2 ^ 59
def prefixEnd_3963212 : Nat := 4983230072969 + 3 ^ 40 * 3963212 * 2
def baseEnd_3963212 : Nat := 1356688461111235432349017

theorem tailTrace_3963212 : CollatzResearch.WordTrace tailWord_3963212 prefixEnd_3963212 1356688461111235432349017 := by
  unfold tailWord_3963212
  simp only [CollatzResearch.WordTrace]
  refine ⟨72275108458983630783457945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96366811278644841044610593 72275108458983630783457945)
  ·
    refine ⟨54206331344237723087593459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72275108458983630783457945 54206331344237723087593459)
    ·
      refine ⟨81309497016356584631390189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54206331344237723087593459 81309497016356584631390189)
      ·
        refine ⟨30491061381133719236771321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81309497016356584631390189 30491061381133719236771321)
        ·
          refine ⟨22868296035850289427578491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30491061381133719236771321 22868296035850289427578491)
          ·
            refine ⟨34302444053775434141367737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22868296035850289427578491 34302444053775434141367737)
            ·
              refine ⟨25726833040331575606025803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34302444053775434141367737 25726833040331575606025803)
              ·
                refine ⟨38590249560497363409038705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25726833040331575606025803 38590249560497363409038705)
                ·
                  refine ⟨28942687170373022556779029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38590249560497363409038705 28942687170373022556779029)
                  ·
                    refine ⟨1356688461111235432349017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28942687170373022556779029 1356688461111235432349017)
                    ·
                      rfl

theorem cell22_3963212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 2, 1, 2, 6].length) (baseStart_3963212 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3963212 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3963212 prefixEnd_3963212 := by exact prefixLift 3963212
  have htrace : WordTrace (prefixWord ++ tailWord_3963212) baseStart_3963212 baseEnd_3963212 := by
    simpa [prefixWord, tailWord_3963212, baseEnd_3963212] using wordTrace_append hprefix tailTrace_3963212
  have hstable : (prefixWord ++ tailWord_3963212).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3963212).length < 2 ^ (prefixWord ++ tailWord_3963212).sum := by decide
  have hdescent : baseEnd_3963212 < baseStart_3963212 := by decide
  rcases family_descends (prefixWord ++ tailWord_3963212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3963214 : List Nat := [4, 1, 1, 1, 1, 1, 2, 5, 3, 3]
def baseStart_3963214 : Nat := 118140960795 + 3963214 * 2 ^ 59
def prefixEnd_3963214 : Nat := 4983230072969 + 3 ^ 40 * 3963214 * 2
def baseEnd_3963214 : Nat := 1356689145752108093799011

theorem tailTrace_3963214 : CollatzResearch.WordTrace tailWord_3963214 prefixEnd_3963214 1356689145752108093799011 := by
  unfold tailWord_3963214
  simp only [CollatzResearch.WordTrace]
  refine ⟨18068786232995001988561087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 96366859909306677272325797 18068786232995001988561087)
  ·
    refine ⟨27103179349492502982841631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18068786232995001988561087 27103179349492502982841631)
    ·
      refine ⟨40654769024238754474262447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27103179349492502982841631 40654769024238754474262447)
      ·
        refine ⟨60982153536358131711393671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40654769024238754474262447 60982153536358131711393671)
        ·
          refine ⟨91473230304537197567090507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60982153536358131711393671 91473230304537197567090507)
          ·
            refine ⟨137209845456805796350635761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91473230304537197567090507 137209845456805796350635761)
            ·
              refine ⟨102907384092604347262976821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 137209845456805796350635761 102907384092604347262976821)
              ·
                refine ⟨9647567258681657555904077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 102907384092604347262976821 9647567258681657555904077)
                ·
                  refine ⟨3617837722005621583464029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9647567258681657555904077 3617837722005621583464029)
                  ·
                    refine ⟨1356689145752108093799011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3617837722005621583464029 1356689145752108093799011)
                    ·
                      rfl

theorem cell22_3963214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 5, 3, 3].length) (baseStart_3963214 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3963214 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3963214 prefixEnd_3963214 := by exact prefixLift 3963214
  have htrace : WordTrace (prefixWord ++ tailWord_3963214) baseStart_3963214 baseEnd_3963214 := by
    simpa [prefixWord, tailWord_3963214, baseEnd_3963214] using wordTrace_append hprefix tailTrace_3963214
  have hstable : (prefixWord ++ tailWord_3963214).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3963214).length < 2 ^ (prefixWord ++ tailWord_3963214).sum := by decide
  have hdescent : baseEnd_3963214 < baseStart_3963214 := by decide
  rcases family_descends (prefixWord ++ tailWord_3963214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3963265 : List Nat := [1, 2, 4, 3, 1, 1, 4, 2, 1, 3]
def baseStart_3963265 : Nat := 118140960795 + 3963265 * 2 ^ 59
def prefixEnd_3963265 : Nat := 4983230072969 + 3 ^ 40 * 3963265 * 2
def baseEnd_3963265 : Nat := 1356706604094360960773855

theorem tailTrace_3963265 : CollatzResearch.WordTrace tailWord_3963265 prefixEnd_3963265 1356706604094360960773855 := by
  unfold tailWord_3963265
  simp only [CollatzResearch.WordTrace]
  refine ⟨144552149986775251618595249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96368099991183501079063499 144552149986775251618595249)
  ·
    refine ⟨108414112490081438713946437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144552149986775251618595249 108414112490081438713946437)
    ·
      refine ⟨20327646091890269758864957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 108414112490081438713946437 20327646091890269758864957)
      ·
        refine ⟨7622867284458851159574359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20327646091890269758864957 7622867284458851159574359)
        ·
          refine ⟨11434300926688276739361539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7622867284458851159574359 11434300926688276739361539)
          ·
            refine ⟨17151451390032415109042309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11434300926688276739361539 17151451390032415109042309)
            ·
              refine ⟨3215897135631077832945433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17151451390032415109042309 3215897135631077832945433)
              ·
                refine ⟨2411922851723308374709075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3215897135631077832945433 2411922851723308374709075)
                ·
                  refine ⟨3617884277584962562063613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2411922851723308374709075 3617884277584962562063613)
                  ·
                    refine ⟨1356706604094360960773855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3617884277584962562063613 1356706604094360960773855)
                    ·
                      rfl

theorem cell22_3963265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 4, 2, 1, 3].length) (baseStart_3963265 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3963265 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3963265 prefixEnd_3963265 := by exact prefixLift 3963265
  have htrace : WordTrace (prefixWord ++ tailWord_3963265) baseStart_3963265 baseEnd_3963265 := by
    simpa [prefixWord, tailWord_3963265, baseEnd_3963265] using wordTrace_append hprefix tailTrace_3963265
  have hstable : (prefixWord ++ tailWord_3963265).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3963265).length < 2 ^ (prefixWord ++ tailWord_3963265).sum := by decide
  have hdescent : baseEnd_3963265 < baseStart_3963265 := by decide
  rcases family_descends (prefixWord ++ tailWord_3963265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3963321 : List Nat := [1, 2, 1, 4, 3, 2, 1, 1, 4, 3]
def baseStart_3963321 : Nat := 118140960795 + 3963321 * 2 ^ 59
def prefixEnd_3963321 : Nat := 4983230072969 + 3 ^ 40 * 3963321 * 2
def baseEnd_3963321 : Nat := 1356725774038795481373683

theorem tailTrace_3963321 : CollatzResearch.WordTrace tailWord_3963321 prefixEnd_3963321 1356725774038795481373683 := by
  unfold tailWord_3963321
  simp only [CollatzResearch.WordTrace]
  refine ⟨144554192474572373182633817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96369461649714915455089211 144554192474572373182633817)
  ·
    refine ⟨108415644355929279886975363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144554192474572373182633817 108415644355929279886975363)
    ·
      refine ⟨162623466533893919830463045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108415644355929279886975363 162623466533893919830463045)
      ·
        refine ⟨30491899975105109968211821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 162623466533893919830463045 30491899975105109968211821)
        ·
          refine ⟨11434462490664416238079433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30491899975105109968211821 11434462490664416238079433)
          ·
            refine ⟨8575846867998312178559575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11434462490664416238079433 8575846867998312178559575)
            ·
              refine ⟨12863770301997468267839363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8575846867998312178559575 12863770301997468267839363)
              ·
                refine ⟨19295655452996202401759045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12863770301997468267839363 19295655452996202401759045)
                ·
                  refine ⟨3617935397436787950329821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19295655452996202401759045 3617935397436787950329821)
                  ·
                    refine ⟨1356725774038795481373683, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3617935397436787950329821 1356725774038795481373683)
                    ·
                      rfl

theorem cell22_3963321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 1, 1, 4, 3].length) (baseStart_3963321 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3963321 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3963321 prefixEnd_3963321 := by exact prefixLift 3963321
  have htrace : WordTrace (prefixWord ++ tailWord_3963321) baseStart_3963321 baseEnd_3963321 := by
    simpa [prefixWord, tailWord_3963321, baseEnd_3963321] using wordTrace_append hprefix tailTrace_3963321
  have hstable : (prefixWord ++ tailWord_3963321).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3963321).length < 2 ^ (prefixWord ++ tailWord_3963321).sum := by decide
  have hdescent : baseEnd_3963321 < baseStart_3963321 := by decide
  rcases family_descends (prefixWord ++ tailWord_3963321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3963338 : List Nat := [3, 1, 2, 1, 2, 2, 5, 1, 2, 3]
def baseStart_3963338 : Nat := 118140960795 + 3963338 * 2 ^ 59
def prefixEnd_3963338 : Nat := 4983230072969 + 3 ^ 40 * 3963338 * 2
def baseEnd_3963338 : Nat := 1356731593486213103698631

theorem tailTrace_3963338 : CollatzResearch.WordTrace tailWord_3963338 prefixEnd_3963338 1356731593486213103698631 := by
  unfold tailWord_3963338
  simp only [CollatzResearch.WordTrace]
  refine ⟨36138703128877696271500667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96369875010340523390668445 36138703128877696271500667)
  ·
    refine ⟨54208054693316544407251001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36138703128877696271500667 54208054693316544407251001)
    ·
      refine ⟨40656041019987408305438251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54208054693316544407251001 40656041019987408305438251)
      ·
        refine ⟨60984061529981112458157377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40656041019987408305438251 60984061529981112458157377)
        ·
          refine ⟨45738046147485834343618033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60984061529981112458157377 45738046147485834343618033)
          ·
            refine ⟨34303534610614375757713525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45738046147485834343618033 34303534610614375757713525)
            ·
              refine ⟨3215956369745097727285643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 34303534610614375757713525 3215956369745097727285643)
              ·
                refine ⟨4823934554617646590928465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3215956369745097727285643 4823934554617646590928465)
                ·
                  refine ⟨3617950915963234943196349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4823934554617646590928465 3617950915963234943196349)
                  ·
                    refine ⟨1356731593486213103698631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3617950915963234943196349 1356731593486213103698631)
                    ·
                      rfl

theorem cell22_3963338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 5, 1, 2, 3].length) (baseStart_3963338 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3963338 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3963338 prefixEnd_3963338 := by exact prefixLift 3963338
  have htrace : WordTrace (prefixWord ++ tailWord_3963338) baseStart_3963338 baseEnd_3963338 := by
    simpa [prefixWord, tailWord_3963338, baseEnd_3963338] using wordTrace_append hprefix tailTrace_3963338
  have hstable : (prefixWord ++ tailWord_3963338).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3963338).length < 2 ^ (prefixWord ++ tailWord_3963338).sum := by decide
  have hdescent : baseEnd_3963338 < baseStart_3963338 := by decide
  rcases family_descends (prefixWord ++ tailWord_3963338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3963347 : List Nat := [1, 1, 1, 2, 1, 1, 1, 1, 5, 8]
def baseStart_3963347 : Nat := 118140960795 + 3963347 * 2 ^ 59
def prefixEnd_3963347 : Nat := 4983230072969 + 3 ^ 40 * 3963347 * 2
def baseEnd_3963347 : Nat := 1356734674370140080223603

theorem tailTrace_3963347 : CollatzResearch.WordTrace tailWord_3963347 prefixEnd_3963347 1356734674370140080223603 := by
  unfold tailWord_3963347
  simp only [CollatzResearch.WordTrace]
  refine ⟨144555140772478179623080295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96370093848318786415386863 144555140772478179623080295)
  ·
    refine ⟨216832711158717269434620443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144555140772478179623080295 216832711158717269434620443)
    ·
      refine ⟨325249066738075904151930665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216832711158717269434620443 325249066738075904151930665)
      ·
        refine ⟨243936800053556928113947999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 325249066738075904151930665 243936800053556928113947999)
        ·
          refine ⟨365905200080335392170921999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 243936800053556928113947999 365905200080335392170921999)
          ·
            refine ⟨548857800120503088256382999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 365905200080335392170921999 548857800120503088256382999)
            ·
              refine ⟨823286700180754632384574499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 548857800120503088256382999 823286700180754632384574499)
              ·
                refine ⟨1234930050271131948576861749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 823286700180754632384574499 1234930050271131948576861749)
                ·
                  refine ⟨115774692212918620179080789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1234930050271131948576861749 115774692212918620179080789)
                  ·
                    refine ⟨1356734674370140080223603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 115774692212918620179080789 1356734674370140080223603)
                    ·
                      rfl

theorem cell22_3963347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 5, 8].length) (baseStart_3963347 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3963347 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3963347 prefixEnd_3963347 := by exact prefixLift 3963347
  have htrace : WordTrace (prefixWord ++ tailWord_3963347) baseStart_3963347 baseEnd_3963347 := by
    simpa [prefixWord, tailWord_3963347, baseEnd_3963347] using wordTrace_append hprefix tailTrace_3963347
  have hstable : (prefixWord ++ tailWord_3963347).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3963347).length < 2 ^ (prefixWord ++ tailWord_3963347).sum := by decide
  have hdescent : baseEnd_3963347 < baseStart_3963347 := by decide
  rcases family_descends (prefixWord ++ tailWord_3963347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3963379 : List Nat := [1, 1, 1, 2, 2, 2, 4, 4, 5]
def baseStart_3963379 : Nat := 118140960795 + 3963379 * 2 ^ 59
def prefixEnd_3963379 : Nat := 4983230072969 + 3 ^ 40 * 3963379 * 2
def baseEnd_3963379 : Nat := 452248542874700887807835

theorem tailTrace_3963379 : CollatzResearch.WordTrace tailWord_3963379 prefixEnd_3963379 452248542874700887807835 := by
  unfold tailWord_3963379
  simp only [CollatzResearch.WordTrace]
  refine ⟨144556307908362249088245191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96370871938908166058830127 144556307908362249088245191)
  ·
    refine ⟨216834461862543373632367787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144556307908362249088245191 216834461862543373632367787)
    ·
      refine ⟨325251692793815060448551681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216834461862543373632367787 325251692793815060448551681)
      ·
        refine ⟨243938769595361295336413761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 325251692793815060448551681 243938769595361295336413761)
        ·
          refine ⟨182954077196520971502310321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 243938769595361295336413761 182954077196520971502310321)
          ·
            refine ⟨137215557897390728626732741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 182954077196520971502310321 137215557897390728626732741)
            ·
              refine ⟨25727917105760761617512389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 137215557897390728626732741 25727917105760761617512389)
              ·
                refine ⟨4823984457330142803283573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25727917105760761617512389 4823984457330142803283573)
                ·
                  refine ⟨452248542874700887807835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4823984457330142803283573 452248542874700887807835)
                  ·
                    rfl

theorem cell22_3963379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 4, 4, 5].length) (baseStart_3963379 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3963379 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3963379 prefixEnd_3963379 := by exact prefixLift 3963379
  have htrace : WordTrace (prefixWord ++ tailWord_3963379) baseStart_3963379 baseEnd_3963379 := by
    simpa [prefixWord, tailWord_3963379, baseEnd_3963379] using wordTrace_append hprefix tailTrace_3963379
  have hstable : (prefixWord ++ tailWord_3963379).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3963379).length < 2 ^ (prefixWord ++ tailWord_3963379).sum := by decide
  have hdescent : baseEnd_3963379 < baseStart_3963379 := by decide
  rcases family_descends (prefixWord ++ tailWord_3963379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3963471 : List Nat := [1, 1, 2, 1, 1, 2, 7, 1, 2, 4]
def baseStart_3963471 : Nat := 118140960795 + 3963471 * 2 ^ 59
def prefixEnd_3963471 : Nat := 4983230072969 + 3 ^ 40 * 3963471 * 2
def baseEnd_3963471 : Nat := 1356777122104245090123223

theorem tailTrace_3963471 : CollatzResearch.WordTrace tailWord_3963471 prefixEnd_3963471 1356777122104245090123223 := by
  unfold tailWord_3963471
  simp only [CollatzResearch.WordTrace]
  refine ⟨144559663424028948800594267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96373108949352632533729511 144559663424028948800594267)
  ·
    refine ⟨216839495136043423200891401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144559663424028948800594267 216839495136043423200891401)
    ·
      refine ⟨162629621352032567400668551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 216839495136043423200891401 162629621352032567400668551)
      ·
        refine ⟨243944432028048851101002827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162629621352032567400668551 243944432028048851101002827)
        ·
          refine ⟨365916648042073276651504241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 243944432028048851101002827 365916648042073276651504241)
          ·
            refine ⟨274437486031554957488628181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 365916648042073276651504241 274437486031554957488628181)
            ·
              refine ⟨6432128578864569316139723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 274437486031554957488628181 6432128578864569316139723)
              ·
                refine ⟨9648192868296853974209585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6432128578864569316139723 9648192868296853974209585)
                ·
                  refine ⟨7236144651222640480657189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9648192868296853974209585 7236144651222640480657189)
                  ·
                    refine ⟨1356777122104245090123223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7236144651222640480657189 1356777122104245090123223)
                    ·
                      rfl

theorem cell22_3963471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 7, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 7, 1, 2, 4].length) (baseStart_3963471 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3963471 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3963471 prefixEnd_3963471 := by exact prefixLift 3963471
  have htrace : WordTrace (prefixWord ++ tailWord_3963471) baseStart_3963471 baseEnd_3963471 := by
    simpa [prefixWord, tailWord_3963471, baseEnd_3963471] using wordTrace_append hprefix tailTrace_3963471
  have hstable : (prefixWord ++ tailWord_3963471).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3963471).length < 2 ^ (prefixWord ++ tailWord_3963471).sum := by decide
  have hdescent : baseEnd_3963471 < baseStart_3963471 := by decide
  rcases family_descends (prefixWord ++ tailWord_3963471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3963499 : List Nat := [1, 1, 1, 1, 2, 2, 1, 5, 2, 6]
def baseStart_3963499 : Nat := 118140960795 + 3963499 * 2 ^ 59
def prefixEnd_3963499 : Nat := 4983230072969 + 3 ^ 40 * 3963499 * 2
def baseEnd_3963499 : Nat := 1356786707076462350423137

theorem tailTrace_3963499 : CollatzResearch.WordTrace tailWord_3963499 prefixEnd_3963499 1356786707076462350423137 := by
  unfold tailWord_3963499
  simp only [CollatzResearch.WordTrace]
  refine ⟨144560684667927509582613551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96373789778618339721742367 144560684667927509582613551)
  ·
    refine ⟨216841027001891264373920327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144560684667927509582613551 216841027001891264373920327)
    ·
      refine ⟨325261540502836896560880491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216841027001891264373920327 325261540502836896560880491)
      ·
        refine ⟨487892310754255344841320737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 325261540502836896560880491 487892310754255344841320737)
        ·
          refine ⟨365919233065691508630990553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 487892310754255344841320737 365919233065691508630990553)
          ·
            refine ⟨274439424799268631473242915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 365919233065691508630990553 274439424799268631473242915)
            ·
              refine ⟨411659137198902947209864373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 274439424799268631473242915 411659137198902947209864373)
              ·
                refine ⟨38593044112397151300924785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 411659137198902947209864373 38593044112397151300924785)
                ·
                  refine ⟨28944783084297863475693589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38593044112397151300924785 28944783084297863475693589)
                  ·
                    refine ⟨1356786707076462350423137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28944783084297863475693589 1356786707076462350423137)
                    ·
                      rfl

theorem cell22_3963499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 5, 2, 6].length) (baseStart_3963499 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3963499 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3963499 prefixEnd_3963499 := by exact prefixLift 3963499
  have htrace : WordTrace (prefixWord ++ tailWord_3963499) baseStart_3963499 baseEnd_3963499 := by
    simpa [prefixWord, tailWord_3963499, baseEnd_3963499] using wordTrace_append hprefix tailTrace_3963499
  have hstable : (prefixWord ++ tailWord_3963499).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3963499).length < 2 ^ (prefixWord ++ tailWord_3963499).sum := by decide
  have hdescent : baseEnd_3963499 < baseStart_3963499 := by decide
  rcases family_descends (prefixWord ++ tailWord_3963499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3963552 : List Nat := [2, 1, 1, 4, 5, 1, 1, 1, 3, 3]
def baseStart_3963552 : Nat := 118140960795 + 3963552 * 2 ^ 59
def prefixEnd_3963552 : Nat := 4983230072969 + 3 ^ 40 * 3963552 * 2
def baseEnd_3963552 : Nat := 1356804850059587878847975

theorem tailTrace_3963552 : CollatzResearch.WordTrace tailWord_3963552 prefixEnd_3963552 1356804850059587878847975 := by
  unfold tailWord_3963552
  simp only [CollatzResearch.WordTrace]
  refine ⟨72281308868367749817146455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96375078491156999756195273 72281308868367749817146455)
  ·
    refine ⟨108421963302551624725719683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72281308868367749817146455 108421963302551624725719683)
    ·
      refine ⟨162632944953827437088579525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108421963302551624725719683 162632944953827437088579525)
      ·
        refine ⟨30493677178842644454108661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 162632944953827437088579525 30493677178842644454108661)
        ·
          refine ⟨2858782235516497917572687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 30493677178842644454108661 2858782235516497917572687)
          ·
            refine ⟨4288173353274746876359031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2858782235516497917572687 4288173353274746876359031)
            ·
              refine ⟨6432260029912120314538547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4288173353274746876359031 6432260029912120314538547)
              ·
                refine ⟨9648390044868180471807821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6432260029912120314538547 9648390044868180471807821)
                ·
                  refine ⟨3618146266825567676927933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9648390044868180471807821 3618146266825567676927933)
                  ·
                    refine ⟨1356804850059587878847975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3618146266825567676927933 1356804850059587878847975)
                    ·
                      rfl

theorem cell22_3963552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 5, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 5, 1, 1, 1, 3, 3].length) (baseStart_3963552 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3963552 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3963552 prefixEnd_3963552 := by exact prefixLift 3963552
  have htrace : WordTrace (prefixWord ++ tailWord_3963552) baseStart_3963552 baseEnd_3963552 := by
    simpa [prefixWord, tailWord_3963552, baseEnd_3963552] using wordTrace_append hprefix tailTrace_3963552
  have hstable : (prefixWord ++ tailWord_3963552).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3963552).length < 2 ^ (prefixWord ++ tailWord_3963552).sum := by decide
  have hdescent : baseEnd_3963552 < baseStart_3963552 := by decide
  rcases family_descends (prefixWord ++ tailWord_3963552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3963565 : List Nat := [1, 5, 2, 1, 1, 2, 4, 1, 5]
def baseStart_3963565 : Nat := 118140960795 + 3963565 * 2 ^ 59
def prefixEnd_3963565 : Nat := 4983230072969 + 3 ^ 40 * 3963565 * 2
def baseEnd_3963565 : Nat := 452269766741753392757645

theorem tailTrace_3963565 : CollatzResearch.WordTrace tailWord_3963565 prefixEnd_3963565 452269766741753392757645 := by
  unfold tailWord_3963565
  simp only [CollatzResearch.WordTrace]
  refine ⟨144563091885688402854516149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96375394590458935236344099 144563091885688402854516149)
  ·
    refine ⟨13552789864283287767610889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 144563091885688402854516149 13552789864283287767610889)
    ·
      refine ⟨10164592398212465825708167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13552789864283287767610889 10164592398212465825708167)
      ·
        refine ⟨15246888597318698738562251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10164592398212465825708167 15246888597318698738562251)
        ·
          refine ⟨22870332895978048107843377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15246888597318698738562251 22870332895978048107843377)
          ·
            refine ⟨17152749671983536080882533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22870332895978048107843377 17152749671983536080882533)
            ·
              refine ⟨3216140563496913015165475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17152749671983536080882533 3216140563496913015165475)
              ·
                refine ⟨4824210845245369522748213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3216140563496913015165475 4824210845245369522748213)
                ·
                  refine ⟨452269766741753392757645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4824210845245369522748213 452269766741753392757645)
                  ·
                    rfl

theorem cell22_3963565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 4, 1, 5].length) (baseStart_3963565 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3963565 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3963565 prefixEnd_3963565 := by exact prefixLift 3963565
  have htrace : WordTrace (prefixWord ++ tailWord_3963565) baseStart_3963565 baseEnd_3963565 := by
    simpa [prefixWord, tailWord_3963565, baseEnd_3963565] using wordTrace_append hprefix tailTrace_3963565
  have hstable : (prefixWord ++ tailWord_3963565).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3963565).length < 2 ^ (prefixWord ++ tailWord_3963565).sum := by decide
  have hdescent : baseEnd_3963565 < baseStart_3963565 := by decide
  rcases family_descends (prefixWord ++ tailWord_3963565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3963696 : List Nat := [2, 1, 1, 1, 2, 2, 1, 2, 2, 8]
def baseStart_3963696 : Nat := 118140960795 + 3963696 * 2 ^ 59
def prefixEnd_3963696 : Nat := 4983230072969 + 3 ^ 40 * 3963696 * 2
def baseEnd_3963696 : Nat := 1356854144202419503247533

theorem tailTrace_3963696 : CollatzResearch.WordTrace tailWord_3963696 prefixEnd_3963696 1356854144202419503247533 := by
  unfold tailWord_3963696
  simp only [CollatzResearch.WordTrace]
  refine ⟨72283934924106906113767471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96378579898809208151689961 72283934924106906113767471)
  ·
    refine ⟨108425902386160359170651207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72283934924106906113767471 108425902386160359170651207)
    ·
      refine ⟨162638853579240538755976811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108425902386160359170651207 162638853579240538755976811)
      ·
        refine ⟨243958280368860808133965217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162638853579240538755976811 243958280368860808133965217)
        ·
          refine ⟨182968710276645606100473913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 243958280368860808133965217 182968710276645606100473913)
          ·
            refine ⟨137226532707484204575355435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 182968710276645606100473913 137226532707484204575355435)
            ·
              refine ⟨205839799061226306863033153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 137226532707484204575355435 205839799061226306863033153)
              ·
                refine ⟨154379849295919730147274865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 205839799061226306863033153 154379849295919730147274865)
                ·
                  refine ⟨115784886971939797610456149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 154379849295919730147274865 115784886971939797610456149)
                  ·
                    refine ⟨1356854144202419503247533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 115784886971939797610456149 1356854144202419503247533)
                    ·
                      rfl

theorem cell22_3963696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 2, 2, 8].length) (baseStart_3963696 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3963696 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3963696 prefixEnd_3963696 := by exact prefixLift 3963696
  have htrace : WordTrace (prefixWord ++ tailWord_3963696) baseStart_3963696 baseEnd_3963696 := by
    simpa [prefixWord, tailWord_3963696, baseEnd_3963696] using wordTrace_append hprefix tailTrace_3963696
  have hstable : (prefixWord ++ tailWord_3963696).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3963696).length < 2 ^ (prefixWord ++ tailWord_3963696).sum := by decide
  have hdescent : baseEnd_3963696 < baseStart_3963696 := by decide
  rcases family_descends (prefixWord ++ tailWord_3963696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3963728 : List Nat := [2, 1, 1, 1, 1, 4, 5, 1, 6]
def baseStart_3963728 : Nat := 118140960795 + 3963728 * 2 ^ 59
def prefixEnd_3963728 : Nat := 4983230072969 + 3 ^ 40 * 3963728 * 2
def baseEnd_3963728 : Nat := 452288366152127362149145

theorem tailTrace_3963728 : CollatzResearch.WordTrace tailWord_3963728 prefixEnd_3963728 452288366152127362149145 := by
  unfold tailWord_3963728
  simp only [CollatzResearch.WordTrace]
  refine ⟨72284518492048940846349919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96379357989398587795133225 72284518492048940846349919)
  ·
    refine ⟨108426777738073411269524879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72284518492048940846349919 108426777738073411269524879)
    ·
      refine ⟨162640166607110116904287319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108426777738073411269524879 162640166607110116904287319)
      ·
        refine ⟨243960249910665175356430979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162640166607110116904287319 243960249910665175356430979)
        ·
          refine ⟨365940374865997763034646469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 243960249910665175356430979 365940374865997763034646469)
          ·
            refine ⟨68613820287374580568996213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 365940374865997763034646469 68613820287374580568996213)
            ·
              refine ⟨6432545651941366928343395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 68613820287374580568996213 6432545651941366928343395)
              ·
                refine ⟨9648818477912050392515093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6432545651941366928343395 9648818477912050392515093)
                ·
                  refine ⟨452288366152127362149145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9648818477912050392515093 452288366152127362149145)
                  ·
                    rfl

theorem cell22_3963728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 5, 1, 6].length) (baseStart_3963728 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3963728 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3963728 prefixEnd_3963728 := by exact prefixLift 3963728
  have htrace : WordTrace (prefixWord ++ tailWord_3963728) baseStart_3963728 baseEnd_3963728 := by
    simpa [prefixWord, tailWord_3963728, baseEnd_3963728] using wordTrace_append hprefix tailTrace_3963728
  have hstable : (prefixWord ++ tailWord_3963728).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3963728).length < 2 ^ (prefixWord ++ tailWord_3963728).sum := by decide
  have hdescent : baseEnd_3963728 < baseStart_3963728 := by decide
  rcases family_descends (prefixWord ++ tailWord_3963728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3963743 : List Nat := [1, 1, 2, 3, 1, 3, 2, 3, 1, 5]
def baseStart_3963743 : Nat := 118140960795 + 3963743 * 2 ^ 59
def prefixEnd_3963743 : Nat := 4983230072969 + 3 ^ 40 * 3963743 * 2
def baseEnd_3963743 : Nat := 1356870233262927047322389

theorem tailTrace_3963743 : CollatzResearch.WordTrace tailWord_3963743 prefixEnd_3963743 1356870233262927047322389 := by
  unfold tailWord_3963743
  simp only [CollatzResearch.WordTrace]
  refine ⟨144569584079043539254495883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96379722719362359502997255 144569584079043539254495883)
  ·
    refine ⟨216854376118565308881743825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144569584079043539254495883 216854376118565308881743825)
    ·
      refine ⟨162640782088923981661307869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 216854376118565308881743825 162640782088923981661307869)
      ·
        refine ⟨60990293283346493122990451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 162640782088923981661307869 60990293283346493122990451)
        ·
          refine ⟨91485439925019739684485677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60990293283346493122990451 91485439925019739684485677)
          ·
            refine ⟨34307039971882402381682129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 91485439925019739684485677 34307039971882402381682129)
            ·
              refine ⟨25730279978911801786261597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34307039971882402381682129 25730279978911801786261597)
              ·
                refine ⟨9648854992091925669848099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25730279978911801786261597 9648854992091925669848099)
                ·
                  refine ⟨14473282488137888504772149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9648854992091925669848099 14473282488137888504772149)
                  ·
                    refine ⟨1356870233262927047322389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14473282488137888504772149 1356870233262927047322389)
                    ·
                      rfl

theorem cell22_3963743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 2, 3, 1, 5].length) (baseStart_3963743 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3963743 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3963743 prefixEnd_3963743 := by exact prefixLift 3963743
  have htrace : WordTrace (prefixWord ++ tailWord_3963743) baseStart_3963743 baseEnd_3963743 := by
    simpa [prefixWord, tailWord_3963743, baseEnd_3963743] using wordTrace_append hprefix tailTrace_3963743
  have hstable : (prefixWord ++ tailWord_3963743).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3963743).length < 2 ^ (prefixWord ++ tailWord_3963743).sum := by decide
  have hdescent : baseEnd_3963743 < baseStart_3963743 := by decide
  rcases family_descends (prefixWord ++ tailWord_3963743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3963747 : List Nat := [1, 1, 1, 5, 3, 3, 1, 2, 1, 4]
def baseStart_3963747 : Nat := 118140960795 + 3963747 * 2 ^ 59
def prefixEnd_3963747 : Nat := 4983230072969 + 3 ^ 40 * 3963747 * 2
def baseEnd_3963747 : Nat := 1356871602544672370222377

theorem tailTrace_3963747 : CollatzResearch.WordTrace tailWord_3963747 prefixEnd_3963747 1356871602544672370222377 := by
  unfold tailWord_3963747
  simp only [CollatzResearch.WordTrace]
  refine ⟨144569729971029047937641495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96379819980686031958427663 144569729971029047937641495)
  ·
    refine ⟨216854594956543571906462243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144569729971029047937641495 216854594956543571906462243)
    ·
      refine ⟨325281892434815357859693365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216854594956543571906462243 325281892434815357859693365)
      ·
        refine ⟨30495177415763939799346253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 325281892434815357859693365 30495177415763939799346253)
        ·
          refine ⟨11435691530911477424754845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30495177415763939799346253 11435691530911477424754845)
          ·
            refine ⟨4288384324091804034283067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11435691530911477424754845 4288384324091804034283067)
            ·
              refine ⟨6432576486137706051424601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4288384324091804034283067 6432576486137706051424601)
              ·
                refine ⟨4824432364603279538568451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6432576486137706051424601 4824432364603279538568451)
                ·
                  refine ⟨7236648546904919307852677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4824432364603279538568451 7236648546904919307852677)
                  ·
                    refine ⟨1356871602544672370222377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7236648546904919307852677 1356871602544672370222377)
                    ·
                      rfl

theorem cell22_3963747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 3, 1, 2, 1, 4].length) (baseStart_3963747 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3963747 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3963747 prefixEnd_3963747 := by exact prefixLift 3963747
  have htrace : WordTrace (prefixWord ++ tailWord_3963747) baseStart_3963747 baseEnd_3963747 := by
    simpa [prefixWord, tailWord_3963747, baseEnd_3963747] using wordTrace_append hprefix tailTrace_3963747
  have hstable : (prefixWord ++ tailWord_3963747).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3963747).length < 2 ^ (prefixWord ++ tailWord_3963747).sum := by decide
  have hdescent : baseEnd_3963747 < baseStart_3963747 := by decide
  rcases family_descends (prefixWord ++ tailWord_3963747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3963852 : List Nat := [2, 2, 1, 4, 1, 1, 5, 1, 5]
def baseStart_3963852 : Nat := 118140960795 + 3963852 * 2 ^ 59
def prefixEnd_3963852 : Nat := 4983230072969 + 3 ^ 40 * 3963852 * 2
def baseEnd_3963852 : Nat := 452302515396829032115685

theorem tailTrace_3963852 : CollatzResearch.WordTrace tailWord_3963852 prefixEnd_3963852 452302515396829032115685 := by
  unfold tailWord_3963852
  simp only [CollatzResearch.WordTrace]
  refine ⟨72286779817824325435106905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96382373090432433913475873 72286779817824325435106905)
  ·
    refine ⟨54215084863368244076330179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72286779817824325435106905 54215084863368244076330179)
    ·
      refine ⟨81322627295052366114495269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54215084863368244076330179 81322627295052366114495269)
      ·
        refine ⟨15247992617822318646467863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 81322627295052366114495269 15247992617822318646467863)
        ·
          refine ⟨22871988926733477969701795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15247992617822318646467863 22871988926733477969701795)
          ·
            refine ⟨34307983390100216954552693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22871988926733477969701795 34307983390100216954552693)
            ·
              refine ⟨3216373442821895339489315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 34307983390100216954552693 3216373442821895339489315)
              ·
                refine ⟨4824560164232843009233973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3216373442821895339489315 4824560164232843009233973)
                ·
                  refine ⟨452302515396829032115685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4824560164232843009233973 452302515396829032115685)
                  ·
                    rfl

theorem cell22_3963852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 5, 1, 5].length) (baseStart_3963852 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3963852 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3963852 prefixEnd_3963852 := by exact prefixLift 3963852
  have htrace : WordTrace (prefixWord ++ tailWord_3963852) baseStart_3963852 baseEnd_3963852 := by
    simpa [prefixWord, tailWord_3963852, baseEnd_3963852] using wordTrace_append hprefix tailTrace_3963852
  have hstable : (prefixWord ++ tailWord_3963852).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3963852).length < 2 ^ (prefixWord ++ tailWord_3963852).sum := by decide
  have hdescent : baseEnd_3963852 < baseStart_3963852 := by decide
  rcases family_descends (prefixWord ++ tailWord_3963852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3963863 : List Nat := [1, 1, 3, 2, 1, 1, 2, 3, 8]
def baseStart_3963863 : Nat := 118140960795 + 3963863 * 2 ^ 59
def prefixEnd_3963863 : Nat := 4983230072969 + 3 ^ 40 * 3963863 * 2
def baseEnd_3963863 : Nat := 452303770571762244774007

theorem tailTrace_3963863 : CollatzResearch.WordTrace tailWord_3963863 prefixEnd_3963863 452303770571762244774007 := by
  unfold tailWord_3963863
  simp only [CollatzResearch.WordTrace]
  refine ⟨144573960838608799748864243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96382640559072533165909495 144573960838608799748864243)
  ·
    refine ⟨216860941257913199623296365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144573960838608799748864243 216860941257913199623296365)
    ·
      refine ⟨81322852971717449858736137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 216860941257913199623296365 81322852971717449858736137)
      ·
        refine ⟨60992139728788087394052103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81322852971717449858736137 60992139728788087394052103)
        ·
          refine ⟨91488209593182131091078155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60992139728788087394052103 91488209593182131091078155)
          ·
            refine ⟨137232314389773196636617233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91488209593182131091078155 137232314389773196636617233)
            ·
              refine ⟨102924235792329897477462925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 137232314389773196636617233 102924235792329897477462925)
              ·
                refine ⟨38596588422123711554048597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 102924235792329897477462925 38596588422123711554048597)
                ·
                  refine ⟨452303770571762244774007, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 38596588422123711554048597 452303770571762244774007)
                  ·
                    rfl

theorem cell22_3963863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 3, 8].length) (baseStart_3963863 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3963863 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3963863 prefixEnd_3963863 := by exact prefixLift 3963863
  have htrace : WordTrace (prefixWord ++ tailWord_3963863) baseStart_3963863 baseEnd_3963863 := by
    simpa [prefixWord, tailWord_3963863, baseEnd_3963863] using wordTrace_append hprefix tailTrace_3963863
  have hstable : (prefixWord ++ tailWord_3963863).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3963863).length < 2 ^ (prefixWord ++ tailWord_3963863).sum := by decide
  have hdescent : baseEnd_3963863 < baseStart_3963863 := by decide
  rcases family_descends (prefixWord ++ tailWord_3963863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3963882 : List Nat := [3, 1, 3, 1, 2, 2, 2, 3, 1, 4]
def baseStart_3963882 : Nat := 118140960795 + 3963882 * 2 ^ 59
def prefixEnd_3963882 : Nat := 4983230072969 + 3 ^ 40 * 3963882 * 2
def baseEnd_3963882 : Nat := 1356917815803577018096963

theorem tailTrace_3963882 : CollatzResearch.WordTrace tailWord_3963882 prefixEnd_3963882 1356917815803577018096963 := by
  unfold tailWord_3963882
  simp only [CollatzResearch.WordTrace]
  refine ⟨36143663456384991498451475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96383102550359977329203933 36143663456384991498451475)
  ·
    refine ⟨54215495184577487247677213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36143663456384991498451475 54215495184577487247677213)
    ·
      refine ⟨20330810694216557717878955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54215495184577487247677213 20330810694216557717878955)
      ·
        refine ⟨30496216041324836576818433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20330810694216557717878955 30496216041324836576818433)
        ·
          refine ⟨22872162030993627432613825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30496216041324836576818433 22872162030993627432613825)
          ·
            refine ⟨17154121523245220574460369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22872162030993627432613825 17154121523245220574460369)
            ·
              refine ⟨12865591142433915430845277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17154121523245220574460369 12865591142433915430845277)
              ·
                refine ⟨4824596678412718286566979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12865591142433915430845277 4824596678412718286566979)
                ·
                  refine ⟨7236895017619077429850469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4824596678412718286566979 7236895017619077429850469)
                  ·
                    refine ⟨1356917815803577018096963, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7236895017619077429850469 1356917815803577018096963)
                    ·
                      rfl

theorem cell22_3963882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 2, 3, 1, 4].length) (baseStart_3963882 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3963882 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3963882 prefixEnd_3963882 := by exact prefixLift 3963882
  have htrace : WordTrace (prefixWord ++ tailWord_3963882) baseStart_3963882 baseEnd_3963882 := by
    simpa [prefixWord, tailWord_3963882, baseEnd_3963882] using wordTrace_append hprefix tailTrace_3963882
  have hstable : (prefixWord ++ tailWord_3963882).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3963882).length < 2 ^ (prefixWord ++ tailWord_3963882).sum := by decide
  have hdescent : baseEnd_3963882 < baseStart_3963882 := by decide
  rcases family_descends (prefixWord ++ tailWord_3963882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3963925 : List Nat := [1, 3, 2, 1, 4, 1, 2, 8]
def baseStart_3963925 : Nat := 118140960795 + 3963925 * 2 ^ 59
def prefixEnd_3963925 : Nat := 4983230072969 + 3 ^ 40 * 3963925 * 2
def baseEnd_3963925 : Nat := 150770281731371026585759

theorem tailTrace_3963925 : CollatzResearch.WordTrace tailWord_3963925 prefixEnd_3963925 150770281731371026585759 := by
  unfold tailWord_3963925
  simp only [CollatzResearch.WordTrace]
  refine ⟨144576222164384184337621229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96384148109589456225080819 144576222164384184337621229)
  ·
    refine ⟨54216083311644069126607961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 144576222164384184337621229 54216083311644069126607961)
    ·
      refine ⟨40662062483733051844955971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54216083311644069126607961 40662062483733051844955971)
      ·
        refine ⟨60993093725599577767433957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40662062483733051844955971 60993093725599577767433957)
        ·
          refine ⟨11436205073549920831393867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 60993093725599577767433957 11436205073549920831393867)
          ·
            refine ⟨17154307610324881247090801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11436205073549920831393867 17154307610324881247090801)
            ·
              refine ⟨12865730707743660935318101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17154307610324881247090801 12865730707743660935318101)
              ·
                refine ⟨150770281731371026585759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12865730707743660935318101 150770281731371026585759)
                ·
                  rfl

theorem cell22_3963925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 2, 8].length) (baseStart_3963925 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3963925 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3963925 prefixEnd_3963925 := by exact prefixLift 3963925
  have htrace : WordTrace (prefixWord ++ tailWord_3963925) baseStart_3963925 baseEnd_3963925 := by
    simpa [prefixWord, tailWord_3963925, baseEnd_3963925] using wordTrace_append hprefix tailTrace_3963925
  have hstable : (prefixWord ++ tailWord_3963925).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3963925).length < 2 ^ (prefixWord ++ tailWord_3963925).sum := by decide
  have hdescent : baseEnd_3963925 < baseStart_3963925 := by decide
  rcases family_descends (prefixWord ++ tailWord_3963925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3963927 : List Nat := [1, 1, 3, 5, 1, 1, 1, 3, 2, 4]
def baseStart_3963927 : Nat := 118140960795 + 3963927 * 2 ^ 59
def prefixEnd_3963927 : Nat := 4983230072969 + 3 ^ 40 * 3963927 * 2
def baseEnd_3963927 : Nat := 1356933220223211900721825

theorem tailTrace_3963927 : CollatzResearch.WordTrace tailWord_3963927 prefixEnd_3963927 1356933220223211900721825 := by
  unfold tailWord_3963927
  simp only [CollatzResearch.WordTrace]
  refine ⟨144576295110376938679194035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96384196740251292452796023 144576295110376938679194035)
  ·
    refine ⟨216864442665565408018791053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144576295110376938679194035 216864442665565408018791053)
    ·
      refine ⟨81324165999587028007046645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 216864442665565408018791053 81324165999587028007046645)
      ·
        refine ⟨7624140562461283875660623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 81324165999587028007046645 7624140562461283875660623)
        ·
          refine ⟨11436210843691925813490935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7624140562461283875660623 11436210843691925813490935)
          ·
            refine ⟨17154316265537888720236403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11436210843691925813490935 17154316265537888720236403)
            ·
              refine ⟨25731474398306833080354605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17154316265537888720236403 25731474398306833080354605)
              ·
                refine ⟨9649302899365062405132977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25731474398306833080354605 9649302899365062405132977)
                ·
                  refine ⟨7236977174523796803849733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9649302899365062405132977 7236977174523796803849733)
                  ·
                    refine ⟨1356933220223211900721825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7236977174523796803849733 1356933220223211900721825)
                    ·
                      rfl

theorem cell22_3963927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 1, 3, 2, 4].length) (baseStart_3963927 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3963927 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3963927 prefixEnd_3963927 := by exact prefixLift 3963927
  have htrace : WordTrace (prefixWord ++ tailWord_3963927) baseStart_3963927 baseEnd_3963927 := by
    simpa [prefixWord, tailWord_3963927, baseEnd_3963927] using wordTrace_append hprefix tailTrace_3963927
  have hstable : (prefixWord ++ tailWord_3963927).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3963927).length < 2 ^ (prefixWord ++ tailWord_3963927).sum := by decide
  have hdescent : baseEnd_3963927 < baseStart_3963927 := by decide
  rcases family_descends (prefixWord ++ tailWord_3963927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3963946 : List Nat := [3, 1, 4, 1, 3, 1, 2, 2, 2, 3]
def baseStart_3963946 : Nat := 118140960795 + 3963946 * 2 ^ 59
def prefixEnd_3963946 : Nat := 4983230072969 + 3 ^ 40 * 3963946 * 2
def baseEnd_3963946 : Nat := 1356939724311502184496767

theorem tailTrace_3963946 : CollatzResearch.WordTrace tailWord_3963946 prefixEnd_3963946 1356939724311502184496767 := by
  unfold tailWord_3963946
  simp only [CollatzResearch.WordTrace]
  refine ⟨36144247024327026231033923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96384658731538736616090461 36144247024327026231033923)
  ·
    refine ⟨54216370536490539346550885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36144247024327026231033923 54216370536490539346550885)
    ·
      refine ⟨10165569475591976127478291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 54216370536490539346550885 10165569475591976127478291)
      ·
        refine ⟨15248354213387964191217437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10165569475591976127478291 15248354213387964191217437)
        ·
          refine ⟨5718132830020486571706539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15248354213387964191217437 5718132830020486571706539)
          ·
            refine ⟨8577199245030729857559809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5718132830020486571706539 8577199245030729857559809)
            ·
              refine ⟨6432899433773047393169857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8577199245030729857559809 6432899433773047393169857)
              ·
                refine ⟨4824674575329785544877393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6432899433773047393169857 4824674575329785544877393)
                ·
                  refine ⟨3618505931497339158658045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4824674575329785544877393 3618505931497339158658045)
                  ·
                    refine ⟨1356939724311502184496767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3618505931497339158658045 1356939724311502184496767)
                    ·
                      rfl

theorem cell22_3963946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 2, 2, 2, 3].length) (baseStart_3963946 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3963946 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3963946 prefixEnd_3963946 := by exact prefixLift 3963946
  have htrace : WordTrace (prefixWord ++ tailWord_3963946) baseStart_3963946 baseEnd_3963946 := by
    simpa [prefixWord, tailWord_3963946, baseEnd_3963946] using wordTrace_append hprefix tailTrace_3963946
  have hstable : (prefixWord ++ tailWord_3963946).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3963946).length < 2 ^ (prefixWord ++ tailWord_3963946).sum := by decide
  have hdescent : baseEnd_3963946 < baseStart_3963946 := by decide
  rcases family_descends (prefixWord ++ tailWord_3963946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3963957 : List Nat := [1, 3, 3, 1, 1, 1, 1, 5, 3, 3]
def baseStart_3963957 : Nat := 118140960795 + 3963957 * 2 ^ 59
def prefixEnd_3963957 : Nat := 4983230072969 + 3 ^ 40 * 3963957 * 2
def baseEnd_3963957 : Nat := 1356943489836301822471733

theorem tailTrace_3963957 : CollatzResearch.WordTrace tailWord_3963957 prefixEnd_3963957 1356943489836301822471733 := by
  unfold tailWord_3963957
  simp only [CollatzResearch.WordTrace]
  refine ⟨144577389300268253802786125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96384926200178835868524083 144577389300268253802786125)
  ·
    refine ⟨54216520987600595176044797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 144577389300268253802786125 54216520987600595176044797)
    ·
      refine ⟨20331195370350223191016799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54216520987600595176044797 20331195370350223191016799)
      ·
        refine ⟨30496793055525334786525199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20331195370350223191016799 30496793055525334786525199)
        ·
          refine ⟨45745189583288002179787799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30496793055525334786525199 45745189583288002179787799)
          ·
            refine ⟨68617784374932003269681699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45745189583288002179787799 68617784374932003269681699)
            ·
              refine ⟨102926676562398004904522549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68617784374932003269681699 102926676562398004904522549)
              ·
                refine ⟨9649375927724812959798989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 102926676562398004904522549 9649375927724812959798989)
                ·
                  refine ⟨3618515972896804859924621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9649375927724812959798989 3618515972896804859924621)
                  ·
                    refine ⟨1356943489836301822471733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3618515972896804859924621 1356943489836301822471733)
                    ·
                      rfl

theorem cell22_3963957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 5, 3, 3].length) (baseStart_3963957 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3963957 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3963957 prefixEnd_3963957 := by exact prefixLift 3963957
  have htrace : WordTrace (prefixWord ++ tailWord_3963957) baseStart_3963957 baseEnd_3963957 := by
    simpa [prefixWord, tailWord_3963957, baseEnd_3963957] using wordTrace_append hprefix tailTrace_3963957
  have hstable : (prefixWord ++ tailWord_3963957).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3963957).length < 2 ^ (prefixWord ++ tailWord_3963957).sum := by decide
  have hdescent : baseEnd_3963957 < baseStart_3963957 := by decide
  rcases family_descends (prefixWord ++ tailWord_3963957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3964064 : List Nat := [2, 1, 1, 4, 2, 1, 2, 4, 2, 3]
def baseStart_3964064 : Nat := 118140960795 + 3964064 * 2 ^ 59
def prefixEnd_3964064 : Nat := 4983230072969 + 3 ^ 40 * 3964064 * 2
def baseEnd_3964064 : Nat := 1356980118122989210046405

theorem tailTrace_3964064 : CollatzResearch.WordTrace tailWord_3964064 prefixEnd_3964064 1356980118122989210046405 := by
  unfold tailWord_3964064
  simp only [CollatzResearch.WordTrace]
  refine ⟨72290645955440305538465623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96387527940587074051287497 72290645955440305538465623)
  ·
    refine ⟨108435968933160458307698435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72290645955440305538465623 108435968933160458307698435)
    ·
      refine ⟨162653953399740687461547653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108435968933160458307698435 162653953399740687461547653)
      ·
        refine ⟨30497616262451378899040185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 162653953399740687461547653 30497616262451378899040185)
        ·
          refine ⟨22873212196838534174280139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30497616262451378899040185 22873212196838534174280139)
          ·
            refine ⟨34309818295257801261420209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22873212196838534174280139 34309818295257801261420209)
            ·
              refine ⟨25732363721443350946065157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34309818295257801261420209 25732363721443350946065157)
              ·
                refine ⟨4824818197770628302387217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25732363721443350946065157 4824818197770628302387217)
                ·
                  refine ⟨3618613648327971226790413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4824818197770628302387217 3618613648327971226790413)
                  ·
                    refine ⟨1356980118122989210046405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3618613648327971226790413 1356980118122989210046405)
                    ·
                      rfl

theorem cell22_3964064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 2, 4, 2, 3].length) (baseStart_3964064 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3964064 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3964064 prefixEnd_3964064 := by exact prefixLift 3964064
  have htrace : WordTrace (prefixWord ++ tailWord_3964064) baseStart_3964064 baseEnd_3964064 := by
    simpa [prefixWord, tailWord_3964064, baseEnd_3964064] using wordTrace_append hprefix tailTrace_3964064
  have hstable : (prefixWord ++ tailWord_3964064).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3964064).length < 2 ^ (prefixWord ++ tailWord_3964064).sum := by decide
  have hdescent : baseEnd_3964064 < baseStart_3964064 := by decide
  rcases family_descends (prefixWord ++ tailWord_3964064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3964066 : List Nat := [3, 3, 1, 3, 2, 2, 1, 1, 6]
def baseStart_3964066 : Nat := 118140960795 + 3964066 * 2 ^ 59
def prefixEnd_3964066 : Nat := 4983230072969 + 3 ^ 40 * 3964066 * 2
def baseEnd_3964066 : Nat := 452326934254620623832133

theorem tailTrace_3964066 : CollatzResearch.WordTrace tailWord_3964066 prefixEnd_3964066 452326934254620623832133 := by
  unfold tailWord_3964066
  simp only [CollatzResearch.WordTrace]
  refine ⟨36145341214218341354626013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96387576571248910279002701 36145341214218341354626013)
  ·
    refine ⟨13554502955331878007984755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36145341214218341354626013 13554502955331878007984755)
    ·
      refine ⟨20331754432997817011977133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13554502955331878007984755 20331754432997817011977133)
      ·
        refine ⟨7624407912374181379491425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20331754432997817011977133 7624407912374181379491425)
        ·
          refine ⟨5718305934280636034618569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7624407912374181379491425 5718305934280636034618569)
          ·
            refine ⟨4288729450710477025963927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5718305934280636034618569 4288729450710477025963927)
            ·
              refine ⟨6433094176065715538945891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4288729450710477025963927 6433094176065715538945891)
              ·
                refine ⟨9649641264098573308418837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6433094176065715538945891 9649641264098573308418837)
                ·
                  refine ⟨452326934254620623832133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9649641264098573308418837 452326934254620623832133)
                  ·
                    rfl

theorem cell22_3964066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 2, 1, 1, 6].length) (baseStart_3964066 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3964066 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3964066 prefixEnd_3964066 := by exact prefixLift 3964066
  have htrace : WordTrace (prefixWord ++ tailWord_3964066) baseStart_3964066 baseEnd_3964066 := by
    simpa [prefixWord, tailWord_3964066, baseEnd_3964066] using wordTrace_append hprefix tailTrace_3964066
  have hstable : (prefixWord ++ tailWord_3964066).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3964066).length < 2 ^ (prefixWord ++ tailWord_3964066).sum := by decide
  have hdescent : baseEnd_3964066 < baseStart_3964066 := by decide
  rcases family_descends (prefixWord ++ tailWord_3964066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3964081 : List Nat := [1, 2, 2, 5, 1, 2, 1, 3, 2, 3]
def baseStart_3964081 : Nat := 118140960795 + 3964081 * 2 ^ 59
def prefixEnd_3964081 : Nat := 4983230072969 + 3 ^ 40 * 3964081 * 2
def baseEnd_3964081 : Nat := 1356985937570406832371353

theorem tailTrace_3964081 : CollatzResearch.WordTrace tailWord_3964081 prefixEnd_3964081 1356985937570406832371353 := by
  unfold tailWord_3964081
  simp only [CollatzResearch.WordTrace]
  refine ⟨144581911951819022980300097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96387941301212681986866731 144581911951819022980300097)
  ·
    refine ⟨108436433963864267235225073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144581911951819022980300097 108436433963864267235225073)
    ·
      refine ⟨81327325472898200426418805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108436433963864267235225073 81327325472898200426418805)
      ·
        refine ⟨7624436763084206289976763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 81327325472898200426418805 7624436763084206289976763)
        ·
          refine ⟨11436655144626309434965145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7624436763084206289976763 11436655144626309434965145)
          ·
            refine ⟨8577491358469732076223859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11436655144626309434965145 8577491358469732076223859)
            ·
              refine ⟨12866237037704598114335789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8577491358469732076223859 12866237037704598114335789)
              ·
                refine ⟨4824838889139224292875921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12866237037704598114335789 4824838889139224292875921)
                ·
                  refine ⟨3618629166854418219656941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4824838889139224292875921 3618629166854418219656941)
                  ·
                    refine ⟨1356985937570406832371353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3618629166854418219656941 1356985937570406832371353)
                    ·
                      rfl

theorem cell22_3964081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 1, 3, 2, 3].length) (baseStart_3964081 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3964081 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3964081 prefixEnd_3964081 := by exact prefixLift 3964081
  have htrace : WordTrace (prefixWord ++ tailWord_3964081) baseStart_3964081 baseEnd_3964081 := by
    simpa [prefixWord, tailWord_3964081, baseEnd_3964081] using wordTrace_append hprefix tailTrace_3964081
  have hstable : (prefixWord ++ tailWord_3964081).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3964081).length < 2 ^ (prefixWord ++ tailWord_3964081).sum := by decide
  have hdescent : baseEnd_3964081 < baseStart_3964081 := by decide
  rcases family_descends (prefixWord ++ tailWord_3964081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3964098 : List Nat := [3, 5, 1, 1, 2, 1, 1, 2, 1, 5]
def baseStart_3964098 : Nat := 118140960795 + 3964098 * 2 ^ 59
def prefixEnd_3964098 : Nat := 4983230072969 + 3 ^ 40 * 3964098 * 2
def baseEnd_3964098 : Nat := 1356991757017824454696301

theorem tailTrace_3964098 : CollatzResearch.WordTrace tailWord_3964098 prefixEnd_3964098 1356991757017824454696301 := by
  unfold tailWord_3964098
  simp only [CollatzResearch.WordTrace]
  refine ⟨36145632998189358720917237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96388354661838289922445965 36145632998189358720917237)
  ·
    refine ⟨3388653093580252380085991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 36145632998189358720917237 3388653093580252380085991)
    ·
      refine ⟨5082979640370378570128987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3388653093580252380085991 5082979640370378570128987)
      ·
        refine ⟨7624469460555567855193481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5082979640370378570128987 7624469460555567855193481)
        ·
          refine ⟨5718352095416675891395111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7624469460555567855193481 5718352095416675891395111)
          ·
            refine ⟨8577528143125013837092667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5718352095416675891395111 8577528143125013837092667)
            ·
              refine ⟨12866292214687520755639001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8577528143125013837092667 12866292214687520755639001)
              ·
                refine ⟨9649719161015640566729251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12866292214687520755639001 9649719161015640566729251)
                ·
                  refine ⟨14474578741523460850093877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9649719161015640566729251 14474578741523460850093877)
                  ·
                    refine ⟨1356991757017824454696301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14474578741523460850093877 1356991757017824454696301)
                    ·
                      rfl

theorem cell22_3964098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 1, 2, 1, 5].length) (baseStart_3964098 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3964098 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3964098 prefixEnd_3964098 := by exact prefixLift 3964098
  have htrace : WordTrace (prefixWord ++ tailWord_3964098) baseStart_3964098 baseEnd_3964098 := by
    simpa [prefixWord, tailWord_3964098, baseEnd_3964098] using wordTrace_append hprefix tailTrace_3964098
  have hstable : (prefixWord ++ tailWord_3964098).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3964098).length < 2 ^ (prefixWord ++ tailWord_3964098).sum := by decide
  have hdescent : baseEnd_3964098 < baseStart_3964098 := by decide
  rcases family_descends (prefixWord ++ tailWord_3964098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3964102 : List Nat := [6, 1, 2, 2, 1, 1, 3, 1, 1, 4]
def baseStart_3964102 : Nat := 118140960795 + 3964102 * 2 ^ 59
def prefixEnd_3964102 : Nat := 4983230072969 + 3 ^ 40 * 3964102 * 2
def baseEnd_3964102 : Nat := 1356993126299569777596289

theorem tailTrace_3964102 : CollatzResearch.WordTrace tailWord_3964102 prefixEnd_3964102 1356993126299569777596289 := by
  unfold tailWord_3964102
  simp only [CollatzResearch.WordTrace]
  refine ⟨4518208683898216986462955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 96388451923161962377876373 4518208683898216986462955)
  ·
    refine ⟨6777313025847325479694433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4518208683898216986462955 6777313025847325479694433)
    ·
      refine ⟨5082984769385494109770825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6777313025847325479694433 5082984769385494109770825)
      ·
        refine ⟨3812238577039120582328119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5082984769385494109770825 3812238577039120582328119)
        ·
          refine ⟨5718357865558680873492179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3812238577039120582328119 5718357865558680873492179)
          ·
            refine ⟨8577536798338021310238269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5718357865558680873492179 8577536798338021310238269)
            ·
              refine ⟨3216576299376757991339351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8577536798338021310238269 3216576299376757991339351)
              ·
                refine ⟨4824864449065136987009027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3216576299376757991339351 4824864449065136987009027)
                ·
                  refine ⟨7237296673597705480513541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4824864449065136987009027 7237296673597705480513541)
                  ·
                    refine ⟨1356993126299569777596289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7237296673597705480513541 1356993126299569777596289)
                    ·
                      rfl

theorem cell22_3964102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 3, 1, 1, 4].length) (baseStart_3964102 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3964102 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3964102 prefixEnd_3964102 := by exact prefixLift 3964102
  have htrace : WordTrace (prefixWord ++ tailWord_3964102) baseStart_3964102 baseEnd_3964102 := by
    simpa [prefixWord, tailWord_3964102, baseEnd_3964102] using wordTrace_append hprefix tailTrace_3964102
  have hstable : (prefixWord ++ tailWord_3964102).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3964102).length < 2 ^ (prefixWord ++ tailWord_3964102).sum := by decide
  have hdescent : baseEnd_3964102 < baseStart_3964102 := by decide
  rcases family_descends (prefixWord ++ tailWord_3964102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3964169 : List Nat := [1, 2, 1, 1, 3, 3, 3, 3, 1, 4]
def baseStart_3964169 : Nat := 118140960795 + 3964169 * 2 ^ 59
def prefixEnd_3964169 : Nat := 4983230072969 + 3 ^ 40 * 3964169 * 2
def baseEnd_3964169 : Nat := 1357016061768803936171083

theorem tailTrace_3964169 : CollatzResearch.WordTrace tailWord_3964169 prefixEnd_3964169 1357016061768803936171083 := by
  unfold tailWord_3964169
  simp only [CollatzResearch.WordTrace]
  refine ⟨144585121575500214009503561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96390081050333476006335707 144585121575500214009503561)
  ·
    refine ⟨108438841181625160507127671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144585121575500214009503561 108438841181625160507127671)
    ·
      refine ⟨162658261772437740760691507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108438841181625160507127671 162658261772437740760691507)
      ·
        refine ⟨243987392658656611141037261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162658261772437740760691507 243987392658656611141037261)
        ·
          refine ⟨91495272246996229177888973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 243987392658656611141037261 91495272246996229177888973)
          ·
            refine ⟨34310727092623585941708365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 91495272246996229177888973 34310727092623585941708365)
            ·
              refine ⟨12866522659733844728140637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34310727092623585941708365 12866522659733844728140637)
              ·
                refine ⟨4824945997400191773052739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12866522659733844728140637 4824945997400191773052739)
                ·
                  refine ⟨7237418996100287659579109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4824945997400191773052739 7237418996100287659579109)
                  ·
                    refine ⟨1357016061768803936171083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7237418996100287659579109 1357016061768803936171083)
                    ·
                      rfl

theorem cell22_3964169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 3, 3, 1, 4].length) (baseStart_3964169 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3964169 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3964169 prefixEnd_3964169 := by exact prefixLift 3964169
  have htrace : WordTrace (prefixWord ++ tailWord_3964169) baseStart_3964169 baseEnd_3964169 := by
    simpa [prefixWord, tailWord_3964169, baseEnd_3964169] using wordTrace_append hprefix tailTrace_3964169
  have hstable : (prefixWord ++ tailWord_3964169).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3964169).length < 2 ^ (prefixWord ++ tailWord_3964169).sum := by decide
  have hdescent : baseEnd_3964169 < baseStart_3964169 := by decide
  rcases family_descends (prefixWord ++ tailWord_3964169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3964184 : List Nat := [2, 1, 2, 3, 1, 4, 2, 1, 6]
def baseStart_3964184 : Nat := 118140960795 + 3964184 * 2 ^ 59
def prefixEnd_3964184 : Nat := 4983230072969 + 3 ^ 40 * 3964184 * 2
def baseEnd_3964184 : Nat := 452340398858449632348679

theorem tailTrace_3964184 : CollatzResearch.WordTrace tailWord_3964184 prefixEnd_3964184 452340398858449632348679 := by
  unfold tailWord_3964184
  simp only [CollatzResearch.WordTrace]
  refine ⟨72292834335222935785649803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96390445780297247714199737 72292834335222935785649803)
  ·
    refine ⟨108439251502834403678474705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72292834335222935785649803 108439251502834403678474705)
    ·
      refine ⟨81329438627125802758856029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108439251502834403678474705 81329438627125802758856029)
      ·
        refine ⟨30498539485172176034571011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81329438627125802758856029 30498539485172176034571011)
        ·
          refine ⟨45747809227758264051856517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30498539485172176034571011 45747809227758264051856517)
          ·
            refine ⟨8577714230204674509723097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45747809227758264051856517 8577714230204674509723097)
            ·
              refine ⟨6433285672653505882292323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8577714230204674509723097 6433285672653505882292323)
              ·
                refine ⟨9649928508980258823438485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6433285672653505882292323 9649928508980258823438485)
                ·
                  refine ⟨452340398858449632348679, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9649928508980258823438485 452340398858449632348679)
                  ·
                    rfl

theorem cell22_3964184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 2, 1, 6].length) (baseStart_3964184 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3964184 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3964184 prefixEnd_3964184 := by exact prefixLift 3964184
  have htrace : WordTrace (prefixWord ++ tailWord_3964184) baseStart_3964184 baseEnd_3964184 := by
    simpa [prefixWord, tailWord_3964184, baseEnd_3964184] using wordTrace_append hprefix tailTrace_3964184
  have hstable : (prefixWord ++ tailWord_3964184).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3964184).length < 2 ^ (prefixWord ++ tailWord_3964184).sum := by decide
  have hdescent : baseEnd_3964184 < baseStart_3964184 := by decide
  rcases family_descends (prefixWord ++ tailWord_3964184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3964190 : List Nat := [4, 3, 2, 1, 2, 1, 3, 1, 5]
def baseStart_3964190 : Nat := 118140960795 + 3964190 * 2 ^ 59
def prefixEnd_3964190 : Nat := 4983230072969 + 3 ^ 40 * 3964190 * 2
def baseEnd_3964190 : Nat := 452341083499322293798673

theorem tailTrace_3964190 : CollatzResearch.WordTrace tailWord_3964190 prefixEnd_3964190 452341083499322293798673 := by
  unfold tailWord_3964190
  simp only [CollatzResearch.WordTrace]
  refine ⟨18073235938553016824502253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 96390591672282756397345349 18073235938553016824502253)
  ·
    refine ⟨6777463476957381309188345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18073235938553016824502253 6777463476957381309188345)
    ·
      refine ⟨5083097607718035981891259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6777463476957381309188345 5083097607718035981891259)
      ·
        refine ⟨7624646411577053972836889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5083097607718035981891259 7624646411577053972836889)
        ·
          refine ⟨5718484808682790479627667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7624646411577053972836889 5718484808682790479627667)
          ·
            refine ⟨8577727213024185719441501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5718484808682790479627667 8577727213024185719441501)
            ·
              refine ⟨3216647704884069644790563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8577727213024185719441501 3216647704884069644790563)
              ·
                refine ⟨4824971557326104467185845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3216647704884069644790563 4824971557326104467185845)
                ·
                  refine ⟨452341083499322293798673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4824971557326104467185845 452341083499322293798673)
                  ·
                    rfl

theorem cell22_3964190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 3, 1, 5].length) (baseStart_3964190 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3964190 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3964190 prefixEnd_3964190 := by exact prefixLift 3964190
  have htrace : WordTrace (prefixWord ++ tailWord_3964190) baseStart_3964190 baseEnd_3964190 := by
    simpa [prefixWord, tailWord_3964190, baseEnd_3964190] using wordTrace_append hprefix tailTrace_3964190
  have hstable : (prefixWord ++ tailWord_3964190).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3964190).length < 2 ^ (prefixWord ++ tailWord_3964190).sum := by decide
  have hdescent : baseEnd_3964190 < baseStart_3964190 := by decide
  rcases family_descends (prefixWord ++ tailWord_3964190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3964291 : List Nat := [1, 1, 1, 3, 5, 2, 2, 2, 5]
def baseStart_3964291 : Nat := 118140960795 + 3964291 * 2 ^ 59
def prefixEnd_3964291 : Nat := 4983230072969 + 3 ^ 40 * 3964291 * 2
def baseEnd_3964291 : Nat := 452352608287345428206903

theorem tailTrace_3964291 : CollatzResearch.WordTrace tailWord_3964291 prefixEnd_3964291 452352608287345428206903 := by
  unfold tailWord_3964291
  simp only [CollatzResearch.WordTrace]
  refine ⟨144589571281058228845444727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96393047520705485896963151 144589571281058228845444727)
  ·
    refine ⟨216884356921587343268167091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144589571281058228845444727 216884356921587343268167091)
    ·
      refine ⟨325326535382381014902250637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216884356921587343268167091 325326535382381014902250637)
      ·
        refine ⟨121997450768392880588343989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 325326535382381014902250637 121997450768392880588343989)
        ·
          refine ⟨11437261009536832555157249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 121997450768392880588343989 11437261009536832555157249)
          ·
            refine ⟨8577945757152624416367937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11437261009536832555157249 8577945757152624416367937)
            ·
              refine ⟨6433459317864468312275953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8577945757152624416367937 6433459317864468312275953)
              ·
                refine ⟨4825094488398351234206965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6433459317864468312275953 4825094488398351234206965)
                ·
                  refine ⟨452352608287345428206903, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4825094488398351234206965 452352608287345428206903)
                  ·
                    rfl

theorem cell22_3964291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 2, 2, 5].length) (baseStart_3964291 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3964291 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3964291 prefixEnd_3964291 := by exact prefixLift 3964291
  have htrace : WordTrace (prefixWord ++ tailWord_3964291) baseStart_3964291 baseEnd_3964291 := by
    simpa [prefixWord, tailWord_3964291, baseEnd_3964291] using wordTrace_append hprefix tailTrace_3964291
  have hstable : (prefixWord ++ tailWord_3964291).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3964291).length < 2 ^ (prefixWord ++ tailWord_3964291).sum := by decide
  have hdescent : baseEnd_3964291 < baseStart_3964291 := by decide
  rcases family_descends (prefixWord ++ tailWord_3964291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3964295 : List Nat := [1, 1, 4, 2, 2, 2, 4, 2, 1, 3]
def baseStart_3964295 : Nat := 118140960795 + 3964295 * 2 ^ 59
def prefixEnd_3964295 : Nat := 4983230072969 + 3 ^ 40 * 3964295 * 2
def baseEnd_3964295 : Nat := 1357059194143781607520697

theorem tailTrace_3964295 : CollatzResearch.WordTrace tailWord_3964295 prefixEnd_3964295 1357059194143781607520697 := by
  unfold tailWord_3964295
  simp only [CollatzResearch.WordTrace]
  refine ⟨144589717173043737528590339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96393144782029158352393559 144589717173043737528590339)
  ·
    refine ⟨216884575759565606292885509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144589717173043737528590339 216884575759565606292885509)
    ·
      refine ⟨40665857954918551179916033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 216884575759565606292885509 40665857954918551179916033)
      ·
        refine ⟨30499393466188913384937025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40665857954918551179916033 30499393466188913384937025)
        ·
          refine ⟨22874545099641685038702769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30499393466188913384937025 22874545099641685038702769)
          ·
            refine ⟨17155908824731263779027077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22874545099641685038702769 17155908824731263779027077)
            ·
              refine ⟨3216732904637111958567577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17155908824731263779027077 3216732904637111958567577)
              ·
                refine ⟨2412549678477833968925683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3216732904637111958567577 2412549678477833968925683)
                ·
                  refine ⟨3618824517716750953388525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2412549678477833968925683 3618824517716750953388525)
                  ·
                    refine ⟨1357059194143781607520697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3618824517716750953388525 1357059194143781607520697)
                    ·
                      rfl

theorem cell22_3964295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 4, 2, 1, 3].length) (baseStart_3964295 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3964295 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3964295 prefixEnd_3964295 := by exact prefixLift 3964295
  have htrace : WordTrace (prefixWord ++ tailWord_3964295) baseStart_3964295 baseEnd_3964295 := by
    simpa [prefixWord, tailWord_3964295, baseEnd_3964295] using wordTrace_append hprefix tailTrace_3964295
  have hstable : (prefixWord ++ tailWord_3964295).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3964295).length < 2 ^ (prefixWord ++ tailWord_3964295).sum := by decide
  have hdescent : baseEnd_3964295 < baseStart_3964295 := by decide
  rcases family_descends (prefixWord ++ tailWord_3964295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3964319 : List Nat := [1, 1, 2, 5, 1, 2, 1, 1, 8]
def baseStart_3964319 : Nat := 118140960795 + 3964319 * 2 ^ 59
def prefixEnd_3964319 : Nat := 4983230072969 + 3 ^ 40 * 3964319 * 2
def baseEnd_3964319 : Nat := 452355803278084514973541

theorem tailTrace_3964319 : CollatzResearch.WordTrace tailWord_3964319 prefixEnd_3964319 452355803278084514973541 := by
  unfold tailWord_3964319
  simp only [CollatzResearch.WordTrace]
  refine ⟨144590592524956789627464011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96393728349971193084976007 144590592524956789627464011)
  ·
    refine ⟨216885888787435184441196017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144590592524956789627464011 216885888787435184441196017)
    ·
      refine ⟨162664416590576388330897013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 216885888787435184441196017 162664416590576388330897013)
      ·
        refine ⟨15249789055366536406021595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 162664416590576388330897013 15249789055366536406021595)
        ·
          refine ⟨22874683583049804609032393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15249789055366536406021595 22874683583049804609032393)
          ·
            refine ⟨17156012687287353456774295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22874683583049804609032393 17156012687287353456774295)
            ·
              refine ⟨25734019030931030185161443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17156012687287353456774295 25734019030931030185161443)
              ·
                refine ⟨38601028546396545277742165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25734019030931030185161443 38601028546396545277742165)
                ·
                  refine ⟨452355803278084514973541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 38601028546396545277742165 452355803278084514973541)
                  ·
                    rfl

theorem cell22_3964319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 1, 1, 8].length) (baseStart_3964319 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3964319 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3964319 prefixEnd_3964319 := by exact prefixLift 3964319
  have htrace : WordTrace (prefixWord ++ tailWord_3964319) baseStart_3964319 baseEnd_3964319 := by
    simpa [prefixWord, tailWord_3964319, baseEnd_3964319] using wordTrace_append hprefix tailTrace_3964319
  have hstable : (prefixWord ++ tailWord_3964319).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3964319).length < 2 ^ (prefixWord ++ tailWord_3964319).sum := by decide
  have hdescent : baseEnd_3964319 < baseStart_3964319 := by decide
  rcases family_descends (prefixWord ++ tailWord_3964319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3964381 : List Nat := [1, 4, 3, 1, 1, 3, 1, 8]
def baseStart_3964381 : Nat := 118140960795 + 3964381 * 2 ^ 59
def prefixEnd_3964381 : Nat := 4983230072969 + 3 ^ 40 * 3964381 * 2
def baseEnd_3964381 : Nat := 150787625966811783318937

theorem tailTrace_3964381 : CollatzResearch.WordTrace tailWord_3964381 prefixEnd_3964381 150787625966811783318937 := by
  unfold tailWord_3964381
  simp only [CollatzResearch.WordTrace]
  refine ⟨144592853850732174216220997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96395235900488116144147331 144592853850732174216220997)
  ·
    refine ⟨27111160097012282665541437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 144592853850732174216220997 27111160097012282665541437)
    ·
      refine ⟨10166685036379605999578039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27111160097012282665541437 10166685036379605999578039)
      ·
        refine ⟨15250027554569408999367059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10166685036379605999578039 15250027554569408999367059)
        ·
          refine ⟨22875041331854113499050589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15250027554569408999367059 22875041331854113499050589)
          ·
            refine ⟨8578140499445292562143971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22875041331854113499050589 8578140499445292562143971)
            ·
              refine ⟨12867210749167938843215957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8578140499445292562143971 12867210749167938843215957)
              ·
                refine ⟨150787625966811783318937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12867210749167938843215957 150787625966811783318937)
                ·
                  rfl

theorem cell22_3964381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 1, 8].length) (baseStart_3964381 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3964381 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3964381 prefixEnd_3964381 := by exact prefixLift 3964381
  have htrace : WordTrace (prefixWord ++ tailWord_3964381) baseStart_3964381 baseEnd_3964381 := by
    simpa [prefixWord, tailWord_3964381, baseEnd_3964381] using wordTrace_append hprefix tailTrace_3964381
  have hstable : (prefixWord ++ tailWord_3964381).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3964381).length < 2 ^ (prefixWord ++ tailWord_3964381).sum := by decide
  have hdescent : baseEnd_3964381 < baseStart_3964381 := by decide
  rcases family_descends (prefixWord ++ tailWord_3964381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3964413 : List Nat := [1, 4, 1, 1, 1, 4, 3, 1, 3, 3]
def baseStart_3964413 : Nat := 118140960795 + 3964413 * 2 ^ 59
def prefixEnd_3964413 : Nat := 4983230072969 + 3 ^ 40 * 3964413 * 2
def baseEnd_3964413 : Nat := 1357099587955268633070335

theorem tailTrace_3964413 : CollatzResearch.WordTrace tailWord_3964413 prefixEnd_3964413 1357099587955268633070335 := by
  unfold tailWord_3964413
  simp only [CollatzResearch.WordTrace]
  refine ⟨144594020986616243681385893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96396013991077495787590595 144594020986616243681385893)
  ·
    refine ⟨27111378934990545690259855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 144594020986616243681385893 27111378934990545690259855)
    ·
      refine ⟨40667068402485818535389783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27111378934990545690259855 40667068402485818535389783)
      ·
        refine ⟨61000602603728727803084675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40667068402485818535389783 61000602603728727803084675)
        ·
          refine ⟨91500903905593091704627013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61000602603728727803084675 91500903905593091704627013)
          ·
            refine ⟨17156419482298704694617565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 91500903905593091704627013 17156419482298704694617565)
            ·
              refine ⟨6433657305862014260481587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17156419482298704694617565 6433657305862014260481587)
              ·
                refine ⟨9650485958793021390722381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6433657305862014260481587 9650485958793021390722381)
                ·
                  refine ⟨3618932234547383021520893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9650485958793021390722381 3618932234547383021520893)
                  ·
                    refine ⟨1357099587955268633070335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3618932234547383021520893 1357099587955268633070335)
                    ·
                      rfl

theorem cell22_3964413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 3, 1, 3, 3].length) (baseStart_3964413 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3964413 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3964413 prefixEnd_3964413 := by exact prefixLift 3964413
  have htrace : WordTrace (prefixWord ++ tailWord_3964413) baseStart_3964413 baseEnd_3964413 := by
    simpa [prefixWord, tailWord_3964413, baseEnd_3964413] using wordTrace_append hprefix tailTrace_3964413
  have hstable : (prefixWord ++ tailWord_3964413).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3964413).length < 2 ^ (prefixWord ++ tailWord_3964413).sum := by decide
  have hdescent : baseEnd_3964413 < baseStart_3964413 := by decide
  rcases family_descends (prefixWord ++ tailWord_3964413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3964516 : List Nat := [2, 3, 1, 1, 2, 4, 9]
def baseStart_3964516 : Nat := 118140960795 + 3964516 * 2 ^ 59
def prefixEnd_3964516 : Nat := 4983230072969 + 3 ^ 40 * 3964516 * 2
def baseEnd_3964516 : Nat := 50264253591118914731297

theorem tailTrace_3964516 : CollatzResearch.WordTrace tailWord_3964516 prefixEnd_3964516 50264253591118914731297 := by
  unfold tailWord_3964516
  simp only [CollatzResearch.WordTrace]
  refine ⟨72298888852621546136192701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96398518470162061514923601 72298888852621546136192701)
  ·
    refine ⟨27112083319733079801072263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72298888852621546136192701 27112083319733079801072263)
    ·
      refine ⟨40668124979599619701608395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27112083319733079801072263 40668124979599619701608395)
      ·
        refine ⟨61002187469399429552412593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40668124979599619701608395 61002187469399429552412593)
        ·
          refine ⟨45751640602049572164309445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61002187469399429552412593 45751640602049572164309445)
          ·
            refine ⟨8578432612884294780808021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45751640602049572164309445 8578432612884294780808021)
            ·
              refine ⟨50264253591118914731297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8578432612884294780808021 50264253591118914731297)
              ·
                rfl

theorem cell22_3964516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 9].length) (baseStart_3964516 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3964516 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3964516 prefixEnd_3964516 := by exact prefixLift 3964516
  have htrace : WordTrace (prefixWord ++ tailWord_3964516) baseStart_3964516 baseEnd_3964516 := by
    simpa [prefixWord, tailWord_3964516, baseEnd_3964516] using wordTrace_append hprefix tailTrace_3964516
  have hstable : (prefixWord ++ tailWord_3964516).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3964516).length < 2 ^ (prefixWord ++ tailWord_3964516).sum := by decide
  have hdescent : baseEnd_3964516 < baseStart_3964516 := by decide
  rcases family_descends (prefixWord ++ tailWord_3964516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3964520 : List Nat := [2, 1, 4, 3, 1, 2, 1, 1, 4, 3]
def baseStart_3964520 : Nat := 118140960795 + 3964520 * 2 ^ 59
def prefixEnd_3964520 : Nat := 4983230072969 + 3 ^ 40 * 3964520 * 2
def baseEnd_3964520 : Nat := 1357136216241956020645007

theorem tailTrace_3964520 : CollatzResearch.WordTrace tailWord_3964520 prefixEnd_3964520 1357136216241956020645007 := by
  unfold tailWord_3964520
  simp only [CollatzResearch.WordTrace]
  refine ⟨72298961798614300477765507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96398615731485733970354009 72298961798614300477765507)
  ·
    refine ⟨108448442697921450716648261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72298961798614300477765507 108448442697921450716648261)
    ·
      refine ⟨20334083005860272009371549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 108448442697921450716648261 20334083005860272009371549)
      ·
        refine ⟨7625281127197602003514331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20334083005860272009371549 7625281127197602003514331)
        ·
          refine ⟨11437921690796403005271497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7625281127197602003514331 11437921690796403005271497)
          ·
            refine ⟨8578441268097302253953623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11437921690796403005271497 8578441268097302253953623)
            ·
              refine ⟨12867661902145953380930435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8578441268097302253953623 12867661902145953380930435)
              ·
                refine ⟨19301492853218930071395653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12867661902145953380930435 19301492853218930071395653)
                ·
                  refine ⟨3619029909978549388386685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19301492853218930071395653 3619029909978549388386685)
                  ·
                    refine ⟨1357136216241956020645007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3619029909978549388386685 1357136216241956020645007)
                    ·
                      rfl

theorem cell22_3964520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 1, 1, 4, 3].length) (baseStart_3964520 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3964520 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3964520 prefixEnd_3964520 := by exact prefixLift 3964520
  have htrace : WordTrace (prefixWord ++ tailWord_3964520) baseStart_3964520 baseEnd_3964520 := by
    simpa [prefixWord, tailWord_3964520, baseEnd_3964520] using wordTrace_append hprefix tailTrace_3964520
  have hstable : (prefixWord ++ tailWord_3964520).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3964520).length < 2 ^ (prefixWord ++ tailWord_3964520).sum := by decide
  have hdescent : baseEnd_3964520 < baseStart_3964520 := by decide
  rcases family_descends (prefixWord ++ tailWord_3964520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3964608 : List Nat := [2, 1, 1, 2, 4, 1, 3, 1, 3, 4]
def baseStart_3964608 : Nat := 118140960795 + 3964608 * 2 ^ 59
def prefixEnd_3964608 : Nat := 4983230072969 + 3 ^ 40 * 3964608 * 2
def baseEnd_3964608 : Nat := 1357166340440353124444737

theorem tailTrace_3964608 : CollatzResearch.WordTrace tailWord_3964608 prefixEnd_3964608 1357166340440353124444737 := by
  unfold tailWord_3964608
  simp only [CollatzResearch.WordTrace]
  refine ⟨72300566610454895992367239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96400755480606527989822985 72300566610454895992367239)
  ·
    refine ⟨108450849915682343988550859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72300566610454895992367239 108450849915682343988550859)
    ·
      refine ⟨162676274873523515982826289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108450849915682343988550859 162676274873523515982826289)
      ·
        refine ⟨122007206155142636987119717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 162676274873523515982826289 122007206155142636987119717)
        ·
          refine ⟨22876351154089244435084947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 122007206155142636987119717 22876351154089244435084947)
          ·
            refine ⟨34314526731133866652627421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22876351154089244435084947 34314526731133866652627421)
            ·
              refine ⟨12867947524175199994735283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34314526731133866652627421 12867947524175199994735283)
              ·
                refine ⟨19301921286262799992102925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12867947524175199994735283 19301921286262799992102925)
                ·
                  refine ⟨7238220482348549997038597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19301921286262799992102925 7238220482348549997038597)
                  ·
                    refine ⟨1357166340440353124444737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7238220482348549997038597 1357166340440353124444737)
                    ·
                      rfl

theorem cell22_3964608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 3, 1, 3, 4].length) (baseStart_3964608 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3964608 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3964608 prefixEnd_3964608 := by exact prefixLift 3964608
  have htrace : WordTrace (prefixWord ++ tailWord_3964608) baseStart_3964608 baseEnd_3964608 := by
    simpa [prefixWord, tailWord_3964608, baseEnd_3964608] using wordTrace_append hprefix tailTrace_3964608
  have hstable : (prefixWord ++ tailWord_3964608).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3964608).length < 2 ^ (prefixWord ++ tailWord_3964608).sum := by decide
  have hdescent : baseEnd_3964608 < baseStart_3964608 := by decide
  rcases family_descends (prefixWord ++ tailWord_3964608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3964655 : List Nat := [1, 1, 2, 1, 5, 1, 1, 5, 2, 3]
def baseStart_3964655 : Nat := 118140960795 + 3964655 * 2 ^ 59
def prefixEnd_3964655 : Nat := 4983230072969 + 3 ^ 40 * 3964655 * 2
def baseEnd_3964655 : Nat := 1357182429500860668519593

theorem tailTrace_3964655 : CollatzResearch.WordTrace tailWord_3964655 prefixEnd_3964655 1357182429500860668519593 := by
  unfold tailWord_3964655
  simp only [CollatzResearch.WordTrace]
  refine ⟨144602847451739519011695419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96401898301159679341130279 144602847451739519011695419)
  ·
    refine ⟨216904271177609278517543129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144602847451739519011695419 216904271177609278517543129)
    ·
      refine ⟨162678203383206958888157347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 216904271177609278517543129 162678203383206958888157347)
      ·
        refine ⟨244017305074810438332236021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162678203383206958888157347 244017305074810438332236021)
        ·
          refine ⟨22876622350763478593647127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 244017305074810438332236021 22876622350763478593647127)
          ·
            refine ⟨34314933526145217890470691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22876622350763478593647127 34314933526145217890470691)
            ·
              refine ⟨51472400289217826835706037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34314933526145217890470691 51472400289217826835706037)
              ·
                refine ⟨4825537527114171265847441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 51472400289217826835706037 4825537527114171265847441)
                ·
                  refine ⟨3619153145335628449385581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4825537527114171265847441 3619153145335628449385581)
                  ·
                    refine ⟨1357182429500860668519593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3619153145335628449385581 1357182429500860668519593)
                    ·
                      rfl

theorem cell22_3964655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 5, 2, 3].length) (baseStart_3964655 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3964655 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3964655 prefixEnd_3964655 := by exact prefixLift 3964655
  have htrace : WordTrace (prefixWord ++ tailWord_3964655) baseStart_3964655 baseEnd_3964655 := by
    simpa [prefixWord, tailWord_3964655, baseEnd_3964655] using wordTrace_append hprefix tailTrace_3964655
  have hstable : (prefixWord ++ tailWord_3964655).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3964655).length < 2 ^ (prefixWord ++ tailWord_3964655).sum := by decide
  have hdescent : baseEnd_3964655 < baseStart_3964655 := by decide
  rcases family_descends (prefixWord ++ tailWord_3964655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3964803 : List Nat := [1, 1, 1, 3, 4, 12]
def baseStart_3964803 : Nat := 118140960795 + 3964803 * 2 ^ 59
def prefixEnd_3964803 : Nat := 4983230072969 + 3 ^ 40 * 3964803 * 2
def baseEnd_3964803 : Nat := 16755964110190587849619

theorem tailTrace_3964803 : CollatzResearch.WordTrace tailWord_3964803 prefixEnd_3964803 16755964110190587849619 := by
  unfold tailWord_3964803
  simp only [CollatzResearch.WordTrace]
  refine ⟨144608245455203340288083063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96405496970135560192055375 144608245455203340288083063)
  ·
    refine ⟨216912368182805010432124595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144608245455203340288083063 216912368182805010432124595)
    ·
      refine ⟨325368552274207515648186893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216912368182805010432124595 325368552274207515648186893)
      ·
        refine ⟨122013207102827818368070085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 325368552274207515648186893 122013207102827818368070085)
        ·
          refine ⟨22877476331780215944013141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 122013207102827818368070085 22877476331780215944013141)
          ·
            refine ⟨16755964110190587849619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 22877476331780215944013141 16755964110190587849619)
            ·
              rfl

theorem cell22_3964803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 12].length) (baseStart_3964803 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3964803 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3964803 prefixEnd_3964803 := by exact prefixLift 3964803
  have htrace : WordTrace (prefixWord ++ tailWord_3964803) baseStart_3964803 baseEnd_3964803 := by
    simpa [prefixWord, tailWord_3964803, baseEnd_3964803] using wordTrace_append hprefix tailTrace_3964803
  have hstable : (prefixWord ++ tailWord_3964803).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3964803).length < 2 ^ (prefixWord ++ tailWord_3964803).sum := by decide
  have hdescent : baseEnd_3964803 < baseStart_3964803 := by decide
  rcases family_descends (prefixWord ++ tailWord_3964803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3964805 : List Nat := [1, 3, 1, 1, 3, 2, 1, 4, 2, 4]
def baseStart_3964805 : Nat := 118140960795 + 3964805 * 2 ^ 59
def prefixEnd_3964805 : Nat := 4983230072969 + 3 ^ 40 * 3964805 * 2
def baseEnd_3964805 : Nat := 1357233777566310277269133

theorem tailTrace_3964805 : CollatzResearch.WordTrace tailWord_3964805 prefixEnd_3964805 1357233777566310277269133 := by
  unfold tailWord_3964805
  simp only [CollatzResearch.WordTrace]
  refine ⟨144608318401196094629655869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96405545600797396419770579 144608318401196094629655869)
  ·
    refine ⟨54228119400448535486120951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 144608318401196094629655869 54228119400448535486120951)
    ·
      refine ⟨81342179100672803229181427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54228119400448535486120951 81342179100672803229181427)
      ·
        refine ⟨122013268651009204843772141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81342179100672803229181427 122013268651009204843772141)
        ·
          refine ⟨45754975744128451816414553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 122013268651009204843772141 45754975744128451816414553)
          ·
            refine ⟨34316231808096338862310915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45754975744128451816414553 34316231808096338862310915)
            ·
              refine ⟨51474347712144508293466373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34316231808096338862310915 51474347712144508293466373)
              ·
                refine ⟨9651440196027095305024945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 51474347712144508293466373 9651440196027095305024945)
                ·
                  refine ⟨7238580147020321478768709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9651440196027095305024945 7238580147020321478768709)
                  ·
                    refine ⟨1357233777566310277269133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7238580147020321478768709 1357233777566310277269133)
                    ·
                      rfl

theorem cell22_3964805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 4, 2, 4].length) (baseStart_3964805 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3964805 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3964805 prefixEnd_3964805 := by exact prefixLift 3964805
  have htrace : WordTrace (prefixWord ++ tailWord_3964805) baseStart_3964805 baseEnd_3964805 := by
    simpa [prefixWord, tailWord_3964805, baseEnd_3964805] using wordTrace_append hprefix tailTrace_3964805
  have hstable : (prefixWord ++ tailWord_3964805).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3964805).length < 2 ^ (prefixWord ++ tailWord_3964805).sum := by decide
  have hdescent : baseEnd_3964805 < baseStart_3964805 := by decide
  rcases family_descends (prefixWord ++ tailWord_3964805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3964824 : List Nat := [2, 1, 2, 6, 1, 1, 2, 1, 1, 5]
def baseStart_3964824 : Nat := 118140960795 + 3964824 * 2 ^ 59
def prefixEnd_3964824 : Nat := 4983230072969 + 3 ^ 40 * 3964824 * 2
def baseEnd_3964824 : Nat := 1357240281654600561044075

theorem tailTrace_3964824 : CollatzResearch.WordTrace tailWord_3964824 prefixEnd_3964824 1357240281654600561044075 := by
  unfold tailWord_3964824
  simp only [CollatzResearch.WordTrace]
  refine ⟨72304505694063630437298763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96406007592084840583065017 72304505694063630437298763)
  ·
    refine ⟨108456758541095445655948145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72304505694063630437298763 108456758541095445655948145)
    ·
      refine ⟨81342568905821584241961109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108456758541095445655948145 81342568905821584241961109)
      ·
        refine ⟨3812932917460386761341927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 81342568905821584241961109 3812932917460386761341927)
        ·
          refine ⟨5719399376190580142012891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3812932917460386761341927 5719399376190580142012891)
          ·
            refine ⟨8579099064285870213019337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5719399376190580142012891 8579099064285870213019337)
            ·
              refine ⟨6434324298214402659764503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8579099064285870213019337 6434324298214402659764503)
              ·
                refine ⟨9651486447321603989646755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6434324298214402659764503 9651486447321603989646755)
                ·
                  refine ⟨14477229670982405984470133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9651486447321603989646755 14477229670982405984470133)
                  ·
                    refine ⟨1357240281654600561044075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14477229670982405984470133 1357240281654600561044075)
                    ·
                      rfl

theorem cell22_3964824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 2, 1, 1, 5].length) (baseStart_3964824 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3964824 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3964824 prefixEnd_3964824 := by exact prefixLift 3964824
  have htrace : WordTrace (prefixWord ++ tailWord_3964824) baseStart_3964824 baseEnd_3964824 := by
    simpa [prefixWord, tailWord_3964824, baseEnd_3964824] using wordTrace_append hprefix tailTrace_3964824
  have hstable : (prefixWord ++ tailWord_3964824).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3964824).length < 2 ^ (prefixWord ++ tailWord_3964824).sum := by decide
  have hdescent : baseEnd_3964824 < baseStart_3964824 := by decide
  rcases family_descends (prefixWord ++ tailWord_3964824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3964839 : List Nat := [1, 1, 6, 1, 2, 3, 1, 1, 2, 4]
def baseStart_3964839 : Nat := 118140960795 + 3964839 * 2 ^ 59
def prefixEnd_3964839 : Nat := 4983230072969 + 3 ^ 40 * 3964839 * 2
def baseEnd_3964839 : Nat := 1357245416461145521919029

theorem tailTrace_3964839 : CollatzResearch.WordTrace tailWord_3964839 prefixEnd_3964839 1357245416461145521919029 := by
  unfold tailWord_3964839
  simp only [CollatzResearch.WordTrace]
  refine ⟨144609558483072918436393571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96406372322048612290929047 144609558483072918436393571)
  ·
    refine ⟨216914337724609377654590357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144609558483072918436393571 216914337724609377654590357)
    ·
      refine ⟨10167859580841064577558923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 216914337724609377654590357 10167859580841064577558923)
      ·
        refine ⟨15251789371261596866338385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10167859580841064577558923 15251789371261596866338385)
        ·
          refine ⟨11438842028446197649753789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15251789371261596866338385 11438842028446197649753789)
          ·
            refine ⟨4289565760667324118657671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11438842028446197649753789 4289565760667324118657671)
            ·
              refine ⟨6434348641000986177986507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4289565760667324118657671 6434348641000986177986507)
              ·
                refine ⟨9651522961501479266979761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6434348641000986177986507 9651522961501479266979761)
                ·
                  refine ⟨7238642221126109450234821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9651522961501479266979761 7238642221126109450234821)
                  ·
                    refine ⟨1357245416461145521919029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7238642221126109450234821 1357245416461145521919029)
                    ·
                      rfl

theorem cell22_3964839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 3, 1, 1, 2, 4].length) (baseStart_3964839 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3964839 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3964839 prefixEnd_3964839 := by exact prefixLift 3964839
  have htrace : WordTrace (prefixWord ++ tailWord_3964839) baseStart_3964839 baseEnd_3964839 := by
    simpa [prefixWord, tailWord_3964839, baseEnd_3964839] using wordTrace_append hprefix tailTrace_3964839
  have hstable : (prefixWord ++ tailWord_3964839).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3964839).length < 2 ^ (prefixWord ++ tailWord_3964839).sum := by decide
  have hdescent : baseEnd_3964839 < baseStart_3964839 := by decide
  rcases family_descends (prefixWord ++ tailWord_3964839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3964880 : List Nat := [2, 1, 1, 1, 1, 2, 6, 1, 2, 5]
def baseStart_3964880 : Nat := 118140960795 + 3964880 * 2 ^ 59
def prefixEnd_3964880 : Nat := 4983230072969 + 3 ^ 40 * 3964880 * 2
def baseEnd_3964880 : Nat := 1357259451599035081643903

theorem tailTrace_3964880 : CollatzResearch.WordTrace tailWord_3964880 prefixEnd_3964880 1357259451599035081643903 := by
  unfold tailWord_3964880
  simp only [CollatzResearch.WordTrace]
  refine ⟨72305526937962191219318047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96407369250616254959090729 72305526937962191219318047)
  ·
    refine ⟨108458290406943286828977071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72305526937962191219318047 108458290406943286828977071)
    ·
      refine ⟨162687435610414930243465607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108458290406943286828977071 162687435610414930243465607)
      ·
        refine ⟨244031153415622395365198411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162687435610414930243465607 244031153415622395365198411)
        ·
          refine ⟨366046730123433593047797617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 244031153415622395365198411 366046730123433593047797617)
          ·
            refine ⟨274535047592575194785848213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 366046730123433593047797617 274535047592575194785848213)
            ·
              refine ⟨12868830355901962255586635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 274535047592575194785848213 12868830355901962255586635)
              ·
                refine ⟨19303245533852943383379953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12868830355901962255586635 19303245533852943383379953)
                ·
                  refine ⟨14477434150389707537534965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19303245533852943383379953 14477434150389707537534965)
                  ·
                    refine ⟨1357259451599035081643903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14477434150389707537534965 1357259451599035081643903)
                    ·
                      rfl

theorem cell22_3964880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 6, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 6, 1, 2, 5].length) (baseStart_3964880 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3964880 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3964880 prefixEnd_3964880 := by exact prefixLift 3964880
  have htrace : WordTrace (prefixWord ++ tailWord_3964880) baseStart_3964880 baseEnd_3964880 := by
    simpa [prefixWord, tailWord_3964880, baseEnd_3964880] using wordTrace_append hprefix tailTrace_3964880
  have hstable : (prefixWord ++ tailWord_3964880).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3964880).length < 2 ^ (prefixWord ++ tailWord_3964880).sum := by decide
  have hdescent : baseEnd_3964880 < baseStart_3964880 := by decide
  rcases family_descends (prefixWord ++ tailWord_3964880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3964903 : List Nat := [1, 1, 5, 2, 3, 2, 1, 3, 1, 3]
def baseStart_3964903 : Nat := 118140960795 + 3964903 * 2 ^ 59
def prefixEnd_3964903 : Nat := 4983230072969 + 3 ^ 40 * 3964903 * 2
def baseEnd_3964903 : Nat := 1357267324969070688318833

theorem tailTrace_3964903 : CollatzResearch.WordTrace tailWord_3964903 prefixEnd_3964903 1357267324969070688318833 := by
  unfold tailWord_3964903
  simp only [CollatzResearch.WordTrace]
  refine ⟨144611892754841057366723363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96407928503227371577815575 144611892754841057366723363)
  ·
    refine ⟨216917839132261586050085045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144611892754841057366723363 216917839132261586050085045)
    ·
      refine ⟨20336047418649523692195473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 216917839132261586050085045 20336047418649523692195473)
      ·
        refine ⟨15252035563987142769146605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20336047418649523692195473 15252035563987142769146605)
        ·
          refine ⟨5719513336495178538429977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15252035563987142769146605 5719513336495178538429977)
          ·
            refine ⟨4289635002371383903822483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5719513336495178538429977 4289635002371383903822483)
            ·
              refine ⟨6434452503557075855733725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4289635002371383903822483 6434452503557075855733725)
              ·
                refine ⟨2412919688833903445900147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6434452503557075855733725 2412919688833903445900147)
                ·
                  refine ⟨3619379533250855168850221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2412919688833903445900147 3619379533250855168850221)
                  ·
                    refine ⟨1357267324969070688318833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3619379533250855168850221 1357267324969070688318833)
                    ·
                      rfl

theorem cell22_3964903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 2, 1, 3, 1, 3].length) (baseStart_3964903 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3964903 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3964903 prefixEnd_3964903 := by exact prefixLift 3964903
  have htrace : WordTrace (prefixWord ++ tailWord_3964903) baseStart_3964903 baseEnd_3964903 := by
    simpa [prefixWord, tailWord_3964903, baseEnd_3964903] using wordTrace_append hprefix tailTrace_3964903
  have hstable : (prefixWord ++ tailWord_3964903).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3964903).length < 2 ^ (prefixWord ++ tailWord_3964903).sum := by decide
  have hdescent : baseEnd_3964903 < baseStart_3964903 := by decide
  rcases family_descends (prefixWord ++ tailWord_3964903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3964912 : List Nat := [2, 1, 1, 1, 3, 2, 4, 3, 1, 4]
def baseStart_3964912 : Nat := 118140960795 + 3964912 * 2 ^ 59
def prefixEnd_3964912 : Nat := 4983230072969 + 3 ^ 40 * 3964912 * 2
def baseEnd_3964912 : Nat := 1357270405852997664843805

theorem tailTrace_3964912 : CollatzResearch.WordTrace tailWord_3964912 prefixEnd_3964912 1357270405852997664843805 := by
  unfold tailWord_3964912
  simp only [CollatzResearch.WordTrace]
  refine ⟨72306110505904225951900495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96408147341205634602533993 72306110505904225951900495)
  ·
    refine ⟨108459165758856338927850743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72306110505904225951900495 108459165758856338927850743)
    ·
      refine ⟨162688748638284508391776115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108459165758856338927850743 162688748638284508391776115)
      ·
        refine ⟨244033122957426762587664173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162688748638284508391776115 244033122957426762587664173)
        ·
          refine ⟨91512421109035035970374065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 244033122957426762587664173 91512421109035035970374065)
          ·
            refine ⟨68634315831776276977780549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91512421109035035970374065 68634315831776276977780549)
            ·
              refine ⟨12868934218458051933333853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 68634315831776276977780549 12868934218458051933333853)
              ·
                refine ⟨4825850331921769475000195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12868934218458051933333853 4825850331921769475000195)
                ·
                  refine ⟨7238775497882654212500293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4825850331921769475000195 7238775497882654212500293)
                  ·
                    refine ⟨1357270405852997664843805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7238775497882654212500293 1357270405852997664843805)
                    ·
                      rfl

theorem cell22_3964912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 4, 3, 1, 4].length) (baseStart_3964912 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3964912 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3964912 prefixEnd_3964912 := by exact prefixLift 3964912
  have htrace : WordTrace (prefixWord ++ tailWord_3964912) baseStart_3964912 baseEnd_3964912 := by
    simpa [prefixWord, tailWord_3964912, baseEnd_3964912] using wordTrace_append hprefix tailTrace_3964912
  have hstable : (prefixWord ++ tailWord_3964912).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3964912).length < 2 ^ (prefixWord ++ tailWord_3964912).sum := by decide
  have hdescent : baseEnd_3964912 < baseStart_3964912 := by decide
  rcases family_descends (prefixWord ++ tailWord_3964912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3964927 : List Nat := [1, 1, 2, 2, 1, 2, 1, 8, 4]
def baseStart_3964927 : Nat := 118140960795 + 3964927 * 2 ^ 59
def prefixEnd_3964927 : Nat := 4983230072969 + 3 ^ 40 * 3964927 * 2
def baseEnd_3964927 : Nat := 452425180219847541906253

theorem tailTrace_3964927 : CollatzResearch.WordTrace tailWord_3964927 prefixEnd_3964927 452425180219847541906253 := by
  unfold tailWord_3964927
  simp only [CollatzResearch.WordTrace]
  refine ⟨144612768106754109465597035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96408512071169406310398023 144612768106754109465597035)
  ·
    refine ⟨216919152160131164198395553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144612768106754109465597035 216919152160131164198395553)
    ·
      refine ⟨162689364120098373148796665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 216919152160131164198395553 162689364120098373148796665)
      ·
        refine ⟨122017023090073779861597499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 162689364120098373148796665 122017023090073779861597499)
        ·
          refine ⟨183025534635110669792396249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122017023090073779861597499 183025534635110669792396249)
          ·
            refine ⟨137269150976333002344297187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 183025534635110669792396249 137269150976333002344297187)
            ·
              refine ⟨205903726464499503516445781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 137269150976333002344297187 205903726464499503516445781)
              ·
                refine ⟨2412934294505853556833349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 205903726464499503516445781 2412934294505853556833349)
                ·
                  refine ⟨452425180219847541906253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2412934294505853556833349 452425180219847541906253)
                  ·
                    rfl

theorem cell22_3964927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 8, 4].length) (baseStart_3964927 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3964927 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3964927 prefixEnd_3964927 := by exact prefixLift 3964927
  have htrace : WordTrace (prefixWord ++ tailWord_3964927) baseStart_3964927 baseEnd_3964927 := by
    simpa [prefixWord, tailWord_3964927, baseEnd_3964927] using wordTrace_append hprefix tailTrace_3964927
  have hstable : (prefixWord ++ tailWord_3964927).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3964927).length < 2 ^ (prefixWord ++ tailWord_3964927).sum := by decide
  have hdescent : baseEnd_3964927 < baseStart_3964927 := by decide
  rcases family_descends (prefixWord ++ tailWord_3964927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3964942 : List Nat := [4, 1, 1, 2, 2, 1, 2, 3, 1, 5]
def baseStart_3964942 : Nat := 118140960795 + 3964942 * 2 ^ 59
def prefixEnd_3964942 : Nat := 4983230072969 + 3 ^ 40 * 3964942 * 2
def baseEnd_3964942 : Nat := 1357280675466087586593713

theorem tailTrace_3964942 : CollatzResearch.WordTrace tailWord_3964942 prefixEnd_3964942 1357280675466087586593713 := by
  unfold tailWord_3964942
  simp only [CollatzResearch.WordTrace]
  refine ⟨18076664400212470878424135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 96408876801133178018262053 18076664400212470878424135)
  ·
    refine ⟨27114996600318706317636203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18076664400212470878424135 27114996600318706317636203)
    ·
      refine ⟨40672494900478059476454305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27114996600318706317636203 40672494900478059476454305)
      ·
        refine ⟨30504371175358544607340729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40672494900478059476454305 30504371175358544607340729)
        ·
          refine ⟨22878278381518908455505547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30504371175358544607340729 22878278381518908455505547)
          ·
            refine ⟨34317417572278362683258321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22878278381518908455505547 34317417572278362683258321)
            ·
              refine ⟨25738063179208772012443741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34317417572278362683258321 25738063179208772012443741)
              ·
                refine ⟨9651773692203289504666403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25738063179208772012443741 9651773692203289504666403)
                ·
                  refine ⟨14477660538304934256999605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9651773692203289504666403 14477660538304934256999605)
                  ·
                    refine ⟨1357280675466087586593713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14477660538304934256999605 1357280675466087586593713)
                    ·
                      rfl

theorem cell22_3964942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 2, 3, 1, 5].length) (baseStart_3964942 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3964942 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3964942 prefixEnd_3964942 := by exact prefixLift 3964942
  have htrace : WordTrace (prefixWord ++ tailWord_3964942) baseStart_3964942 baseEnd_3964942 := by
    simpa [prefixWord, tailWord_3964942, baseEnd_3964942] using wordTrace_append hprefix tailTrace_3964942
  have hstable : (prefixWord ++ tailWord_3964942).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3964942).length < 2 ^ (prefixWord ++ tailWord_3964942).sum := by decide
  have hdescent : baseEnd_3964942 < baseStart_3964942 := by decide
  rcases family_descends (prefixWord ++ tailWord_3964942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3964974 : List Nat := [4, 1, 3, 1, 1, 2, 2, 2, 2, 4]
def baseStart_3964974 : Nat := 118140960795 + 3964974 * 2 ^ 59
def prefixEnd_3964974 : Nat := 4983230072969 + 3 ^ 40 * 3964974 * 2
def baseEnd_3964974 : Nat := 1357291629720050169793615

theorem tailTrace_3964974 : CollatzResearch.WordTrace tailWord_3964974 prefixEnd_3964974 1357291629720050169793615 := by
  unfold tailWord_3964974
  simp only [CollatzResearch.WordTrace]
  refine ⟨18076810292197979561569747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 96409654891722557661705317 18076810292197979561569747)
  ·
    refine ⟨27115215438296969342354621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18076810292197979561569747 27115215438296969342354621)
    ·
      refine ⟨10168205789361363503382983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27115215438296969342354621 10168205789361363503382983)
      ·
        refine ⟨15252308684042045255074475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10168205789361363503382983 15252308684042045255074475)
        ·
          refine ⟨22878463026063067882611713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15252308684042045255074475 22878463026063067882611713)
          ·
            refine ⟨17158847269547300911958785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22878463026063067882611713 17158847269547300911958785)
            ·
              refine ⟨12869135452160475683969089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17158847269547300911958785 12869135452160475683969089)
              ·
                refine ⟨9651851589120356762976817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12869135452160475683969089 9651851589120356762976817)
                ·
                  refine ⟨7238888691840267572232613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9651851589120356762976817 7238888691840267572232613)
                  ·
                    refine ⟨1357291629720050169793615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7238888691840267572232613 1357291629720050169793615)
                    ·
                      rfl

theorem cell22_3964974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 2, 2, 2, 4].length) (baseStart_3964974 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3964974 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3964974 prefixEnd_3964974 := by exact prefixLift 3964974
  have htrace : WordTrace (prefixWord ++ tailWord_3964974) baseStart_3964974 baseEnd_3964974 := by
    simpa [prefixWord, tailWord_3964974, baseEnd_3964974] using wordTrace_append hprefix tailTrace_3964974
  have hstable : (prefixWord ++ tailWord_3964974).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3964974).length < 2 ^ (prefixWord ++ tailWord_3964974).sum := by decide
  have hdescent : baseEnd_3964974 < baseStart_3964974 := by decide
  rcases family_descends (prefixWord ++ tailWord_3964974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3965034 : List Nat := [3, 1, 3, 2, 3, 1, 1, 1, 7]
def baseStart_3965034 : Nat := 118140960795 + 3965034 * 2 ^ 59
def prefixEnd_3965034 : Nat := 4983230072969 + 3 ^ 40 * 3965034 * 2
def baseEnd_3965034 : Nat := 452437389648743337764477

theorem tailTrace_3965034 : CollatzResearch.WordTrace tailWord_3965034 prefixEnd_3965034 452437389648743337764477 := by
  unfold tailWord_3965034
  simp only [CollatzResearch.WordTrace]
  refine ⟨36154167679341616684935539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96411113811577644493161437 36154167679341616684935539)
  ·
    refine ⟨54231251519012425027403309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36154167679341616684935539 54231251519012425027403309)
    ·
      refine ⟨20336719319629659385276241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54231251519012425027403309 20336719319629659385276241)
      ·
        refine ⟨15252539489722244538957181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20336719319629659385276241 15252539489722244538957181)
        ·
          refine ⟨5719702308645841702108943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15252539489722244538957181 5719702308645841702108943)
          ·
            refine ⟨8579553462968762553163415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5719702308645841702108943 8579553462968762553163415)
            ·
              refine ⟨12869330194453143829745123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8579553462968762553163415 12869330194453143829745123)
              ·
                refine ⟨19303995291679715744617685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12869330194453143829745123 19303995291679715744617685)
                ·
                  refine ⟨452437389648743337764477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19303995291679715744617685 452437389648743337764477)
                  ·
                    rfl

theorem cell22_3965034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 1, 1, 7].length) (baseStart_3965034 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3965034 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3965034 prefixEnd_3965034 := by exact prefixLift 3965034
  have htrace : WordTrace (prefixWord ++ tailWord_3965034) baseStart_3965034 baseEnd_3965034 := by
    simpa [prefixWord, tailWord_3965034, baseEnd_3965034] using wordTrace_append hprefix tailTrace_3965034
  have hstable : (prefixWord ++ tailWord_3965034).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3965034).length < 2 ^ (prefixWord ++ tailWord_3965034).sum := by decide
  have hdescent : baseEnd_3965034 < baseStart_3965034 := by decide
  rcases family_descends (prefixWord ++ tailWord_3965034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3965077 : List Nat := [1, 3, 2, 1, 1, 1, 4, 1, 3, 5]
def baseStart_3965077 : Nat := 118140960795 + 3965077 * 2 ^ 59
def prefixEnd_3965077 : Nat := 4983230072969 + 3 ^ 40 * 3965077 * 2
def baseEnd_3965077 : Nat := 1357326888724992234468299

theorem tailTrace_3965077 : CollatzResearch.WordTrace tailWord_3965077 prefixEnd_3965077 1357326888724992234468299 := by
  unfold tailWord_3965077
  simp only [CollatzResearch.WordTrace]
  refine ⟨144618239056210685083557485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96412159370807123389038323 144618239056210685083557485)
  ·
    refine ⟨54231839646079006906334057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 144618239056210685083557485 54231839646079006906334057)
    ·
      refine ⟨40673879734559255179750543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54231839646079006906334057 40673879734559255179750543)
      ·
        refine ⟨61010819601838882769625815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40673879734559255179750543 61010819601838882769625815)
        ·
          refine ⟨91516229402758324154438723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61010819601838882769625815 91516229402758324154438723)
          ·
            refine ⟨137274344104137486231658085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91516229402758324154438723 137274344104137486231658085)
            ·
              refine ⟨25738939519525778668435891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 137274344104137486231658085 25738939519525778668435891)
              ·
                refine ⟨38608409279288668002653837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25738939519525778668435891 38608409279288668002653837)
                ·
                  refine ⟨14478153479733250500995189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38608409279288668002653837 14478153479733250500995189)
                  ·
                    refine ⟨1357326888724992234468299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14478153479733250500995189 1357326888724992234468299)
                    ·
                      rfl

theorem cell22_3965077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 4, 1, 3, 5].length) (baseStart_3965077 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3965077 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3965077 prefixEnd_3965077 := by exact prefixLift 3965077
  have htrace : WordTrace (prefixWord ++ tailWord_3965077) baseStart_3965077 baseEnd_3965077 := by
    simpa [prefixWord, tailWord_3965077, baseEnd_3965077] using wordTrace_append hprefix tailTrace_3965077
  have hstable : (prefixWord ++ tailWord_3965077).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3965077).length < 2 ^ (prefixWord ++ tailWord_3965077).sum := by decide
  have hdescent : baseEnd_3965077 < baseStart_3965077 := by decide
  rcases family_descends (prefixWord ++ tailWord_3965077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3965102 : List Nat := [4, 1, 4, 2, 2, 1, 2, 1, 5]
def baseStart_3965102 : Nat := 118140960795 + 3965102 * 2 ^ 59
def prefixEnd_3965102 : Nat := 4983230072969 + 3 ^ 40 * 3965102 * 2
def baseEnd_3965102 : Nat := 452445148911966834197741

theorem tailTrace_3965102 : CollatzResearch.WordTrace tailWord_3965102 prefixEnd_3965102 452445148911966834197741 := by
  unfold tailWord_3965102
  simp only [CollatzResearch.WordTrace]
  refine ⟨18077393860140014294152195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 96412767254080076235478373 18077393860140014294152195)
  ·
    refine ⟨27116090790210021441228293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18077393860140014294152195 27116090790210021441228293)
    ·
      refine ⟨5084267023164379020230305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27116090790210021441228293 5084267023164379020230305)
      ·
        refine ⟨3813200267373284265172729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5084267023164379020230305 3813200267373284265172729)
        ·
          refine ⟨2859900200529963198879547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3813200267373284265172729 2859900200529963198879547)
          ·
            refine ⟨4289850300794944798319321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2859900200529963198879547 4289850300794944798319321)
            ·
              refine ⟨3217387725596208598739491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4289850300794944798319321 3217387725596208598739491)
              ·
                refine ⟨4826081588394312898109237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3217387725596208598739491 4826081588394312898109237)
                ·
                  refine ⟨452445148911966834197741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4826081588394312898109237 452445148911966834197741)
                  ·
                    rfl

theorem cell22_3965102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 2, 1, 2, 1, 5].length) (baseStart_3965102 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3965102 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3965102 prefixEnd_3965102 := by exact prefixLift 3965102
  have htrace : WordTrace (prefixWord ++ tailWord_3965102) baseStart_3965102 baseEnd_3965102 := by
    simpa [prefixWord, tailWord_3965102, baseEnd_3965102] using wordTrace_append hprefix tailTrace_3965102
  have hstable : (prefixWord ++ tailWord_3965102).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3965102).length < 2 ^ (prefixWord ++ tailWord_3965102).sum := by decide
  have hdescent : baseEnd_3965102 < baseStart_3965102 := by decide
  rcases family_descends (prefixWord ++ tailWord_3965102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3965111 : List Nat := [1, 1, 3, 1, 4, 3, 1, 3, 2, 3]
def baseStart_3965111 : Nat := 118140960795 + 3965111 * 2 ^ 59
def prefixEnd_3965111 : Nat := 4983230072969 + 3 ^ 40 * 3965111 * 2
def baseEnd_3965111 : Nat := 1357338527619827479118195

theorem tailTrace_3965111 : CollatzResearch.WordTrace tailWord_3965111 prefixEnd_3965111 1357338527619827479118195 := by
  unfold tailWord_3965111
  simp only [CollatzResearch.WordTrace]
  refine ⟨144619479138087508890295187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96412986092058339260196791 144619479138087508890295187)
  ·
    refine ⟨216929218707131263335442781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144619479138087508890295187 216929218707131263335442781)
    ·
      refine ⟨81348457015174223750791043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 216929218707131263335442781 81348457015174223750791043)
      ·
        refine ⟨122022685522761335626186565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81348457015174223750791043 122022685522761335626186565)
        ·
          refine ⟨22879253535517750429909981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 122022685522761335626186565 22879253535517750429909981)
          ·
            refine ⟨8579720075819156411216243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22879253535517750429909981 8579720075819156411216243)
            ·
              refine ⟨12869580113728734616824365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8579720075819156411216243 12869580113728734616824365)
              ·
                refine ⟨4826092542648275481309137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12869580113728734616824365 4826092542648275481309137)
                ·
                  refine ⟨3619569406986206610981853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4826092542648275481309137 3619569406986206610981853)
                  ·
                    refine ⟨1357338527619827479118195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3619569406986206610981853 1357338527619827479118195)
                    ·
                      rfl

theorem cell22_3965111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 1, 3, 2, 3].length) (baseStart_3965111 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3965111 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3965111 prefixEnd_3965111 := by exact prefixLift 3965111
  have htrace : WordTrace (prefixWord ++ tailWord_3965111) baseStart_3965111 baseEnd_3965111 := by
    simpa [prefixWord, tailWord_3965111, baseEnd_3965111] using wordTrace_append hprefix tailTrace_3965111
  have hstable : (prefixWord ++ tailWord_3965111).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3965111).length < 2 ^ (prefixWord ++ tailWord_3965111).sum := by decide
  have hdescent : baseEnd_3965111 < baseStart_3965111 := by decide
  rcases family_descends (prefixWord ++ tailWord_3965111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3965124 : List Nat := [2, 3, 3, 1, 2, 1, 2, 8]
def baseStart_3965124 : Nat := 118140960795 + 3965124 * 2 ^ 59
def prefixEnd_3965124 : Nat := 4983230072969 + 3 ^ 40 * 3965124 * 2
def baseEnd_3965124 : Nat := 150815886420611086504795

theorem tailTrace_3965124 : CollatzResearch.WordTrace tailWord_3965124 prefixEnd_3965124 150815886420611086504795 := by
  unfold tailWord_3965124
  simp only [CollatzResearch.WordTrace]
  refine ⟨72309976643520206055259213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96413302191360274740345617 72309976643520206055259213)
  ·
    refine ⟨27116241241320077270722205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72309976643520206055259213 27116241241320077270722205)
    ·
      refine ⟨10168590465495028976520827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27116241241320077270722205 10168590465495028976520827)
      ·
        refine ⟨15252885698242543464781241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10168590465495028976520827 15252885698242543464781241)
        ·
          refine ⟨11439664273681907598585931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15252885698242543464781241 11439664273681907598585931)
          ·
            refine ⟨17159496410522861397878897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11439664273681907598585931 17159496410522861397878897)
            ·
              refine ⟨12869622307892146048409173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17159496410522861397878897 12869622307892146048409173)
              ·
                refine ⟨150815886420611086504795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12869622307892146048409173 150815886420611086504795)
                ·
                  rfl

theorem cell22_3965124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 2, 8].length) (baseStart_3965124 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3965124 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3965124 prefixEnd_3965124 := by exact prefixLift 3965124
  have htrace : WordTrace (prefixWord ++ tailWord_3965124) baseStart_3965124 baseEnd_3965124 := by
    simpa [prefixWord, tailWord_3965124, baseEnd_3965124] using wordTrace_append hprefix tailTrace_3965124
  have hstable : (prefixWord ++ tailWord_3965124).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3965124).length < 2 ^ (prefixWord ++ tailWord_3965124).sum := by decide
  have hdescent : baseEnd_3965124 < baseStart_3965124 := by decide
  rcases family_descends (prefixWord ++ tailWord_3965124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3965169 : List Nat := [1, 2, 2, 2, 2, 1, 4, 3, 5]
def baseStart_3965169 : Nat := 118140960795 + 3965169 * 2 ^ 59
def prefixEnd_3965169 : Nat := 4983230072969 + 3 ^ 40 * 3965169 * 2
def baseEnd_3965169 : Nat := 452452794068378220389339

theorem tailTrace_3965169 : CollatzResearch.WordTrace tailWord_3965169 prefixEnd_3965169 452452794068378220389339 := by
  unfold tailWord_3965169
  simp only [CollatzResearch.WordTrace]
  refine ⟨144621594571877384795906561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96414396381251589863937707 144621594571877384795906561)
  ·
    refine ⟨108466195928908038596929921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144621594571877384795906561 108466195928908038596929921)
    ·
      refine ⟨81349646946681028947697441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108466195928908038596929921 81349646946681028947697441)
      ·
        refine ⟨61012235210010771710773081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81349646946681028947697441 61012235210010771710773081)
        ·
          refine ⟨45759176407508078783079811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61012235210010771710773081 45759176407508078783079811)
          ·
            refine ⟨68638764611262118174619717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45759176407508078783079811 68638764611262118174619717)
            ·
              refine ⟨12869768364611647157741197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 68638764611262118174619717 12869768364611647157741197)
              ·
                refine ⟨4826163136729367684152949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12869768364611647157741197 4826163136729367684152949)
                ·
                  refine ⟨452452794068378220389339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4826163136729367684152949 452452794068378220389339)
                  ·
                    rfl

theorem cell22_3965169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 4, 3, 5].length) (baseStart_3965169 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3965169 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3965169 prefixEnd_3965169 := by exact prefixLift 3965169
  have htrace : WordTrace (prefixWord ++ tailWord_3965169) baseStart_3965169 baseEnd_3965169 := by
    simpa [prefixWord, tailWord_3965169, baseEnd_3965169] using wordTrace_append hprefix tailTrace_3965169
  have hstable : (prefixWord ++ tailWord_3965169).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3965169).length < 2 ^ (prefixWord ++ tailWord_3965169).sum := by decide
  have hdescent : baseEnd_3965169 < baseStart_3965169 := by decide
  rcases family_descends (prefixWord ++ tailWord_3965169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3965233 : List Nat := [1, 2, 2, 3, 4, 1, 2, 2, 1, 4]
def baseStart_3965233 : Nat := 118140960795 + 3965233 * 2 ^ 59
def prefixEnd_3965233 : Nat := 4983230072969 + 3 ^ 40 * 3965233 * 2
def baseEnd_3965233 : Nat := 1357380290713059827567821

theorem tailTrace_3965233 : CollatzResearch.WordTrace tailWord_3965233 prefixEnd_3965233 1357380290713059827567821 := by
  unfold tailWord_3965233
  simp only [CollatzResearch.WordTrace]
  refine ⟨144623928843645523726236353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96415952562430349150824235 144623928843645523726236353)
  ·
    refine ⟨108467946632734142794677265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144623928843645523726236353 108467946632734142794677265)
    ·
      refine ⟨81350959974550607096007949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108467946632734142794677265 81350959974550607096007949)
      ·
        refine ⟨30506609990456477661002981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81350959974550607096007949 30506609990456477661002981)
        ·
          refine ⟨5719989373210589561438059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30506609990456477661002981 5719989373210589561438059)
          ·
            refine ⟨8579984059815884342157089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5719989373210589561438059 8579984059815884342157089)
            ·
              refine ⟨6434988044861913256617817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8579984059815884342157089 6434988044861913256617817)
              ·
                refine ⟨4826241033646434942463363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6434988044861913256617817 4826241033646434942463363)
                ·
                  refine ⟨7239361550469652413695045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4826241033646434942463363 7239361550469652413695045)
                  ·
                    refine ⟨1357380290713059827567821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7239361550469652413695045 1357380290713059827567821)
                    ·
                      rfl

theorem cell22_3965233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 2, 2, 1, 4].length) (baseStart_3965233 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3965233 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3965233 prefixEnd_3965233 := by exact prefixLift 3965233
  have htrace : WordTrace (prefixWord ++ tailWord_3965233) baseStart_3965233 baseEnd_3965233 := by
    simpa [prefixWord, tailWord_3965233, baseEnd_3965233] using wordTrace_append hprefix tailTrace_3965233
  have hstable : (prefixWord ++ tailWord_3965233).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3965233).length < 2 ^ (prefixWord ++ tailWord_3965233).sum := by decide
  have hdescent : baseEnd_3965233 < baseStart_3965233 := by decide
  rcases family_descends (prefixWord ++ tailWord_3965233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3965244 : List Nat := [2, 2, 2, 2, 1, 2, 1, 3, 1, 6]
def baseStart_3965244 : Nat := 118140960795 + 3965244 * 2 ^ 59
def prefixEnd_3965244 : Nat := 4983230072969 + 3 ^ 40 * 3965244 * 2
def baseEnd_3965244 : Nat := 1357384056237859465542787

theorem tailTrace_3965244 : CollatzResearch.WordTrace tailWord_3965244 prefixEnd_3965244 1357384056237859465542787 := by
  unfold tailWord_3965244
  simp only [CollatzResearch.WordTrace]
  refine ⟨72312165023302836302443393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96416220031070448403257857 72312165023302836302443393)
  ·
    refine ⟨54234123767477127226832545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72312165023302836302443393 54234123767477127226832545)
    ·
      refine ⟨40675592825607845420124409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54234123767477127226832545 40675592825607845420124409)
      ·
        refine ⟨30506694619205884065093307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40675592825607845420124409 30506694619205884065093307)
        ·
          refine ⟨45760041928808826097639961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30506694619205884065093307 45760041928808826097639961)
          ·
            refine ⟨34320031446606619573229971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45760041928808826097639961 34320031446606619573229971)
            ·
              refine ⟨51480047169909929359844957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34320031446606619573229971 51480047169909929359844957)
              ·
                refine ⟨19305017688716223509941859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51480047169909929359844957 19305017688716223509941859)
                ·
                  refine ⟨28957526533074335264912789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19305017688716223509941859 28957526533074335264912789)
                  ·
                    refine ⟨1357384056237859465542787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28957526533074335264912789 1357384056237859465542787)
                    ·
                      rfl

theorem cell22_3965244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 3, 1, 6].length) (baseStart_3965244 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3965244 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3965244 prefixEnd_3965244 := by exact prefixLift 3965244
  have htrace : WordTrace (prefixWord ++ tailWord_3965244) baseStart_3965244 baseEnd_3965244 := by
    simpa [prefixWord, tailWord_3965244, baseEnd_3965244] using wordTrace_append hprefix tailTrace_3965244
  have hstable : (prefixWord ++ tailWord_3965244).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3965244).length < 2 ^ (prefixWord ++ tailWord_3965244).sum := by decide
  have hdescent : baseEnd_3965244 < baseStart_3965244 := by decide
  rcases family_descends (prefixWord ++ tailWord_3965244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3965321 : List Nat := [1, 2, 1, 1, 6, 1, 1, 4, 5]
def baseStart_3965321 : Nat := 118140960795 + 3965321 * 2 ^ 59
def prefixEnd_3965321 : Nat := 4983230072969 + 3 ^ 40 * 3965321 * 2
def baseEnd_3965321 : Nat := 452470138303818977122517

theorem tailTrace_3965321 : CollatzResearch.WordTrace tailWord_3965321 prefixEnd_3965321 452470138303818977122517 := by
  unfold tailWord_3965321
  simp only [CollatzResearch.WordTrace]
  refine ⟨144627138467326714755439817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96418092311551143170293211 144627138467326714755439817)
  ·
    refine ⟨108470353850495036066579863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144627138467326714755439817 108470353850495036066579863)
    ·
      refine ⟨162705530775742554099869795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108470353850495036066579863 162705530775742554099869795)
      ·
        refine ⟨244058296163613831149804693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162705530775742554099869795 244058296163613831149804693)
        ·
          refine ⟨11440232632669398335147095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 244058296163613831149804693 11440232632669398335147095)
          ·
            refine ⟨17160348949004097502720643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11440232632669398335147095 17160348949004097502720643)
            ·
              refine ⟨25740523423506146254080965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17160348949004097502720643 25740523423506146254080965)
              ·
                refine ⟨4826348141907402422640181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25740523423506146254080965 4826348141907402422640181)
                ·
                  refine ⟨452470138303818977122517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4826348141907402422640181 452470138303818977122517)
                  ·
                    rfl

theorem cell22_3965321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 1, 4, 5].length) (baseStart_3965321 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3965321 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3965321 prefixEnd_3965321 := by exact prefixLift 3965321
  have htrace : WordTrace (prefixWord ++ tailWord_3965321) baseStart_3965321 baseEnd_3965321 := by
    simpa [prefixWord, tailWord_3965321, baseEnd_3965321] using wordTrace_append hprefix tailTrace_3965321
  have hstable : (prefixWord ++ tailWord_3965321).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3965321).length < 2 ^ (prefixWord ++ tailWord_3965321).sum := by decide
  have hdescent : baseEnd_3965321 < baseStart_3965321 := by decide
  rcases family_descends (prefixWord ++ tailWord_3965321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3965336 : List Nat := [2, 1, 2, 5, 1, 1, 1, 1, 1, 7]
def baseStart_3965336 : Nat := 118140960795 + 3965336 * 2 ^ 59
def prefixEnd_3965336 : Nat := 4983230072969 + 3 ^ 40 * 3965336 * 2
def baseEnd_3965336 : Nat := 1357415549718001892242505

theorem tailTrace_3965336 : CollatzResearch.WordTrace tailWord_3965336 prefixEnd_3965336 1357415549718001892242505 := by
  unfold tailWord_3965336
  simp only [CollatzResearch.WordTrace]
  refine ⟨72313842781136186158617931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96418457041514914878157241 72313842781136186158617931)
  ·
    refine ⟨108470764171704279237926897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72313842781136186158617931 108470764171704279237926897)
    ·
      refine ⟨81353073128778209428445173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108470764171704279237926897 81353073128778209428445173)
      ·
        refine ⟨7626850605822957133916735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 81353073128778209428445173 7626850605822957133916735)
        ·
          refine ⟨11440275908734435700875103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7626850605822957133916735 11440275908734435700875103)
          ·
            refine ⟨17160413863101653551312655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11440275908734435700875103 17160413863101653551312655)
            ·
              refine ⟨25740620794652480326968983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17160413863101653551312655 25740620794652480326968983)
              ·
                refine ⟨38610931191978720490453475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25740620794652480326968983 38610931191978720490453475)
                ·
                  refine ⟨57916396787968080735680213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38610931191978720490453475 57916396787968080735680213)
                  ·
                    refine ⟨1357415549718001892242505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 57916396787968080735680213 1357415549718001892242505)
                    ·
                      rfl

theorem cell22_3965336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 1, 1, 1, 7].length) (baseStart_3965336 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3965336 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3965336 prefixEnd_3965336 := by exact prefixLift 3965336
  have htrace : WordTrace (prefixWord ++ tailWord_3965336) baseStart_3965336 baseEnd_3965336 := by
    simpa [prefixWord, tailWord_3965336, baseEnd_3965336] using wordTrace_append hprefix tailTrace_3965336
  have hstable : (prefixWord ++ tailWord_3965336).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3965336).length < 2 ^ (prefixWord ++ tailWord_3965336).sum := by decide
  have hdescent : baseEnd_3965336 < baseStart_3965336 := by decide
  rcases family_descends (prefixWord ++ tailWord_3965336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3965383 : List Nat := [1, 1, 4, 1, 1, 4, 2, 4, 4]
def baseStart_3965383 : Nat := 118140960795 + 3965383 * 2 ^ 59
def prefixEnd_3965383 : Nat := 4983230072969 + 3 ^ 40 * 3965383 * 2
def baseEnd_3965383 : Nat := 452477212926169812105787

theorem tailTrace_3965383 : CollatzResearch.WordTrace tailWord_3965383 prefixEnd_3965383 452477212926169812105787 := by
  unfold tailWord_3965383
  simp only [CollatzResearch.WordTrace]
  refine ⟨144629399793102099344196803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96419599862068066229464535 144629399793102099344196803)
  ·
    refine ⟨216944099689653149016295205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144629399793102099344196803 216944099689653149016295205)
    ·
      refine ⟨40677018691809965440555351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 216944099689653149016295205 40677018691809965440555351)
      ·
        refine ⟨61015528037714948160833027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40677018691809965440555351 61015528037714948160833027)
        ·
          refine ⟨91523292056572422241249541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61015528037714948160833027 91523292056572422241249541)
          ·
            refine ⟨17160617260607329170234289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 91523292056572422241249541 17160617260607329170234289)
            ·
              refine ⟨12870462945455496877675717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17160617260607329170234289 12870462945455496877675717)
              ·
                refine ⟨2413211802272905664564197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12870462945455496877675717 2413211802272905664564197)
                ·
                  refine ⟨452477212926169812105787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2413211802272905664564197 452477212926169812105787)
                  ·
                    rfl

theorem cell22_3965383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 2, 4, 4].length) (baseStart_3965383 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3965383 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3965383 prefixEnd_3965383 := by exact prefixLift 3965383
  have htrace : WordTrace (prefixWord ++ tailWord_3965383) baseStart_3965383 baseEnd_3965383 := by
    simpa [prefixWord, tailWord_3965383, baseEnd_3965383] using wordTrace_append hprefix tailTrace_3965383
  have hstable : (prefixWord ++ tailWord_3965383).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3965383).length < 2 ^ (prefixWord ++ tailWord_3965383).sum := by decide
  have hdescent : baseEnd_3965383 < baseStart_3965383 := by decide
  rcases family_descends (prefixWord ++ tailWord_3965383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3965471 : List Nat := [1, 1, 2, 4, 1, 1, 1, 2, 4, 5]
def baseStart_3965471 : Nat := 118140960795 + 3965471 * 2 ^ 59
def prefixEnd_3965471 : Nat := 4983230072969 + 3 ^ 40 * 3965471 * 2
def baseEnd_3965471 : Nat := 1357461762976906540117091

theorem tailTrace_3965471 : CollatzResearch.WordTrace tailWord_3965471 prefixEnd_3965471 1357461762976906540117091 := by
  unfold tailWord_3965471
  simp only [CollatzResearch.WordTrace]
  refine ⟨144632609416783290373400267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96421739611188860248933511 144632609416783290373400267)
  ·
    refine ⟨216948914125174935560100401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144632609416783290373400267 216948914125174935560100401)
    ·
      refine ⟨162711685593881201670075301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 216948914125174935560100401 162711685593881201670075301)
      ·
        refine ⟨30508441048852725313139119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 162711685593881201670075301 30508441048852725313139119)
        ·
          refine ⟨45762661573279087969708679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30508441048852725313139119 45762661573279087969708679)
          ·
            refine ⟨68643992359918631954563019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45762661573279087969708679 68643992359918631954563019)
            ·
              refine ⟨102965988539877947931844529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68643992359918631954563019 102965988539877947931844529)
              ·
                refine ⟨77224491404908460948883397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 102965988539877947931844529 77224491404908460948883397)
                ·
                  refine ⟨14479592138420336427915637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 77224491404908460948883397 14479592138420336427915637)
                  ·
                    refine ⟨1357461762976906540117091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14479592138420336427915637 1357461762976906540117091)
                    ·
                      rfl

theorem cell22_3965471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 2, 4, 5].length) (baseStart_3965471 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3965471 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3965471 prefixEnd_3965471 := by exact prefixLift 3965471
  have htrace : WordTrace (prefixWord ++ tailWord_3965471) baseStart_3965471 baseEnd_3965471 := by
    simpa [prefixWord, tailWord_3965471, baseEnd_3965471] using wordTrace_append hprefix tailTrace_3965471
  have hstable : (prefixWord ++ tailWord_3965471).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3965471).length < 2 ^ (prefixWord ++ tailWord_3965471).sum := by decide
  have hdescent : baseEnd_3965471 < baseStart_3965471 := by decide
  rcases family_descends (prefixWord ++ tailWord_3965471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3965494 : List Nat := [5, 1, 2, 1, 2, 2, 1, 4, 1, 3]
def baseStart_3965494 : Nat := 118140960795 + 3965494 * 2 ^ 59
def prefixEnd_3965494 : Nat := 4983230072969 + 3 ^ 40 * 3965494 * 2
def baseEnd_3965494 : Nat := 1357469636346942146792021

theorem tailTrace_3965494 : CollatzResearch.WordTrace tailWord_3965494 prefixEnd_3965494 1357469636346942146792021 := by
  unfold tailWord_3965494
  simp only [CollatzResearch.WordTrace]
  refine ⟨9039590518481247831342971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 96422298863799976867658357 9039590518481247831342971)
  ·
    refine ⟨13559385777721871747014457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9039590518481247831342971 13559385777721871747014457)
    ·
      refine ⟨10169539333291403810260843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13559385777721871747014457 10169539333291403810260843)
      ·
        refine ⟨15254308999937105715391265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10169539333291403810260843 15254308999937105715391265)
        ·
          refine ⟨11440731749952829286543449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15254308999937105715391265 11440731749952829286543449)
          ·
            refine ⟨8580548812464621964907587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11440731749952829286543449 8580548812464621964907587)
            ·
              refine ⟨12870823218696932947361381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8580548812464621964907587 12870823218696932947361381)
              ·
                refine ⟨2413279353505674927630259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12870823218696932947361381 2413279353505674927630259)
                ·
                  refine ⟨3619919030258512391445389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2413279353505674927630259 3619919030258512391445389)
                  ·
                    refine ⟨1357469636346942146792021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3619919030258512391445389 1357469636346942146792021)
                    ·
                      rfl

theorem cell22_3965494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 1, 4, 1, 3].length) (baseStart_3965494 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3965494 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3965494 prefixEnd_3965494 := by exact prefixLift 3965494
  have htrace : WordTrace (prefixWord ++ tailWord_3965494) baseStart_3965494 baseEnd_3965494 := by
    simpa [prefixWord, tailWord_3965494, baseEnd_3965494] using wordTrace_append hprefix tailTrace_3965494
  have hstable : (prefixWord ++ tailWord_3965494).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3965494).length < 2 ^ (prefixWord ++ tailWord_3965494).sum := by decide
  have hdescent : baseEnd_3965494 < baseStart_3965494 := by decide
  rcases family_descends (prefixWord ++ tailWord_3965494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3965537 : List Nat := [1, 2, 3, 1, 1, 6, 2, 1, 1, 4]
def baseStart_3965537 : Nat := 118140960795 + 3965537 * 2 ^ 59
def prefixEnd_3965537 : Nat := 4983230072969 + 3 ^ 40 * 3965537 * 2
def baseEnd_3965537 : Nat := 1357484356125704367966889

theorem tailTrace_3965537 : CollatzResearch.WordTrace tailWord_3965537 prefixEnd_3965537 1357484356125704367966889 := by
  unfold tailWord_3965537
  simp only [CollatzResearch.WordTrace]
  refine ⟨144635016634544183645302865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96423344423029455763535243 144635016634544183645302865)
  ·
    refine ⟨108476262475908137733977149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144635016634544183645302865 108476262475908137733977149)
    ·
      refine ⟨40678598428465551650241431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 108476262475908137733977149 40678598428465551650241431)
      ·
        refine ⟨61017897642698327475362147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40678598428465551650241431 61017897642698327475362147)
        ·
          refine ⟨91526846464047491213043221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61017897642698327475362147 91526846464047491213043221)
          ·
            refine ⟨4290320928002226150611401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 91526846464047491213043221 4290320928002226150611401)
            ·
              refine ⟨3217740696001669612958551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4290320928002226150611401 3217740696001669612958551)
              ·
                refine ⟨4826611044002504419437827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3217740696001669612958551 4826611044002504419437827)
                ·
                  refine ⟨7239916566003756629156741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4826611044002504419437827 7239916566003756629156741)
                  ·
                    refine ⟨1357484356125704367966889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7239916566003756629156741 1357484356125704367966889)
                    ·
                      rfl

theorem cell22_3965537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 6, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 6, 2, 1, 1, 4].length) (baseStart_3965537 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3965537 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3965537 prefixEnd_3965537 := by exact prefixLift 3965537
  have htrace : WordTrace (prefixWord ++ tailWord_3965537) baseStart_3965537 baseEnd_3965537 := by
    simpa [prefixWord, tailWord_3965537, baseEnd_3965537] using wordTrace_append hprefix tailTrace_3965537
  have hstable : (prefixWord ++ tailWord_3965537).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3965537).length < 2 ^ (prefixWord ++ tailWord_3965537).sum := by decide
  have hdescent : baseEnd_3965537 < baseStart_3965537 := by decide
  rcases family_descends (prefixWord ++ tailWord_3965537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3965548 : List Nat := [2, 2, 1, 1, 3, 1, 2, 4, 2, 4]
def baseStart_3965548 : Nat := 118140960795 + 3965548 * 2 ^ 59
def prefixEnd_3965548 : Nat := 4983230072969 + 3 ^ 40 * 3965548 * 2
def baseEnd_3965548 : Nat := 1357488121650504005941855

theorem tailTrace_3965548 : CollatzResearch.WordTrace tailWord_3965548 prefixEnd_3965548 1357488121650504005941855 := by
  unfold tailWord_3965548
  simp only [CollatzResearch.WordTrace]
  refine ⟨72317708918752166261976649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96423611891669555015968865 72317708918752166261976649)
  ·
    refine ⟨54238281689064124696482487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72317708918752166261976649 54238281689064124696482487)
    ·
      refine ⟨81357422533596187044723731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54238281689064124696482487 81357422533596187044723731)
      ·
        refine ⟨122036133800394280567085597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81357422533596187044723731 122036133800394280567085597)
        ·
          refine ⟨45763550175147855212657099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 122036133800394280567085597 45763550175147855212657099)
          ·
            refine ⟨68645325262721782818985649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45763550175147855212657099 68645325262721782818985649)
            ·
              refine ⟨51483993947041337114239237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68645325262721782818985649 51483993947041337114239237)
              ·
                refine ⟨9653248865070250708919857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 51483993947041337114239237 9653248865070250708919857)
                ·
                  refine ⟨7239936648802688031689893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9653248865070250708919857 7239936648802688031689893)
                  ·
                    refine ⟨1357488121650504005941855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7239936648802688031689893 1357488121650504005941855)
                    ·
                      rfl

theorem cell22_3965548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 4].length) (baseStart_3965548 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3965548 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3965548 prefixEnd_3965548 := by exact prefixLift 3965548
  have htrace : WordTrace (prefixWord ++ tailWord_3965548) baseStart_3965548 baseEnd_3965548 := by
    simpa [prefixWord, tailWord_3965548, baseEnd_3965548] using wordTrace_append hprefix tailTrace_3965548
  have hstable : (prefixWord ++ tailWord_3965548).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3965548).length < 2 ^ (prefixWord ++ tailWord_3965548).sum := by decide
  have hdescent : baseEnd_3965548 < baseStart_3965548 := by decide
  rcases family_descends (prefixWord ++ tailWord_3965548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3965683 : List Nat := [1, 1, 1, 2, 2, 3, 1, 4, 1, 6]
def baseStart_3965683 : Nat := 118140960795 + 3965683 * 2 ^ 59
def prefixEnd_3965683 : Nat := 4983230072969 + 3 ^ 40 * 3965683 * 2
def baseEnd_3965683 : Nat := 1357534334909408653816441

theorem tailTrace_3965683 : CollatzResearch.WordTrace tailWord_3965683 prefixEnd_3965683 1357534334909408653816441 := by
  unfold tailWord_3965683
  simp only [CollatzResearch.WordTrace]
  refine ⟨144640341692015250580117703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96426894461343500386745135 144640341692015250580117703)
  ·
    refine ⟨216960512538022875870176555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144640341692015250580117703 216960512538022875870176555)
    ·
      refine ⟨325440768807034313805264833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216960512538022875870176555 325440768807034313805264833)
      ·
        refine ⟨244080576605275735353948625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 325440768807034313805264833 244080576605275735353948625)
        ·
          refine ⟨183060432453956801515461469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 244080576605275735353948625 183060432453956801515461469)
          ·
            refine ⟨68647662170233800568298051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 183060432453956801515461469 68647662170233800568298051)
            ·
              refine ⟨102971493255350700852447077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68647662170233800568298051 102971493255350700852447077)
              ·
                refine ⟨19307154985378256409833827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 102971493255350700852447077 19307154985378256409833827)
                ·
                  refine ⟨28960732478067384614750741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19307154985378256409833827 28960732478067384614750741)
                  ·
                    refine ⟨1357534334909408653816441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28960732478067384614750741 1357534334909408653816441)
                    ·
                      rfl

theorem cell22_3965683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 4, 1, 6].length) (baseStart_3965683 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3965683 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3965683 prefixEnd_3965683 := by exact prefixLift 3965683
  have htrace : WordTrace (prefixWord ++ tailWord_3965683) baseStart_3965683 baseEnd_3965683 := by
    simpa [prefixWord, tailWord_3965683, baseEnd_3965683] using wordTrace_append hprefix tailTrace_3965683
  have hstable : (prefixWord ++ tailWord_3965683).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3965683).length < 2 ^ (prefixWord ++ tailWord_3965683).sum := by decide
  have hdescent : baseEnd_3965683 < baseStart_3965683 := by decide
  rcases family_descends (prefixWord ++ tailWord_3965683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3965700 : List Nat := [2, 3, 2, 2, 1, 1, 3, 1, 1, 6]
def baseStart_3965700 : Nat := 118140960795 + 3965700 * 2 ^ 59
def prefixEnd_3965700 : Nat := 4983230072969 + 3 ^ 40 * 3965700 * 2
def baseEnd_3965700 : Nat := 1357540154356826276141389

theorem tailTrace_3965700 : CollatzResearch.WordTrace tailWord_3965700 prefixEnd_3965700 1357540154356826276141389 := by
  unfold tailWord_3965700
  simp only [CollatzResearch.WordTrace]
  refine ⟨72320480866476831241743277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96427307821969108322324369 72320480866476831241743277)
  ·
    refine ⟨27120180324928811715653729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72320480866476831241743277 27120180324928811715653729)
    ·
      refine ⟨20340135243696608786740297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27120180324928811715653729 20340135243696608786740297)
      ·
        refine ⟨15255101432772456590055223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20340135243696608786740297 15255101432772456590055223)
        ·
          refine ⟨22882652149158684885082835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15255101432772456590055223 22882652149158684885082835)
          ·
            refine ⟨34323978223738027327624253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22882652149158684885082835 34323978223738027327624253)
            ·
              refine ⟨12871491833901760247859095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34323978223738027327624253 12871491833901760247859095)
              ·
                refine ⟨19307237750852640371788643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12871491833901760247859095 19307237750852640371788643)
                ·
                  refine ⟨28960856626278960557682965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19307237750852640371788643 28960856626278960557682965)
                  ·
                    refine ⟨1357540154356826276141389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28960856626278960557682965 1357540154356826276141389)
                    ·
                      rfl

theorem cell22_3965700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 3, 1, 1, 6].length) (baseStart_3965700 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3965700 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3965700 prefixEnd_3965700 := by exact prefixLift 3965700
  have htrace : WordTrace (prefixWord ++ tailWord_3965700) baseStart_3965700 baseEnd_3965700 := by
    simpa [prefixWord, tailWord_3965700, baseEnd_3965700] using wordTrace_append hprefix tailTrace_3965700
  have hstable : (prefixWord ++ tailWord_3965700).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3965700).length < 2 ^ (prefixWord ++ tailWord_3965700).sum := by decide
  have hdescent : baseEnd_3965700 < baseStart_3965700 := by decide
  rcases family_descends (prefixWord ++ tailWord_3965700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3965743 : List Nat := [1, 1, 2, 1, 2, 1, 2, 1, 11]
def baseStart_3965743 : Nat := 118140960795 + 3965743 * 2 ^ 59
def prefixEnd_3965743 : Nat := 4983230072969 + 3 ^ 40 * 3965743 * 2
def baseEnd_3965743 : Nat := 452518291378529499105419

theorem tailTrace_3965743 : CollatzResearch.WordTrace tailWord_3965743 prefixEnd_3965743 452518291378529499105419 := by
  unfold tailWord_3965743
  simp only [CollatzResearch.WordTrace]
  refine ⟨144642530071797880827301883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96428353381198587218201255 144642530071797880827301883)
  ·
    refine ⟨216963795107696821240952825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144642530071797880827301883 216963795107696821240952825)
    ·
      refine ⟨162722846330772615930714619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 216963795107696821240952825 162722846330772615930714619)
      ·
        refine ⟨244084269496158923896071929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162722846330772615930714619 244084269496158923896071929)
        ·
          refine ⟨183063202122119192922053947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 244084269496158923896071929 183063202122119192922053947)
          ·
            refine ⟨274594803183178789383080921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 183063202122119192922053947 274594803183178789383080921)
            ·
              refine ⟨205946102387384092037310691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 274594803183178789383080921 205946102387384092037310691)
              ·
                refine ⟨308919153581076138055966037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 205946102387384092037310691 308919153581076138055966037)
                ·
                  refine ⟨452518291378529499105419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 308919153581076138055966037 452518291378529499105419)
                  ·
                    rfl

theorem cell22_3965743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 1, 11].length) (baseStart_3965743 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3965743 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3965743 prefixEnd_3965743 := by exact prefixLift 3965743
  have htrace : WordTrace (prefixWord ++ tailWord_3965743) baseStart_3965743 baseEnd_3965743 := by
    simpa [prefixWord, tailWord_3965743, baseEnd_3965743] using wordTrace_append hprefix tailTrace_3965743
  have hstable : (prefixWord ++ tailWord_3965743).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3965743).length < 2 ^ (prefixWord ++ tailWord_3965743).sum := by decide
  have hdescent : baseEnd_3965743 < baseStart_3965743 := by decide
  rcases family_descends (prefixWord ++ tailWord_3965743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3965747 : List Nat := [1, 1, 1, 2, 6, 1, 2, 2, 3, 3]
def baseStart_3965747 : Nat := 118140960795 + 3965747 * 2 ^ 59
def prefixEnd_3965747 : Nat := 4983230072969 + 3 ^ 40 * 3965747 * 2
def baseEnd_3965747 : Nat := 1357556243417333820216245

theorem tailTrace_3965747 : CollatzResearch.WordTrace tailWord_3965747 prefixEnd_3965747 1357556243417333820216245 := by
  unfold tailWord_3965747
  simp only [CollatzResearch.WordTrace]
  refine ⟨144642675963783389510447495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96428450642522259673631663 144642675963783389510447495)
  ·
    refine ⟨216964013945675084265671243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144642675963783389510447495 216964013945675084265671243)
    ·
      refine ⟨325446020918512626398506865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216964013945675084265671243 325446020918512626398506865)
      ·
        refine ⟨244084515688884469798880149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 325446020918512626398506865 244084515688884469798880149)
        ·
          refine ⟨11441461672916459521822507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 244084515688884469798880149 11441461672916459521822507)
          ·
            refine ⟨17162192509374689282733761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11441461672916459521822507 17162192509374689282733761)
            ·
              refine ⟨12871644382031016962050321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17162192509374689282733761 12871644382031016962050321)
              ·
                refine ⟨9653733286523262721537741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12871644382031016962050321 9653733286523262721537741)
                ·
                  refine ⟨3620149982446223520576653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9653733286523262721537741 3620149982446223520576653)
                  ·
                    refine ⟨1357556243417333820216245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3620149982446223520576653 1357556243417333820216245)
                    ·
                      rfl

theorem cell22_3965747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 2, 2, 3, 3].length) (baseStart_3965747 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3965747 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3965747 prefixEnd_3965747 := by exact prefixLift 3965747
  have htrace : WordTrace (prefixWord ++ tailWord_3965747) baseStart_3965747 baseEnd_3965747 := by
    simpa [prefixWord, tailWord_3965747, baseEnd_3965747] using wordTrace_append hprefix tailTrace_3965747
  have hstable : (prefixWord ++ tailWord_3965747).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3965747).length < 2 ^ (prefixWord ++ tailWord_3965747).sum := by decide
  have hdescent : baseEnd_3965747 < baseStart_3965747 := by decide
  rcases family_descends (prefixWord ++ tailWord_3965747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3965766 : List Nat := [6, 1, 1, 2, 3, 1, 8]
def baseStart_3965766 : Nat := 118140960795 + 3965766 * 2 ^ 59
def prefixEnd_3965766 : Nat := 4983230072969 + 3 ^ 40 * 3965766 * 2
def baseEnd_3965766 : Nat := 50280101759467559407081

theorem tailTrace_3965766 : CollatzResearch.WordTrace tailWord_3965766 prefixEnd_3965766 50280101759467559407081 := by
  unfold tailWord_3965766
  simp only [CollatzResearch.WordTrace]
  refine ⟨4520105279709829867355911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 96428912633809703836926101 4520105279709829867355911)
  ·
    refine ⟨6780157919564744801033867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4520105279709829867355911 6780157919564744801033867)
    ·
      refine ⟨10170236879347117201550801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6780157919564744801033867 10170236879347117201550801)
      ·
        refine ⟨7627677659510337901163101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10170236879347117201550801 7627677659510337901163101)
        ·
          refine ⟨2860379122316376712936163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7627677659510337901163101 2860379122316376712936163)
          ·
            refine ⟨4290568683474565069404245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2860379122316376712936163 4290568683474565069404245)
            ·
              refine ⟨50280101759467559407081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4290568683474565069404245 50280101759467559407081)
              ·
                rfl

theorem cell22_3965766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 3, 1, 8].length) (baseStart_3965766 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3965766 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3965766 prefixEnd_3965766 := by exact prefixLift 3965766
  have htrace : WordTrace (prefixWord ++ tailWord_3965766) baseStart_3965766 baseEnd_3965766 := by
    simpa [prefixWord, tailWord_3965766, baseEnd_3965766] using wordTrace_append hprefix tailTrace_3965766
  have hstable : (prefixWord ++ tailWord_3965766).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3965766).length < 2 ^ (prefixWord ++ tailWord_3965766).sum := by decide
  have hdescent : baseEnd_3965766 < baseStart_3965766 := by decide
  rcases family_descends (prefixWord ++ tailWord_3965766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3965781 : List Nat := [1, 3, 2, 2, 2, 1, 5, 2, 1, 3]
def baseStart_3965781 : Nat := 118140960795 + 3965781 * 2 ^ 59
def prefixEnd_3965781 : Nat := 4983230072969 + 3 ^ 40 * 3965781 * 2
def baseEnd_3965781 : Nat := 1357567882312169064866141

theorem tailTrace_3965781 : CollatzResearch.WordTrace tailWord_3965781 prefixEnd_3965781 1357567882312169064866141 := by
  unfold tailWord_3965781
  simp only [CollatzResearch.WordTrace]
  refine ⟨144643916045660213317185197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96429277363773475544790131 144643916045660213317185197)
  ·
    refine ⟨54241468517122579993944449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 144643916045660213317185197 54241468517122579993944449)
    ·
      refine ⟨40681101387841934995458337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54241468517122579993944449 40681101387841934995458337)
      ·
        refine ⟨30510826040881451246593753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40681101387841934995458337 30510826040881451246593753)
        ·
          refine ⟨22883119530661088434945315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30510826040881451246593753 22883119530661088434945315)
          ·
            refine ⟨34324679295991632652417973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22883119530661088434945315 34324679295991632652417973)
            ·
              refine ⟨3217938683999215561164185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 34324679295991632652417973 3217938683999215561164185)
              ·
                refine ⟨2413454012999411670873139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3217938683999215561164185 2413454012999411670873139)
                ·
                  refine ⟨3620181019499117506309709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2413454012999411670873139 3620181019499117506309709)
                  ·
                    refine ⟨1357567882312169064866141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3620181019499117506309709 1357567882312169064866141)
                    ·
                      rfl

theorem cell22_3965781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 5, 2, 1, 3].length) (baseStart_3965781 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3965781 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3965781 prefixEnd_3965781 := by exact prefixLift 3965781
  have htrace : WordTrace (prefixWord ++ tailWord_3965781) baseStart_3965781 baseEnd_3965781 := by
    simpa [prefixWord, tailWord_3965781, baseEnd_3965781] using wordTrace_append hprefix tailTrace_3965781
  have hstable : (prefixWord ++ tailWord_3965781).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3965781).length < 2 ^ (prefixWord ++ tailWord_3965781).sum := by decide
  have hdescent : baseEnd_3965781 < baseStart_3965781 := by decide
  rcases family_descends (prefixWord ++ tailWord_3965781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3965794 : List Nat := [3, 3, 2, 1, 3, 1, 1, 3, 5]
def baseStart_3965794 : Nat := 118140960795 + 3965794 * 2 ^ 59
def prefixEnd_3965794 : Nat := 4983230072969 + 3 ^ 40 * 3965794 * 2
def baseEnd_3965794 : Nat := 452524110825947121430367

theorem tailTrace_3965794 : CollatzResearch.WordTrace tailWord_3965794 prefixEnd_3965794 452524110825947121430367 := by
  unfold tailWord_3965794
  simp only [CollatzResearch.WordTrace]
  refine ⟨36161097548653279134352109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96429593463075411024938957 36161097548653279134352109)
  ·
    refine ⟨13560411580744979675382041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36161097548653279134352109 13560411580744979675382041)
    ·
      refine ⟨10170308685558734756536531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13560411580744979675382041 10170308685558734756536531)
      ·
        refine ⟨15255463028338102134804797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10170308685558734756536531 15255463028338102134804797)
        ·
          refine ⟨5720798635626788300551799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15255463028338102134804797 5720798635626788300551799)
          ·
            refine ⟨8581197953440182450827699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5720798635626788300551799 8581197953440182450827699)
            ·
              refine ⟨12871796930160273676241549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8581197953440182450827699 12871796930160273676241549)
              ·
                refine ⟨4826923848810102628590581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12871796930160273676241549 4826923848810102628590581)
                ·
                  refine ⟨452524110825947121430367, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4826923848810102628590581 452524110825947121430367)
                  ·
                    rfl

theorem cell22_3965794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 1, 3, 5].length) (baseStart_3965794 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3965794 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3965794 prefixEnd_3965794 := by exact prefixLift 3965794
  have htrace : WordTrace (prefixWord ++ tailWord_3965794) baseStart_3965794 baseEnd_3965794 := by
    simpa [prefixWord, tailWord_3965794, baseEnd_3965794] using wordTrace_append hprefix tailTrace_3965794
  have hstable : (prefixWord ++ tailWord_3965794).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3965794).length < 2 ^ (prefixWord ++ tailWord_3965794).sum := by decide
  have hdescent : baseEnd_3965794 < baseStart_3965794 := by decide
  rcases family_descends (prefixWord ++ tailWord_3965794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3965805 : List Nat := [1, 5, 1, 1, 1, 1, 1, 3, 8]
def baseStart_3965805 : Nat := 118140960795 + 3965805 * 2 ^ 59
def prefixEnd_3965805 : Nat := 4983230072969 + 3 ^ 40 * 3965805 * 2
def baseEnd_3965805 : Nat := 452525366000880334088689

theorem tailTrace_3965805 : CollatzResearch.WordTrace tailWord_3965805 prefixEnd_3965805 452525366000880334088689 := by
  unfold tailWord_3965805
  simp only [CollatzResearch.WordTrace]
  refine ⟨144644791397573265416058869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96429860931715510277372579 144644791397573265416058869)
  ·
    refine ⟨13560449193522493632755519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 144644791397573265416058869 13560449193522493632755519)
    ·
      refine ⟨20340673790283740449133279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13560449193522493632755519 20340673790283740449133279)
      ·
        refine ⟨30511010685425610673699919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20340673790283740449133279 30511010685425610673699919)
        ·
          refine ⟨45766516028138416010549879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30511010685425610673699919 45766516028138416010549879)
          ·
            refine ⟨68649774042207624015824819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45766516028138416010549879 68649774042207624015824819)
            ·
              refine ⟨102974661063311436023737229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68649774042207624015824819 102974661063311436023737229)
              ·
                refine ⟨38615497898741788508901461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 102974661063311436023737229 38615497898741788508901461)
                ·
                  refine ⟨452525366000880334088689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 38615497898741788508901461 452525366000880334088689)
                  ·
                    rfl

theorem cell22_3965805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 3, 8].length) (baseStart_3965805 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3965805 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3965805 prefixEnd_3965805 := by exact prefixLift 3965805
  have htrace : WordTrace (prefixWord ++ tailWord_3965805) baseStart_3965805 baseEnd_3965805 := by
    simpa [prefixWord, tailWord_3965805, baseEnd_3965805] using wordTrace_append hprefix tailTrace_3965805
  have hstable : (prefixWord ++ tailWord_3965805).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3965805).length < 2 ^ (prefixWord ++ tailWord_3965805).sum := by decide
  have hdescent : baseEnd_3965805 < baseStart_3965805 := by decide
  rcases family_descends (prefixWord ++ tailWord_3965805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3965882 : List Nat := [3, 1, 1, 1, 2, 1, 3, 2, 5, 3]
def baseStart_3965882 : Nat := 118140960795 + 3965882 * 2 ^ 59
def prefixEnd_3965882 : Nat := 4983230072969 + 3 ^ 40 * 3965882 * 2
def baseEnd_3965882 : Nat := 1357602456676238468090831

theorem tailTrace_3965882 : CollatzResearch.WordTrace tailWord_3965882 prefixEnd_3965882 1357602456676238468090831 := by
  unfold tailWord_3965882
  simp only [CollatzResearch.WordTrace]
  refine ⟨36161899954573576891652975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96431733212196205044407933 36161899954573576891652975)
  ·
    refine ⟨54242849931860365337479463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36161899954573576891652975 54242849931860365337479463)
    ·
      refine ⟨81364274897790548006219195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54242849931860365337479463 81364274897790548006219195)
      ·
        refine ⟨122046412346685822009328793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81364274897790548006219195 122046412346685822009328793)
        ·
          refine ⟨91534809260014366506996595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122046412346685822009328793 91534809260014366506996595)
          ·
            refine ⟨137302213890021549760494893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91534809260014366506996595 137302213890021549760494893)
            ·
              refine ⟨51488330208758081160185585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 137302213890021549760494893 51488330208758081160185585)
              ·
                refine ⟨38616247656568560870139189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51488330208758081160185585 38616247656568560870139189)
                ·
                  refine ⟨3620273217803302581575549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 38616247656568560870139189 3620273217803302581575549)
                  ·
                    refine ⟨1357602456676238468090831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3620273217803302581575549 1357602456676238468090831)
                    ·
                      rfl

theorem cell22_3965882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 2, 5, 3].length) (baseStart_3965882 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3965882 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3965882 prefixEnd_3965882 := by exact prefixLift 3965882
  have htrace : WordTrace (prefixWord ++ tailWord_3965882) baseStart_3965882 baseEnd_3965882 := by
    simpa [prefixWord, tailWord_3965882, baseEnd_3965882] using wordTrace_append hprefix tailTrace_3965882
  have hstable : (prefixWord ++ tailWord_3965882).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3965882).length < 2 ^ (prefixWord ++ tailWord_3965882).sum := by decide
  have hdescent : baseEnd_3965882 < baseStart_3965882 := by decide
  rcases family_descends (prefixWord ++ tailWord_3965882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3965899 : List Nat := [1, 1, 1, 1, 3, 6, 2, 1, 3, 3]
def baseStart_3965899 : Nat := 118140960795 + 3965899 * 2 ^ 59
def prefixEnd_3965899 : Nat := 4983230072969 + 3 ^ 40 * 3965899 * 2
def baseEnd_3965899 : Nat := 1357608276123656090415779

theorem tailTrace_3965899 : CollatzResearch.WordTrace tailWord_3965899 prefixEnd_3965899 1357608276123656090415779 := by
  unfold tailWord_3965899
  simp only [CollatzResearch.WordTrace]
  refine ⟨144648219859232719469980751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96432146572821812979987167 144648219859232719469980751)
  ·
    refine ⟨216972329788849079204971127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144648219859232719469980751 216972329788849079204971127)
    ·
      refine ⟨325458494683273618807456691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216972329788849079204971127 325458494683273618807456691)
      ·
        refine ⟨488187742024910428211185037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 325458494683273618807456691 488187742024910428211185037)
        ·
          refine ⟨183070403259341410579194389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 488187742024910428211185037 183070403259341410579194389)
          ·
            refine ⟨8581425152781628620899737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 183070403259341410579194389 8581425152781628620899737)
            ·
              refine ⟨6436068864586221465674803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8581425152781628620899737 6436068864586221465674803)
              ·
                refine ⟨9654103296879332198512205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6436068864586221465674803 9654103296879332198512205)
                ·
                  refine ⟨3620288736329749574442077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9654103296879332198512205 3620288736329749574442077)
                  ·
                    refine ⟨1357608276123656090415779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3620288736329749574442077 1357608276123656090415779)
                    ·
                      rfl

theorem cell22_3965899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 2, 1, 3, 3].length) (baseStart_3965899 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3965899 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3965899 prefixEnd_3965899 := by exact prefixLift 3965899
  have htrace : WordTrace (prefixWord ++ tailWord_3965899) baseStart_3965899 baseEnd_3965899 := by
    simpa [prefixWord, tailWord_3965899, baseEnd_3965899] using wordTrace_append hprefix tailTrace_3965899
  have hstable : (prefixWord ++ tailWord_3965899).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3965899).length < 2 ^ (prefixWord ++ tailWord_3965899).sum := by decide
  have hdescent : baseEnd_3965899 < baseStart_3965899 := by decide
  rcases family_descends (prefixWord ++ tailWord_3965899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3965950 : List Nat := [4, 2, 2, 2, 3, 1, 1, 1, 3, 3]
def baseStart_3965950 : Nat := 118140960795 + 3965950 * 2 ^ 59
def prefixEnd_3965950 : Nat := 4983230072969 + 3 ^ 40 * 3965950 * 2
def baseEnd_3965950 : Nat := 1357625734465908957390623

theorem tailTrace_3965950 : CollatzResearch.WordTrace tailWord_3965950 prefixEnd_3965950 1357625734465908957390623 := by
  unfold tailWord_3965950
  simp only [CollatzResearch.WordTrace]
  refine ⟨18081259997755994397510913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 96433386654698636786724869 18081259997755994397510913)
  ·
    refine ⟨13560944998316995798133185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18081259997755994397510913 13560944998316995798133185)
    ·
      refine ⟨10170708748737746848599889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13560944998316995798133185 10170708748737746848599889)
      ·
        refine ⟨7628031561553310136449917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10170708748737746848599889 7628031561553310136449917)
        ·
          refine ⟨2860511835582491301168719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7628031561553310136449917 2860511835582491301168719)
          ·
            refine ⟨4290767753373736951753079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2860511835582491301168719 4290767753373736951753079)
            ·
              refine ⟨6436151630060605427629619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4290767753373736951753079 6436151630060605427629619)
              ·
                refine ⟨9654227445090908141444429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6436151630060605427629619 9654227445090908141444429)
                ·
                  refine ⟨3620335291909090553041661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9654227445090908141444429 3620335291909090553041661)
                  ·
                    refine ⟨1357625734465908957390623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3620335291909090553041661 1357625734465908957390623)
                    ·
                      rfl

theorem cell22_3965950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 3, 1, 1, 1, 3, 3].length) (baseStart_3965950 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3965950 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3965950 prefixEnd_3965950 := by exact prefixLift 3965950
  have htrace : WordTrace (prefixWord ++ tailWord_3965950) baseStart_3965950 baseEnd_3965950 := by
    simpa [prefixWord, tailWord_3965950, baseEnd_3965950] using wordTrace_append hprefix tailTrace_3965950
  have hstable : (prefixWord ++ tailWord_3965950).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3965950).length < 2 ^ (prefixWord ++ tailWord_3965950).sum := by decide
  have hdescent : baseEnd_3965950 < baseStart_3965950 := by decide
  rcases family_descends (prefixWord ++ tailWord_3965950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3965976 : List Nat := [2, 1, 2, 3, 2, 4, 1, 2, 1, 4]
def baseStart_3965976 : Nat := 118140960795 + 3965976 * 2 ^ 59
def prefixEnd_3965976 : Nat := 4983230072969 + 3 ^ 40 * 3965976 * 2
def baseEnd_3965976 : Nat := 1357634634797253556240543

theorem tailTrace_3965976 : CollatzResearch.WordTrace tailWord_3965976 prefixEnd_3965976 1357634634797253556240543 := by
  unfold tailWord_3965976
  simp only [CollatzResearch.WordTrace]
  refine ⟨72325514139976880810266891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96434018853302507747022521 72325514139976880810266891)
  ·
    refine ⟨108488271209965321215400337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72325514139976880810266891 108488271209965321215400337)
    ·
      refine ⟨81366203407473990911550253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108488271209965321215400337 81366203407473990911550253)
      ·
        refine ⟨30512326277802746591831345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81366203407473990911550253 30512326277802746591831345)
        ·
          refine ⟨22884244708352059943873509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30512326277802746591831345 22884244708352059943873509)
          ·
            refine ⟨4290795882816011239476283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22884244708352059943873509 4290795882816011239476283)
            ·
              refine ⟨6436193824224016859214425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4290795882816011239476283 6436193824224016859214425)
              ·
                refine ⟨4827145368168012644410819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6436193824224016859214425 4827145368168012644410819)
                ·
                  refine ⟨7240718052252018966616229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4827145368168012644410819 7240718052252018966616229)
                  ·
                    refine ⟨1357634634797253556240543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7240718052252018966616229 1357634634797253556240543)
                    ·
                      rfl

theorem cell22_3965976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 4, 1, 2, 1, 4].length) (baseStart_3965976 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3965976 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3965976 prefixEnd_3965976 := by exact prefixLift 3965976
  have htrace : WordTrace (prefixWord ++ tailWord_3965976) baseStart_3965976 baseEnd_3965976 := by
    simpa [prefixWord, tailWord_3965976, baseEnd_3965976] using wordTrace_append hprefix tailTrace_3965976
  have hstable : (prefixWord ++ tailWord_3965976).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3965976).length < 2 ^ (prefixWord ++ tailWord_3965976).sum := by decide
  have hdescent : baseEnd_3965976 < baseStart_3965976 := by decide
  rcases family_descends (prefixWord ++ tailWord_3965976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3966008 : List Nat := [2, 1, 2, 1, 5, 3, 2, 2, 4]
def baseStart_3966008 : Nat := 118140960795 + 3966008 * 2 ^ 59
def prefixEnd_3966008 : Nat := 4983230072969 + 3 ^ 40 * 3966008 * 2
def baseEnd_3966008 : Nat := 452548529683738713146815

theorem tailTrace_3966008 : CollatzResearch.WordTrace tailWord_3966008 prefixEnd_3966008 452548529683738713146815 := by
  unfold tailWord_3966008
  simp only [CollatzResearch.WordTrace]
  refine ⟨72326097707918915542849339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96434796943891887390465785 72326097707918915542849339)
  ·
    refine ⟨108489146561878373314274009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72326097707918915542849339 108489146561878373314274009)
    ·
      refine ⟨81366859921408779985705507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108489146561878373314274009 81366859921408779985705507)
      ·
        refine ⟨122050289882113169978558261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81366859921408779985705507 122050289882113169978558261)
        ·
          refine ⟨11442214676448109685489837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 122050289882113169978558261 11442214676448109685489837)
          ·
            refine ⟨4290830503668041132058689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11442214676448109685489837 4290830503668041132058689)
            ·
              refine ⟨3218122877751030849044017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4290830503668041132058689 3218122877751030849044017)
              ·
                refine ⟨2413592158313273136783013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3218122877751030849044017 2413592158313273136783013)
                ·
                  refine ⟨452548529683738713146815, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2413592158313273136783013 452548529683738713146815)
                  ·
                    rfl

theorem cell22_3966008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 3, 2, 2, 4].length) (baseStart_3966008 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3966008 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3966008 prefixEnd_3966008 := by exact prefixLift 3966008
  have htrace : WordTrace (prefixWord ++ tailWord_3966008) baseStart_3966008 baseEnd_3966008 := by
    simpa [prefixWord, tailWord_3966008, baseEnd_3966008] using wordTrace_append hprefix tailTrace_3966008
  have hstable : (prefixWord ++ tailWord_3966008).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3966008).length < 2 ^ (prefixWord ++ tailWord_3966008).sum := by decide
  have hdescent : baseEnd_3966008 < baseStart_3966008 := by decide
  rcases family_descends (prefixWord ++ tailWord_3966008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3966038 : List Nat := [5, 2, 2, 1, 2, 1, 1, 1, 1, 6]
def baseStart_3966038 : Nat := 118140960795 + 3966038 * 2 ^ 59
def prefixEnd_3966038 : Nat := 4983230072969 + 3 ^ 40 * 3966038 * 2
def baseEnd_3966038 : Nat := 1357655858664306061190353

theorem tailTrace_3966038 : CollatzResearch.WordTrace tailWord_3966038 prefixEnd_3966038 1357655858664306061190353 := by
  unfold tailWord_3966038
  simp only [CollatzResearch.WordTrace]
  refine ⟨9040830600358071638080673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 96435526403819430806193845 9040830600358071638080673)
  ·
    refine ⟨6780622950268553728560505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9040830600358071638080673 6780622950268553728560505)
    ·
      refine ⟨5085467212701415296420379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6780622950268553728560505 5085467212701415296420379)
      ·
        refine ⟨7628200819052122944630569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5085467212701415296420379 7628200819052122944630569)
        ·
          refine ⟨5721150614289092208472927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7628200819052122944630569 5721150614289092208472927)
          ·
            refine ⟨8581725921433638312709391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5721150614289092208472927 8581725921433638312709391)
            ·
              refine ⟨12872588882150457469064087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8581725921433638312709391 12872588882150457469064087)
              ·
                refine ⟨19308883323225686203596131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12872588882150457469064087 19308883323225686203596131)
                ·
                  refine ⟨28963324984838529305394197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19308883323225686203596131 28963324984838529305394197)
                  ·
                    refine ⟨1357655858664306061190353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28963324984838529305394197 1357655858664306061190353)
                    ·
                      rfl

theorem cell22_3966038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 1, 1, 1, 6].length) (baseStart_3966038 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3966038 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3966038 prefixEnd_3966038 := by exact prefixLift 3966038
  have htrace : WordTrace (prefixWord ++ tailWord_3966038) baseStart_3966038 baseEnd_3966038 := by
    simpa [prefixWord, tailWord_3966038, baseEnd_3966038] using wordTrace_append hprefix tailTrace_3966038
  have hstable : (prefixWord ++ tailWord_3966038).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3966038).length < 2 ^ (prefixWord ++ tailWord_3966038).sum := by decide
  have hdescent : baseEnd_3966038 < baseStart_3966038 := by decide
  rcases family_descends (prefixWord ++ tailWord_3966038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3966047 : List Nat := [1, 1, 2, 3, 1, 1, 4, 2, 7]
def baseStart_3966047 : Nat := 118140960795 + 3966047 * 2 ^ 59
def prefixEnd_3966047 : Nat := 4983230072969 + 3 ^ 40 * 3966047 * 2
def baseEnd_3966047 : Nat := 452552979849411012571775

theorem tailTrace_3966047 : CollatzResearch.WordTrace tailWord_3966047 prefixEnd_3966047 452552979849411012571775 := by
  unfold tailWord_3966047
  simp only [CollatzResearch.WordTrace]
  refine ⟨144653617862696540746368395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96435745241797693830912263 144653617862696540746368395)
  ·
    refine ⟨216980426794044811119552593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144653617862696540746368395 216980426794044811119552593)
    ·
      refine ⟨162735320095533608339664445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 216980426794044811119552593 162735320095533608339664445)
      ·
        refine ⟨61025745035825103127374167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 162735320095533608339664445 61025745035825103127374167)
        ·
          refine ⟨91538617553737654691061251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61025745035825103127374167 91538617553737654691061251)
          ·
            refine ⟨137307926330606482036591877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91538617553737654691061251 137307926330606482036591877)
            ·
              refine ⟨25745236186988715381860977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 137307926330606482036591877 25745236186988715381860977)
              ·
                refine ⟨19308927140241536536395733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25745236186988715381860977 19308927140241536536395733)
                ·
                  refine ⟨452552979849411012571775, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19308927140241536536395733 452552979849411012571775)
                  ·
                    rfl

theorem cell22_3966047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 4, 2, 7].length) (baseStart_3966047 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3966047 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3966047 prefixEnd_3966047 := by exact prefixLift 3966047
  have htrace : WordTrace (prefixWord ++ tailWord_3966047) baseStart_3966047 baseEnd_3966047 := by
    simpa [prefixWord, tailWord_3966047, baseEnd_3966047] using wordTrace_append hprefix tailTrace_3966047
  have hstable : (prefixWord ++ tailWord_3966047).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3966047).length < 2 ^ (prefixWord ++ tailWord_3966047).sum := by decide
  have hdescent : baseEnd_3966047 < baseStart_3966047 := by decide
  rcases family_descends (prefixWord ++ tailWord_3966047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3966145 : List Nat := [1, 2, 6, 1, 1, 3, 1, 2, 1, 4]
def baseStart_3966145 : Nat := 118140960795 + 3966145 * 2 ^ 59
def prefixEnd_3966145 : Nat := 4983230072969 + 3 ^ 40 * 3966145 * 2
def baseEnd_3966145 : Nat := 1357692486950993448765025

theorem tailTrace_3966145 : CollatzResearch.WordTrace tailWord_3966145 prefixEnd_3966145 1357692486950993448765025 := by
  unfold tailWord_3966145
  simp only [CollatzResearch.WordTrace]
  refine ⟨144657192216341503483435889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96438128144227668988957259 144657192216341503483435889)
  ·
    refine ⟨108492894162256127612576917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144657192216341503483435889 108492894162256127612576917)
    ·
      refine ⟨5085604413855755981839543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 108492894162256127612576917 5085604413855755981839543)
      ·
        refine ⟨7628406620783633972759315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5085604413855755981839543 7628406620783633972759315)
        ·
          refine ⟨11442609931175450959138973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7628406620783633972759315 11442609931175450959138973)
          ·
            refine ⟨4290978724190794109677115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11442609931175450959138973 4290978724190794109677115)
            ·
              refine ⟨6436468086286191164515673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4290978724190794109677115 6436468086286191164515673)
              ·
                refine ⟨4827351064714643373386755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6436468086286191164515673 4827351064714643373386755)
                ·
                  refine ⟨7241026597071965060080133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4827351064714643373386755 7241026597071965060080133)
                  ·
                    refine ⟨1357692486950993448765025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7241026597071965060080133 1357692486950993448765025)
                    ·
                      rfl

theorem cell22_3966145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 3, 1, 2, 1, 4].length) (baseStart_3966145 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3966145 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3966145 prefixEnd_3966145 := by exact prefixLift 3966145
  have htrace : WordTrace (prefixWord ++ tailWord_3966145) baseStart_3966145 baseEnd_3966145 := by
    simpa [prefixWord, tailWord_3966145, baseEnd_3966145] using wordTrace_append hprefix tailTrace_3966145
  have hstable : (prefixWord ++ tailWord_3966145).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3966145).length < 2 ^ (prefixWord ++ tailWord_3966145).sum := by decide
  have hdescent : baseEnd_3966145 < baseStart_3966145 := by decide
  rcases family_descends (prefixWord ++ tailWord_3966145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3966154 : List Nat := [3, 1, 2, 1, 3, 2, 2, 8]
def baseStart_3966154 : Nat := 118140960795 + 3966154 * 2 ^ 59
def prefixEnd_3966154 : Nat := 4983230072969 + 3 ^ 40 * 3966154 * 2
def baseEnd_3966154 : Nat := 150855063092768936143333

theorem tailTrace_3966154 : CollatzResearch.WordTrace tailWord_3966154 prefixEnd_3966154 150855063092768936143333 := by
  unfold tailWord_3966154
  simp only [CollatzResearch.WordTrace]
  refine ⟨36164380118327224505128379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96438346982205932013675677 36164380118327224505128379)
  ·
    refine ⟨54246570177490836757692569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36164380118327224505128379 54246570177490836757692569)
    ·
      refine ⟨40684927633118127568269427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54246570177490836757692569 40684927633118127568269427)
      ·
        refine ⟨61027391449677191352404141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40684927633118127568269427 61027391449677191352404141)
        ·
          refine ⟨22885271793628946757151553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61027391449677191352404141 22885271793628946757151553)
          ·
            refine ⟨17163953845221710067863665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22885271793628946757151553 17163953845221710067863665)
            ·
              refine ⟨12872965383916282550897749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17163953845221710067863665 12872965383916282550897749)
              ·
                refine ⟨150855063092768936143333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12872965383916282550897749 150855063092768936143333)
                ·
                  rfl

theorem cell22_3966154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 2, 8].length) (baseStart_3966154 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3966154 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3966154 prefixEnd_3966154 := by exact prefixLift 3966154
  have htrace : WordTrace (prefixWord ++ tailWord_3966154) baseStart_3966154 baseEnd_3966154 := by
    simpa [prefixWord, tailWord_3966154, baseEnd_3966154] using wordTrace_append hprefix tailTrace_3966154
  have hstable : (prefixWord ++ tailWord_3966154).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3966154).length < 2 ^ (prefixWord ++ tailWord_3966154).sum := by decide
  have hdescent : baseEnd_3966154 < baseStart_3966154 := by decide
  rcases family_descends (prefixWord ++ tailWord_3966154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3966184 : List Nat := [2, 1, 4, 1, 2, 1, 1, 1, 1, 8]
def baseStart_3966184 : Nat := 118140960795 + 3966184 * 2 ^ 59
def prefixEnd_3966184 : Nat := 4983230072969 + 3 ^ 40 * 3966184 * 2
def baseEnd_3966184 : Nat := 1357705837448010347039905

theorem tailTrace_3966184 : CollatzResearch.WordTrace tailWord_3966184 prefixEnd_3966184 1357705837448010347039905 := by
  unfold tailWord_3966184
  simp only [CollatzResearch.WordTrace]
  refine ⟨72329307331600106572052803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96439076442133475429403737 72329307331600106572052803)
  ·
    refine ⟨108493960997400159858079205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72329307331600106572052803 108493960997400159858079205)
    ·
      refine ⟨20342617687012529973389851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 108493960997400159858079205 20342617687012529973389851)
      ·
        refine ⟨30513926530518794960084777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20342617687012529973389851 30513926530518794960084777)
        ·
          refine ⟨22885444897889096220063583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30513926530518794960084777 22885444897889096220063583)
          ·
            refine ⟨34328167346833644330095375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22885444897889096220063583 34328167346833644330095375)
            ·
              refine ⟨51492251020250466495143063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34328167346833644330095375 51492251020250466495143063)
              ·
                refine ⟨77238376530375699742714595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51492251020250466495143063 77238376530375699742714595)
                ·
                  refine ⟨115857564795563549614071893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 77238376530375699742714595 115857564795563549614071893)
                  ·
                    refine ⟨1357705837448010347039905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 115857564795563549614071893 1357705837448010347039905)
                    ·
                      rfl

theorem cell22_3966184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 1, 1, 8].length) (baseStart_3966184 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3966184 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3966184 prefixEnd_3966184 := by exact prefixLift 3966184
  have htrace : WordTrace (prefixWord ++ tailWord_3966184) baseStart_3966184 baseEnd_3966184 := by
    simpa [prefixWord, tailWord_3966184, baseEnd_3966184] using wordTrace_append hprefix tailTrace_3966184
  have hstable : (prefixWord ++ tailWord_3966184).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3966184).length < 2 ^ (prefixWord ++ tailWord_3966184).sum := by decide
  have hdescent : baseEnd_3966184 < baseStart_3966184 := by decide
  rcases family_descends (prefixWord ++ tailWord_3966184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3966220 : List Nat := [2, 2, 1, 2, 2, 4, 2, 3, 1, 3]
def baseStart_3966220 : Nat := 118140960795 + 3966220 * 2 ^ 59
def prefixEnd_3966220 : Nat := 4983230072969 + 3 ^ 40 * 3966220 * 2
def baseEnd_3966220 : Nat := 1357718160983718253139795

theorem tailTrace_3966220 : CollatzResearch.WordTrace tailWord_3966220 prefixEnd_3966220 1357718160983718253139795 := by
  unfold tailWord_3966220
  simp only [CollatzResearch.WordTrace]
  refine ⟨72329963845534895646208057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96439951794046527528277409 72329963845534895646208057)
  ·
    refine ⟨54247472884151171734656043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72329963845534895646208057 54247472884151171734656043)
    ·
      refine ⟨81371209326226757601984065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54247472884151171734656043 81371209326226757601984065)
      ·
        refine ⟨61028406994670068201488049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81371209326226757601984065 61028406994670068201488049)
        ·
          refine ⟨45771305246002551151116037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61028406994670068201488049 45771305246002551151116037)
          ·
            refine ⟨8582119733625478340834257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45771305246002551151116037 8582119733625478340834257)
            ·
              refine ⟨6436589800219108755625693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8582119733625478340834257 6436589800219108755625693)
              ·
                refine ⟨2413721175082165783359635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6436589800219108755625693 2413721175082165783359635)
                ·
                  refine ⟨3620581762623248675039453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2413721175082165783359635 3620581762623248675039453)
                  ·
                    refine ⟨1357718160983718253139795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3620581762623248675039453 1357718160983718253139795)
                    ·
                      rfl

theorem cell22_3966220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 2, 3, 1, 3].length) (baseStart_3966220 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3966220 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3966220 prefixEnd_3966220 := by exact prefixLift 3966220
  have htrace : WordTrace (prefixWord ++ tailWord_3966220) baseStart_3966220 baseEnd_3966220 := by
    simpa [prefixWord, tailWord_3966220, baseEnd_3966220] using wordTrace_append hprefix tailTrace_3966220
  have hstable : (prefixWord ++ tailWord_3966220).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3966220).length < 2 ^ (prefixWord ++ tailWord_3966220).sum := by decide
  have hdescent : baseEnd_3966220 < baseStart_3966220 := by decide
  rcases family_descends (prefixWord ++ tailWord_3966220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3966250 : List Nat := [3, 1, 4, 2, 1, 2, 3, 1, 5]
def baseStart_3966250 : Nat := 118140960795 + 3966250 * 2 ^ 59
def prefixEnd_3966250 : Nat := 4983230072969 + 3 ^ 40 * 3966250 * 2
def baseEnd_3966250 : Nat := 452576143532269391629901

theorem tailTrace_3966250 : CollatzResearch.WordTrace tailWord_3966250 prefixEnd_3966250 452576143532269391629901 := by
  unfold tailWord_3966250
  simp only [CollatzResearch.WordTrace]
  refine ⟨36165255470240276604002051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96440681253974070944005469 36165255470240276604002051)
  ·
    refine ⟨54247883205360414906003077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36165255470240276604002051 54247883205360414906003077)
    ·
      refine ⟨10171478101005077794875577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 54247883205360414906003077 10171478101005077794875577)
      ·
        refine ⟨7628608575753808346156683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10171478101005077794875577 7628608575753808346156683)
        ·
          refine ⟨11442912863630712519235025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7628608575753808346156683 11442912863630712519235025)
          ·
            refine ⟨8582184647723034389426269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11442912863630712519235025 8582184647723034389426269)
            ·
              refine ⟨3218319242896137896034851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8582184647723034389426269 3218319242896137896034851)
              ·
                refine ⟨4827478864344206844052277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3218319242896137896034851 4827478864344206844052277)
                ·
                  refine ⟨452576143532269391629901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4827478864344206844052277 452576143532269391629901)
                  ·
                    rfl

theorem cell22_3966250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 3, 1, 5].length) (baseStart_3966250 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3966250 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3966250 prefixEnd_3966250 := by exact prefixLift 3966250
  have htrace : WordTrace (prefixWord ++ tailWord_3966250) baseStart_3966250 baseEnd_3966250 := by
    simpa [prefixWord, tailWord_3966250, baseEnd_3966250] using wordTrace_append hprefix tailTrace_3966250
  have hstable : (prefixWord ++ tailWord_3966250).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3966250).length < 2 ^ (prefixWord ++ tailWord_3966250).sum := by decide
  have hdescent : baseEnd_3966250 < baseStart_3966250 := by decide
  rcases family_descends (prefixWord ++ tailWord_3966250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3966261 : List Nat := [1, 3, 3, 1, 2, 2, 2, 2, 6]
def baseStart_3966261 : Nat := 118140960795 + 3966261 * 2 ^ 59
def prefixEnd_3966261 : Nat := 4983230072969 + 3 ^ 40 * 3966261 * 2
def baseEnd_3966261 : Nat := 452577398707202604288223

theorem tailTrace_3966261 : CollatzResearch.WordTrace tailWord_3966261 prefixEnd_3966261 452577398707202604288223 := by
  unfold tailWord_3966261
  simp only [CollatzResearch.WordTrace]
  refine ⟨144661423083921255294658637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96440948722614170196439091 144661423083921255294658637)
  ·
    refine ⟨54248033656470470735496989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 144661423083921255294658637 54248033656470470735496989)
    ·
      refine ⟨20343012621176426525811371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54248033656470470735496989 20343012621176426525811371)
      ·
        refine ⟨30514518931764639788717057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20343012621176426525811371 30514518931764639788717057)
        ·
          refine ⟨22885889198823479841537793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30514518931764639788717057 22885889198823479841537793)
          ·
            refine ⟨17164416899117609881153345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22885889198823479841537793 17164416899117609881153345)
            ·
              refine ⟨12873312674338207410865009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17164416899117609881153345 12873312674338207410865009)
              ·
                refine ⟨9654984505753655558148757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12873312674338207410865009 9654984505753655558148757)
                ·
                  refine ⟨452577398707202604288223, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9654984505753655558148757 452577398707202604288223)
                  ·
                    rfl

theorem cell22_3966261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 2, 2, 6].length) (baseStart_3966261 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3966261 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3966261 prefixEnd_3966261 := by exact prefixLift 3966261
  have htrace : WordTrace (prefixWord ++ tailWord_3966261) baseStart_3966261 baseEnd_3966261 := by
    simpa [prefixWord, tailWord_3966261, baseEnd_3966261] using wordTrace_append hprefix tailTrace_3966261
  have hstable : (prefixWord ++ tailWord_3966261).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3966261).length < 2 ^ (prefixWord ++ tailWord_3966261).sum := by decide
  have hdescent : baseEnd_3966261 < baseStart_3966261 := by decide
  rcases family_descends (prefixWord ++ tailWord_3966261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3966291 : List Nat := [1, 1, 1, 2, 1, 1, 7, 2, 2, 4]
def baseStart_3966291 : Nat := 118140960795 + 3966291 * 2 ^ 59
def prefixEnd_3966291 : Nat := 4983230072969 + 3 ^ 40 * 3966291 * 2
def baseEnd_3966291 : Nat := 1357742465734697734614577

theorem tailTrace_3966291 : CollatzResearch.WordTrace tailWord_3966291 prefixEnd_3966291 1357742465734697734614577 := by
  unfold tailWord_3966291
  simp only [CollatzResearch.WordTrace]
  refine ⟨144662517273812570418250727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96441678182541713612167151 144662517273812570418250727)
  ·
    refine ⟨216993775910718855627376091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144662517273812570418250727 216993775910718855627376091)
    ·
      refine ⟨325490663866078283441064137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216993775910718855627376091 325490663866078283441064137)
      ·
        refine ⟨244117997899558712580798103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 325490663866078283441064137 244117997899558712580798103)
        ·
          refine ⟨366176996849338068871197155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 244117997899558712580798103 366176996849338068871197155)
          ·
            refine ⟨549265495274007103306795733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 366176996849338068871197155 549265495274007103306795733)
            ·
              refine ⟨12873410045484541483753025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 549265495274007103306795733 12873410045484541483753025)
              ·
                refine ⟨9655057534113406112814769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12873410045484541483753025 9655057534113406112814769)
                ·
                  refine ⟨7241293150585054584611077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9655057534113406112814769 7241293150585054584611077)
                  ·
                    refine ⟨1357742465734697734614577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7241293150585054584611077 1357742465734697734614577)
                    ·
                      rfl

theorem cell22_3966291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 7, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 7, 2, 2, 4].length) (baseStart_3966291 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3966291 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3966291 prefixEnd_3966291 := by exact prefixLift 3966291
  have htrace : WordTrace (prefixWord ++ tailWord_3966291) baseStart_3966291 baseEnd_3966291 := by
    simpa [prefixWord, tailWord_3966291, baseEnd_3966291] using wordTrace_append hprefix tailTrace_3966291
  have hstable : (prefixWord ++ tailWord_3966291).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3966291).length < 2 ^ (prefixWord ++ tailWord_3966291).sum := by decide
  have hdescent : baseEnd_3966291 < baseStart_3966291 := by decide
  rcases family_descends (prefixWord ++ tailWord_3966291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3966293 : List Nat := [1, 3, 2, 2, 3, 1, 2, 1, 4, 3]
def baseStart_3966293 : Nat := 118140960795 + 3966293 * 2 ^ 59
def prefixEnd_3966293 : Nat := 4983230072969 + 3 ^ 40 * 3966293 * 2
def baseEnd_3966293 : Nat := 1357743150375570396064571

theorem tailTrace_3966293 : CollatzResearch.WordTrace tailWord_3966293 prefixEnd_3966293 1357743150375570396064571 := by
  unfold tailWord_3966293
  simp only [CollatzResearch.WordTrace]
  refine ⟨144662590219805324759823533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96441726813203549839882355 144662590219805324759823533)
  ·
    refine ⟨54248471332426996784933825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 144662590219805324759823533 54248471332426996784933825)
    ·
      refine ⟨40686353499320247588700369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54248471332426996784933825 40686353499320247588700369)
      ·
        refine ⟨30514765124490185691525277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40686353499320247588700369 30514765124490185691525277)
        ·
          refine ⟨11443036921683819634321979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30514765124490185691525277 11443036921683819634321979)
          ·
            refine ⟨17164555382525729451482969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11443036921683819634321979 17164555382525729451482969)
            ·
              refine ⟨12873416536894297088612227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17164555382525729451482969 12873416536894297088612227)
              ·
                refine ⟨19310124805341445632918341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12873416536894297088612227 19310124805341445632918341)
                ·
                  refine ⟨3620648401001521056172189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19310124805341445632918341 3620648401001521056172189)
                  ·
                    refine ⟨1357743150375570396064571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3620648401001521056172189 1357743150375570396064571)
                    ·
                      rfl

theorem cell22_3966293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 2, 1, 4, 3].length) (baseStart_3966293 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3966293 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3966293 prefixEnd_3966293 := by exact prefixLift 3966293
  have htrace : WordTrace (prefixWord ++ tailWord_3966293) baseStart_3966293 baseEnd_3966293 := by
    simpa [prefixWord, tailWord_3966293, baseEnd_3966293] using wordTrace_append hprefix tailTrace_3966293
  have hstable : (prefixWord ++ tailWord_3966293).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3966293).length < 2 ^ (prefixWord ++ tailWord_3966293).sum := by decide
  have hdescent : baseEnd_3966293 < baseStart_3966293 := by decide
  rcases family_descends (prefixWord ++ tailWord_3966293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3966295 : List Nat := [1, 1, 3, 2, 3, 3, 3, 2, 4]
def baseStart_3966295 : Nat := 118140960795 + 3966295 * 2 ^ 59
def prefixEnd_3966295 : Nat := 4983230072969 + 3 ^ 40 * 3966295 * 2
def baseEnd_3966295 : Nat := 452581278338814352504855

theorem tailTrace_3966295 : CollatzResearch.WordTrace tailWord_3966295 prefixEnd_3966295 452581278338814352504855 := by
  unfold tailWord_3966295
  simp only [CollatzResearch.WordTrace]
  refine ⟨144662663165798079101396339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96441775443865386067597559 144662663165798079101396339)
  ·
    refine ⟨216993994748697118652094509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144662663165798079101396339 216993994748697118652094509)
    ·
      refine ⟨81372748030761419494535441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 216993994748697118652094509 81372748030761419494535441)
      ·
        refine ⟨61029561023071064620901581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81372748030761419494535441 61029561023071064620901581)
        ·
          refine ⟨22886085383651649232838093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61029561023071064620901581 22886085383651649232838093)
          ·
            refine ⟨8582282018869368462314285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22886085383651649232838093 8582282018869368462314285)
            ·
              refine ⟨3218355757076013173367857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8582282018869368462314285 3218355757076013173367857)
              ·
                refine ⟨2413766817807009880025893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3218355757076013173367857 2413766817807009880025893)
                ·
                  refine ⟨452581278338814352504855, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2413766817807009880025893 452581278338814352504855)
                  ·
                    rfl

theorem cell22_3966295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 3, 2, 4].length) (baseStart_3966295 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3966295 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3966295 prefixEnd_3966295 := by exact prefixLift 3966295
  have htrace : WordTrace (prefixWord ++ tailWord_3966295) baseStart_3966295 baseEnd_3966295 := by
    simpa [prefixWord, tailWord_3966295, baseEnd_3966295] using wordTrace_append hprefix tailTrace_3966295
  have hstable : (prefixWord ++ tailWord_3966295).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3966295).length < 2 ^ (prefixWord ++ tailWord_3966295).sum := by decide
  have hdescent : baseEnd_3966295 < baseStart_3966295 := by decide
  rcases family_descends (prefixWord ++ tailWord_3966295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3966301 : List Nat := [1, 4, 5, 1, 2, 1, 2, 1, 5]
def baseStart_3966301 : Nat := 118140960795 + 3966301 * 2 ^ 59
def prefixEnd_3966301 : Nat := 4983230072969 + 3 ^ 40 * 3966301 * 2
def baseEnd_3966301 : Nat := 452581962979687013954849

theorem tailTrace_3966301 : CollatzResearch.WordTrace tailWord_3966301 prefixEnd_3966301 452581962979687013954849 := by
  unfold tailWord_3966301
  simp only [CollatzResearch.WordTrace]
  refine ⟨144662882003776342126114757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96441921335850894750743171 144662882003776342126114757)
  ·
    refine ⟨27124290375708064148646517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 144662882003776342126114757 27124290375708064148646517)
    ·
      refine ⟨2542902222722631013935611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 27124290375708064148646517 2542902222722631013935611)
      ·
        refine ⟨3814353334083946520903417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2542902222722631013935611 3814353334083946520903417)
        ·
          refine ⟨2860765000562959890677563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3814353334083946520903417 2860765000562959890677563)
          ·
            refine ⟨4291147500844439836016345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2860765000562959890677563 4291147500844439836016345)
            ·
              refine ⟨3218360625633329877012259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4291147500844439836016345 3218360625633329877012259)
              ·
                refine ⟨4827540938449994815518389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3218360625633329877012259 4827540938449994815518389)
                ·
                  refine ⟨452581962979687013954849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4827540938449994815518389 452581962979687013954849)
                  ·
                    rfl

theorem cell22_3966301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 2, 1, 2, 1, 5].length) (baseStart_3966301 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3966301 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3966301 prefixEnd_3966301 := by exact prefixLift 3966301
  have htrace : WordTrace (prefixWord ++ tailWord_3966301) baseStart_3966301 baseEnd_3966301 := by
    simpa [prefixWord, tailWord_3966301, baseEnd_3966301] using wordTrace_append hprefix tailTrace_3966301
  have hstable : (prefixWord ++ tailWord_3966301).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3966301).length < 2 ^ (prefixWord ++ tailWord_3966301).sum := by decide
  have hdescent : baseEnd_3966301 < baseStart_3966301 := by decide
  rcases family_descends (prefixWord ++ tailWord_3966301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3966325 : List Nat := [1, 3, 4, 1, 3, 1, 2, 1, 2, 4]
def baseStart_3966325 : Nat := 118140960795 + 3966325 * 2 ^ 59
def prefixEnd_3966325 : Nat := 4983230072969 + 3 ^ 40 * 3966325 * 2
def baseEnd_3966325 : Nat := 1357754104629532979264473

theorem tailTrace_3966325 : CollatzResearch.WordTrace tailWord_3966325 prefixEnd_3966325 1357754104629532979264473 := by
  unfold tailWord_3966325
  simp only [CollatzResearch.WordTrace]
  refine ⟨144663757355689394224988429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96442504903792929483325619 144663757355689394224988429)
  ·
    refine ⟨54248909008383522834370661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 144663757355689394224988429 54248909008383522834370661)
    ·
      refine ⟨10171670439071910531444499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 54248909008383522834370661 10171670439071910531444499)
      ·
        refine ⟨15257505658607865797166749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10171670439071910531444499 15257505658607865797166749)
        ·
          refine ⟨5721564621977949673937531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15257505658607865797166749 5721564621977949673937531)
          ·
            refine ⟨8582346932966924510906297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5721564621977949673937531 8582346932966924510906297)
            ·
              refine ⟨6436760199725193383179723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8582346932966924510906297 6436760199725193383179723)
              ·
                refine ⟨9655140299587790074769585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6436760199725193383179723 9655140299587790074769585)
                ·
                  refine ⟨7241355224690842556077189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9655140299587790074769585 7241355224690842556077189)
                  ·
                    refine ⟨1357754104629532979264473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7241355224690842556077189 1357754104629532979264473)
                    ·
                      rfl

theorem cell22_3966325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 2, 1, 2, 4].length) (baseStart_3966325 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3966325 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3966325 prefixEnd_3966325 := by exact prefixLift 3966325
  have htrace : WordTrace (prefixWord ++ tailWord_3966325) baseStart_3966325 baseEnd_3966325 := by
    simpa [prefixWord, tailWord_3966325, baseEnd_3966325] using wordTrace_append hprefix tailTrace_3966325
  have hstable : (prefixWord ++ tailWord_3966325).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3966325).length < 2 ^ (prefixWord ++ tailWord_3966325).sum := by decide
  have hdescent : baseEnd_3966325 < baseStart_3966325 := by decide
  rcases family_descends (prefixWord ++ tailWord_3966325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3966411 : List Nat := [1, 1, 1, 1, 3, 3, 2, 2, 3, 5]
def baseStart_3966411 : Nat := 118140960795 + 3966411 * 2 ^ 59
def prefixEnd_3966411 : Nat := 4983230072969 + 3 ^ 40 * 3966411 * 2
def baseEnd_3966411 : Nat := 1357783544187057421614209

theorem tailTrace_3966411 : CollatzResearch.WordTrace tailWord_3966411 prefixEnd_3966411 1357783544187057421614209 := by
  unfold tailWord_3966411
  simp only [CollatzResearch.WordTrace]
  refine ⟨144666894033377830912619087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96444596022251887275079391 144666894033377830912619087)
  ·
    refine ⟨217000341050066746368928631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144666894033377830912619087 217000341050066746368928631)
    ·
      refine ⟨325500511575100119553392947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217000341050066746368928631 325500511575100119553392947)
      ·
        refine ⟨488250767362650179330089421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 325500511575100119553392947 488250767362650179330089421)
        ·
          refine ⟨183094037760993817248783533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 488250767362650179330089421 183094037760993817248783533)
          ·
            refine ⟨68660264160372681468293825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 183094037760993817248783533 68660264160372681468293825)
            ·
              refine ⟨51495198120279511101220369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68660264160372681468293825 51495198120279511101220369)
              ·
                refine ⟨38621398590209633325915277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51495198120279511101220369 38621398590209633325915277)
                ·
                  refine ⟨14483024471328612497218229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38621398590209633325915277 14483024471328612497218229)
                  ·
                    refine ⟨1357783544187057421614209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14483024471328612497218229 1357783544187057421614209)
                    ·
                      rfl

theorem cell22_3966411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 2, 3, 5].length) (baseStart_3966411 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3966411 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3966411 prefixEnd_3966411 := by exact prefixLift 3966411
  have htrace : WordTrace (prefixWord ++ tailWord_3966411) baseStart_3966411 baseEnd_3966411 := by
    simpa [prefixWord, tailWord_3966411, baseEnd_3966411] using wordTrace_append hprefix tailTrace_3966411
  have hstable : (prefixWord ++ tailWord_3966411).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3966411).length < 2 ^ (prefixWord ++ tailWord_3966411).sum := by decide
  have hdescent : baseEnd_3966411 < baseStart_3966411 := by decide
  rcases family_descends (prefixWord ++ tailWord_3966411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3966520 : List Nat := [2, 1, 2, 1, 4, 3, 2, 2, 5]
def baseStart_3966520 : Nat := 118140960795 + 3966520 * 2 ^ 59
def prefixEnd_3966520 : Nat := 4983230072969 + 3 ^ 40 * 3966520 * 2
def baseEnd_3966520 : Nat := 452606952371539156879625

theorem tailTrace_3966520 : CollatzResearch.WordTrace tailWord_3966520 prefixEnd_3966520 452606952371539156879625 := by
  unfold tailWord_3966520
  simp only [CollatzResearch.WordTrace]
  refine ⟨72335434794991471264168507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96447246393321961685558009 72335434794991471264168507)
  ·
    refine ⟨108503152192487206896252761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72335434794991471264168507 108503152192487206896252761)
    ·
      refine ⟨81377364144365405172189571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108503152192487206896252761 81377364144365405172189571)
      ·
        refine ⟨122066046216548107758284357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81377364144365405172189571 122066046216548107758284357)
        ·
          refine ⟨22887383665602770204678317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 122066046216548107758284357 22887383665602770204678317)
          ·
            refine ⟨8582768874601038826754369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22887383665602770204678317 8582768874601038826754369)
            ·
              refine ⟨6437076655950779120065777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8582768874601038826754369 6437076655950779120065777)
              ·
                refine ⟨4827807491963084340049333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6437076655950779120065777 4827807491963084340049333)
                ·
                  refine ⟨452606952371539156879625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4827807491963084340049333 452606952371539156879625)
                  ·
                    rfl

theorem cell22_3966520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 2, 2, 5].length) (baseStart_3966520 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3966520 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3966520 prefixEnd_3966520 := by exact prefixLift 3966520
  have htrace : WordTrace (prefixWord ++ tailWord_3966520) baseStart_3966520 baseEnd_3966520 := by
    simpa [prefixWord, tailWord_3966520, baseEnd_3966520] using wordTrace_append hprefix tailTrace_3966520
  have hstable : (prefixWord ++ tailWord_3966520).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3966520).length < 2 ^ (prefixWord ++ tailWord_3966520).sum := by decide
  have hdescent : baseEnd_3966520 < baseStart_3966520 := by decide
  rcases family_descends (prefixWord ++ tailWord_3966520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3966524 : List Nat := [2, 2, 2, 2, 4, 1, 1, 4, 1, 3]
def baseStart_3966524 : Nat := 118140960795 + 3966524 * 2 ^ 59
def prefixEnd_3966524 : Nat := 4983230072969 + 3 ^ 40 * 3966524 * 2
def baseEnd_3966524 : Nat := 1357822226396362793538863

theorem tailTrace_3966524 : CollatzResearch.WordTrace tailWord_3966524 prefixEnd_3966524 1357822226396362793538863 := by
  unfold tailWord_3966524
  simp only [CollatzResearch.WordTrace]
  refine ⟨72335507740984225605741313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96447343654645634140988417 72335507740984225605741313)
  ·
    refine ⟨54251630805738169204305985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72335507740984225605741313 54251630805738169204305985)
    ·
      refine ⟨40688723104303626903229489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54251630805738169204305985 40688723104303626903229489)
      ·
        refine ⟨30516542328227720177422117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40688723104303626903229489 30516542328227720177422117)
        ·
          refine ⟨5721851686542697533266647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30516542328227720177422117 5721851686542697533266647)
          ·
            refine ⟨8582777529814046299899971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5721851686542697533266647 8582777529814046299899971)
            ·
              refine ⟨12874166294721069449849957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8582777529814046299899971 12874166294721069449849957)
              ·
                refine ⟨2413906180260200521846867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12874166294721069449849957 2413906180260200521846867)
                ·
                  refine ⟨3620859270390300782770301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2413906180260200521846867 3620859270390300782770301)
                  ·
                    refine ⟨1357822226396362793538863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3620859270390300782770301 1357822226396362793538863)
                    ·
                      rfl

theorem cell22_3966524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 1, 4, 1, 3].length) (baseStart_3966524 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3966524 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3966524 prefixEnd_3966524 := by exact prefixLift 3966524
  have htrace : WordTrace (prefixWord ++ tailWord_3966524) baseStart_3966524 baseEnd_3966524 := by
    simpa [prefixWord, tailWord_3966524, baseEnd_3966524] using wordTrace_append hprefix tailTrace_3966524
  have hstable : (prefixWord ++ tailWord_3966524).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3966524).length < 2 ^ (prefixWord ++ tailWord_3966524).sum := by decide
  have hdescent : baseEnd_3966524 < baseStart_3966524 := by decide
  rcases family_descends (prefixWord ++ tailWord_3966524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3966533 : List Nat := [1, 3, 1, 1, 1, 4, 1, 1, 5, 4]
def baseStart_3966533 : Nat := 118140960795 + 3966533 * 2 ^ 59
def prefixEnd_3966533 : Nat := 4983230072969 + 3 ^ 40 * 3966533 * 2
def baseEnd_3966533 : Nat := 1357825307280289770063835

theorem tailTrace_3966533 : CollatzResearch.WordTrace tailWord_3966533 prefixEnd_3966533 1357825307280289770063835 := by
  unfold tailWord_3966533
  simp only [CollatzResearch.WordTrace]
  refine ⟨144671343738935845748560253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96447562492623897165706835 144671343738935845748560253)
  ·
    refine ⟨54251753902100942155710095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 144671343738935845748560253 54251753902100942155710095)
    ·
      refine ⟨81377630853151413233565143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54251753902100942155710095 81377630853151413233565143)
      ·
        refine ⟨122066446279727119850347715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81377630853151413233565143 122066446279727119850347715)
        ·
          refine ⟨183099669419590679775521573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122066446279727119850347715 183099669419590679775521573)
          ·
            refine ⟨34331188016173252457910295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 183099669419590679775521573 34331188016173252457910295)
            ·
              refine ⟨51496782024259878686865443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34331188016173252457910295 51496782024259878686865443)
              ·
                refine ⟨77245173036389818030298165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51496782024259878686865443 77245173036389818030298165)
                ·
                  refine ⟨7241734972161545440340453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 77245173036389818030298165 7241734972161545440340453)
                  ·
                    refine ⟨1357825307280289770063835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7241734972161545440340453 1357825307280289770063835)
                    ·
                      rfl

theorem cell22_3966533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 1, 5, 4].length) (baseStart_3966533 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3966533 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3966533 prefixEnd_3966533 := by exact prefixLift 3966533
  have htrace : WordTrace (prefixWord ++ tailWord_3966533) baseStart_3966533 baseEnd_3966533 := by
    simpa [prefixWord, tailWord_3966533, baseEnd_3966533] using wordTrace_append hprefix tailTrace_3966533
  have hstable : (prefixWord ++ tailWord_3966533).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3966533).length < 2 ^ (prefixWord ++ tailWord_3966533).sum := by decide
  have hdescent : baseEnd_3966533 < baseStart_3966533 := by decide
  rcases family_descends (prefixWord ++ tailWord_3966533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3966535 : List Nat := [1, 1, 4, 1, 5, 1, 1, 1, 2, 5]
def baseStart_3966535 : Nat := 118140960795 + 3966535 * 2 ^ 59
def prefixEnd_3966535 : Nat := 4983230072969 + 3 ^ 40 * 3966535 * 2
def baseEnd_3966535 : Nat := 1357825991921162431513829

theorem tailTrace_3966535 : CollatzResearch.WordTrace tailWord_3966535 prefixEnd_3966535 1357825991921162431513829 := by
  unfold tailWord_3966535
  simp only [CollatzResearch.WordTrace]
  refine ⟨144671416684928600090133059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96447611123285733393422039 144671416684928600090133059)
  ·
    refine ⟨217007125027392900135199589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144671416684928600090133059 217007125027392900135199589)
    ·
      refine ⟨40688835942636168775349923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 217007125027392900135199589 40688835942636168775349923)
      ·
        refine ⟨61033253913954253163024885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40688835942636168775349923 61033253913954253163024885)
        ·
          refine ⟨5721867554433211234033583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 61033253913954253163024885 5721867554433211234033583)
          ·
            refine ⟨8582801331649816851050375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5721867554433211234033583 8582801331649816851050375)
            ·
              refine ⟨12874201997474725276575563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8582801331649816851050375 12874201997474725276575563)
              ·
                refine ⟨19311302996212087914863345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12874201997474725276575563 19311302996212087914863345)
                ·
                  refine ⟨14483477247159065936147509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19311302996212087914863345 14483477247159065936147509)
                  ·
                    refine ⟨1357825991921162431513829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14483477247159065936147509 1357825991921162431513829)
                    ·
                      rfl

theorem cell22_3966535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 1, 1, 2, 5].length) (baseStart_3966535 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3966535 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3966535 prefixEnd_3966535 := by exact prefixLift 3966535
  have htrace : WordTrace (prefixWord ++ tailWord_3966535) baseStart_3966535 baseEnd_3966535 := by
    simpa [prefixWord, tailWord_3966535, baseEnd_3966535] using wordTrace_append hprefix tailTrace_3966535
  have hstable : (prefixWord ++ tailWord_3966535).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3966535).length < 2 ^ (prefixWord ++ tailWord_3966535).sum := by decide
  have hdescent : baseEnd_3966535 < baseStart_3966535 := by decide
  rcases family_descends (prefixWord ++ tailWord_3966535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3966567 : List Nat := [1, 1, 5, 1, 1, 1, 6, 1, 1, 4]
def baseStart_3966567 : Nat := 118140960795 + 3966567 * 2 ^ 59
def prefixEnd_3966567 : Nat := 4983230072969 + 3 ^ 40 * 3966567 * 2
def baseEnd_3966567 : Nat := 1357836946175125014713731

theorem tailTrace_3966567 : CollatzResearch.WordTrace tailWord_3966567 prefixEnd_3966567 1357836946175125014713731 := by
  unfold tailWord_3966567
  simp only [CollatzResearch.WordTrace]
  refine ⟨144672583820812669555297955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96448389213875113036865303 144672583820812669555297955)
  ·
    refine ⟨217008875731219004332946933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144672583820812669555297955 217008875731219004332946933)
    ·
      refine ⟨20344582099801781656213775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 217008875731219004332946933 20344582099801781656213775)
      ·
        refine ⟨30516873149702672484320663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20344582099801781656213775 30516873149702672484320663)
        ·
          refine ⟨45775309724554008726480995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30516873149702672484320663 45775309724554008726480995)
          ·
            refine ⟨68662964586831013089721493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45775309724554008726480995 68662964586831013089721493)
            ·
              refine ⟨3218576465007703738580695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 68662964586831013089721493 3218576465007703738580695)
              ·
                refine ⟨4827864697511555607871043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3218576465007703738580695 4827864697511555607871043)
                ·
                  refine ⟨7241797046267333411806565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4827864697511555607871043 7241797046267333411806565)
                  ·
                    refine ⟨1357836946175125014713731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7241797046267333411806565 1357836946175125014713731)
                    ·
                      rfl

theorem cell22_3966567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 6, 1, 1, 4].length) (baseStart_3966567 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3966567 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3966567 prefixEnd_3966567 := by exact prefixLift 3966567
  have htrace : WordTrace (prefixWord ++ tailWord_3966567) baseStart_3966567 baseEnd_3966567 := by
    simpa [prefixWord, tailWord_3966567, baseEnd_3966567] using wordTrace_append hprefix tailTrace_3966567
  have hstable : (prefixWord ++ tailWord_3966567).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3966567).length < 2 ^ (prefixWord ++ tailWord_3966567).sum := by decide
  have hdescent : baseEnd_3966567 < baseStart_3966567 := by decide
  rcases family_descends (prefixWord ++ tailWord_3966567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3966582 : List Nat := [5, 1, 1, 2, 2, 2, 2, 1, 6]
def baseStart_3966582 : Nat := 118140960795 + 3966582 * 2 ^ 59
def prefixEnd_3966582 : Nat := 4983230072969 + 3 ^ 40 * 3966582 * 2
def baseEnd_3966582 : Nat := 452614026993889991862895

theorem tailTrace_3966582 : CollatzResearch.WordTrace tailWord_3966582 prefixEnd_3966582 452614026993889991862895 := by
  unfold tailWord_3966582
  simp only [CollatzResearch.WordTrace]
  refine ⟨9042070682234895444818375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 96448753943838884744729333 9042070682234895444818375)
  ·
    refine ⟨13563106023352343167227563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9042070682234895444818375 13563106023352343167227563)
    ·
      refine ⟨20344659035028514750841345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13563106023352343167227563 20344659035028514750841345)
      ·
        refine ⟨15258494276271386063131009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20344659035028514750841345 15258494276271386063131009)
        ·
          refine ⟨11443870707203539547348257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15258494276271386063131009 11443870707203539547348257)
          ·
            refine ⟨8582903030402654660511193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11443870707203539547348257 8582903030402654660511193)
            ·
              refine ⟨6437177272801990995383395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8582903030402654660511193 6437177272801990995383395)
              ·
                refine ⟨9655765909202986493075093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6437177272801990995383395 9655765909202986493075093)
                ·
                  refine ⟨452614026993889991862895, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9655765909202986493075093 452614026993889991862895)
                  ·
                    rfl

theorem cell22_3966582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 2, 1, 6].length) (baseStart_3966582 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3966582 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3966582 prefixEnd_3966582 := by exact prefixLift 3966582
  have htrace : WordTrace (prefixWord ++ tailWord_3966582) baseStart_3966582 baseEnd_3966582 := by
    simpa [prefixWord, tailWord_3966582, baseEnd_3966582] using wordTrace_append hprefix tailTrace_3966582
  have hstable : (prefixWord ++ tailWord_3966582).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3966582).length < 2 ^ (prefixWord ++ tailWord_3966582).sum := by decide
  have hdescent : baseEnd_3966582 < baseStart_3966582 := by decide
  rcases family_descends (prefixWord ++ tailWord_3966582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3966642 : List Nat := [3, 2, 1, 1, 1, 2, 5, 1, 3, 3]
def baseStart_3966642 : Nat := 118140960795 + 3966642 * 2 ^ 59
def prefixEnd_3966642 : Nat := 4983230072969 + 3 ^ 40 * 3966642 * 2
def baseEnd_3966642 : Nat := 1357862620207849819088501

theorem tailTrace_3966642 : CollatzResearch.WordTrace tailWord_3966642 prefixEnd_3966642 1357862620207849819088501 := by
  unfold tailWord_3966642
  simp only [CollatzResearch.WordTrace]
  refine ⟨36168829823885239341069545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96450212863693971576185453 36168829823885239341069545)
  ·
    refine ⟨27126622367913929505802159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36168829823885239341069545 27126622367913929505802159)
    ·
      refine ⟨40689933551870894258703239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27126622367913929505802159 40689933551870894258703239)
      ·
        refine ⟨61034900327806341388054859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40689933551870894258703239 61034900327806341388054859)
        ·
          refine ⟨91552350491709512082082289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61034900327806341388054859 91552350491709512082082289)
          ·
            refine ⟨68664262868782134061561717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91552350491709512082082289 68664262868782134061561717)
            ·
              refine ⟨6437274643948325068271411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 68664262868782134061561717 6437274643948325068271411)
              ·
                refine ⟨9655911965922487602407117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6437274643948325068271411 9655911965922487602407117)
                ·
                  refine ⟨3620966987220932850902669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9655911965922487602407117 3620966987220932850902669)
                  ·
                    refine ⟨1357862620207849819088501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3620966987220932850902669 1357862620207849819088501)
                    ·
                      rfl

theorem cell22_3966642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 5, 1, 3, 3].length) (baseStart_3966642 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3966642 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3966642 prefixEnd_3966642 := by exact prefixLift 3966642
  have htrace : WordTrace (prefixWord ++ tailWord_3966642) baseStart_3966642 baseEnd_3966642 := by
    simpa [prefixWord, tailWord_3966642, baseEnd_3966642] using wordTrace_append hprefix tailTrace_3966642
  have hstable : (prefixWord ++ tailWord_3966642).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3966642).length < 2 ^ (prefixWord ++ tailWord_3966642).sum := by decide
  have hdescent : baseEnd_3966642 < baseStart_3966642 := by decide
  rcases family_descends (prefixWord ++ tailWord_3966642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3966655 : List Nat := [1, 1, 2, 2, 2, 3, 3, 3, 5]
def baseStart_3966655 : Nat := 118140960795 + 3966655 * 2 ^ 59
def prefixEnd_3966655 : Nat := 4983230072969 + 3 ^ 40 * 3966655 * 2
def baseEnd_3966655 : Nat := 452622356791174039504487

theorem tailTrace_3966655 : CollatzResearch.WordTrace tailWord_3966655 prefixEnd_3966655 452622356791174039504487 := by
  unfold tailWord_3966655
  simp only [CollatzResearch.WordTrace]
  refine ⟨144675793444493860584501419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96450528962995907056334279 144675793444493860584501419)
  ·
    refine ⟨217013690166740790876752129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144675793444493860584501419 217013690166740790876752129)
    ·
      refine ⟨162760267625055593157564097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 217013690166740790876752129 162760267625055593157564097)
      ·
        refine ⟨122070200718791694868173073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 162760267625055593157564097 122070200718791694868173073)
        ·
          refine ⟨91552650539093771151129805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122070200718791694868173073 91552650539093771151129805)
          ·
            refine ⟨34332243952160164181673677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 91552650539093771151129805 34332243952160164181673677)
            ·
              refine ⟨12874591482060061568127629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34332243952160164181673677 12874591482060061568127629)
              ·
                refine ⟨4827971805772523088047861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12874591482060061568127629 4827971805772523088047861)
                ·
                  refine ⟨452622356791174039504487, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4827971805772523088047861 452622356791174039504487)
                  ·
                    rfl

theorem cell22_3966655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 3, 3, 5].length) (baseStart_3966655 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3966655 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3966655 prefixEnd_3966655 := by exact prefixLift 3966655
  have htrace : WordTrace (prefixWord ++ tailWord_3966655) baseStart_3966655 baseEnd_3966655 := by
    simpa [prefixWord, tailWord_3966655, baseEnd_3966655] using wordTrace_append hprefix tailTrace_3966655
  have hstable : (prefixWord ++ tailWord_3966655).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3966655).length < 2 ^ (prefixWord ++ tailWord_3966655).sum := by decide
  have hdescent : baseEnd_3966655 < baseStart_3966655 := by decide
  rcases family_descends (prefixWord ++ tailWord_3966655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3966740 : List Nat := [2, 4, 4, 1, 2, 1, 1, 2, 5]
def baseStart_3966740 : Nat := 118140960795 + 3966740 * 2 ^ 59
def prefixEnd_3966740 : Nat := 4983230072969 + 3 ^ 40 * 3966740 * 2
def baseEnd_3966740 : Nat := 452632055870203410046067

theorem tailTrace_3966740 : CollatzResearch.WordTrace tailWord_3966740 prefixEnd_3966740 452632055870203410046067 := by
  unfold tailWord_3966740
  simp only [CollatzResearch.WordTrace]
  refine ⟨72339446824592960050672837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96452595766123946734230449 72339446824592960050672837)
  ·
    refine ⟨13563646279611180009501157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 72339446824592960050672837 13563646279611180009501157)
    ·
      refine ⟨2543183677427096251781467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13563646279611180009501157 2543183677427096251781467)
      ·
        refine ⟨3814775516140644377672201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2543183677427096251781467 3814775516140644377672201)
        ·
          refine ⟨2861081637105483283254151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3814775516140644377672201 2861081637105483283254151)
          ·
            refine ⟨4291622455658224924881227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2861081637105483283254151 4291622455658224924881227)
            ·
              refine ⟨6437433683487337387321841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4291622455658224924881227 6437433683487337387321841)
              ·
                refine ⟨4828075262615503040491381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6437433683487337387321841 4828075262615503040491381)
                ·
                  refine ⟨452632055870203410046067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4828075262615503040491381 452632055870203410046067)
                  ·
                    rfl

theorem cell22_3966740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 2, 1, 1, 2, 5].length) (baseStart_3966740 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3966740 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3966740 prefixEnd_3966740 := by exact prefixLift 3966740
  have htrace : WordTrace (prefixWord ++ tailWord_3966740) baseStart_3966740 baseEnd_3966740 := by
    simpa [prefixWord, tailWord_3966740, baseEnd_3966740] using wordTrace_append hprefix tailTrace_3966740
  have hstable : (prefixWord ++ tailWord_3966740).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3966740).length < 2 ^ (prefixWord ++ tailWord_3966740).sum := by decide
  have hdescent : baseEnd_3966740 < baseStart_3966740 := by decide
  rcases family_descends (prefixWord ++ tailWord_3966740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3966766 : List Nat := [4, 1, 3, 2, 2, 2, 1, 1, 1, 5]
def baseStart_3966766 : Nat := 118140960795 + 3966766 * 2 ^ 59
def prefixEnd_3966766 : Nat := 4983230072969 + 3 ^ 40 * 3966766 * 2
def baseEnd_3966766 : Nat := 1357905067941954828988121

theorem tailTrace_3966766 : CollatzResearch.WordTrace tailWord_3966766 prefixEnd_3966766 1357905067941954828988121 := by
  unfold tailWord_3966766
  simp only [CollatzResearch.WordTrace]
  refine ⟨18084980243386465817724019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 96453227964727817694528101 18084980243386465817724019)
  ·
    refine ⟨27127470365079698726586029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18084980243386465817724019 27127470365079698726586029)
    ·
      refine ⟨10172801386904887022469761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27127470365079698726586029 10172801386904887022469761)
      ·
        refine ⟨7629601040178665266852321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10172801386904887022469761 7629601040178665266852321)
        ·
          refine ⟨5722200780133998950139241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7629601040178665266852321 5722200780133998950139241)
          ·
            refine ⟨4291650585100499212604431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5722200780133998950139241 4291650585100499212604431)
            ·
              refine ⟨6437475877650748818906647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4291650585100499212604431 6437475877650748818906647)
              ·
                refine ⟨9656213816476123228359971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6437475877650748818906647 9656213816476123228359971)
                ·
                  refine ⟨14484320724714184842539957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9656213816476123228359971 14484320724714184842539957)
                  ·
                    refine ⟨1357905067941954828988121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14484320724714184842539957 1357905067941954828988121)
                    ·
                      rfl

theorem cell22_3966766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 2, 1, 1, 1, 5].length) (baseStart_3966766 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3966766 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3966766 prefixEnd_3966766 := by exact prefixLift 3966766
  have htrace : WordTrace (prefixWord ++ tailWord_3966766) baseStart_3966766 baseEnd_3966766 := by
    simpa [prefixWord, tailWord_3966766, baseEnd_3966766] using wordTrace_append hprefix tailTrace_3966766
  have hstable : (prefixWord ++ tailWord_3966766).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3966766).length < 2 ^ (prefixWord ++ tailWord_3966766).sum := by decide
  have hdescent : baseEnd_3966766 < baseStart_3966766 := by decide
  rcases family_descends (prefixWord ++ tailWord_3966766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3966835 : List Nat := [1, 1, 1, 2, 2, 1, 3, 3, 8]
def baseStart_3966835 : Nat := 118140960795 + 3966835 * 2 ^ 59
def prefixEnd_3966835 : Nat := 4983230072969 + 3 ^ 40 * 3966835 * 2
def baseEnd_3966835 : Nat := 452642896017353883004303

theorem tailTrace_3966835 : CollatzResearch.WordTrace tailWord_3966835 prefixEnd_3966835 452642896017353883004303 := by
  unfold tailWord_3966835
  simp only [CollatzResearch.WordTrace]
  refine ⟨144682358583841751326053959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96454905722561167550702639 144682358583841751326053959)
  ·
    refine ⟨217023537875762626989080939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144682358583841751326053959 217023537875762626989080939)
    ·
      refine ⟨325535306813643940483621409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217023537875762626989080939 325535306813643940483621409)
      ·
        refine ⟨244151480110232955362716057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 325535306813643940483621409 244151480110232955362716057)
        ·
          refine ⟨183113610082674716522037043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 244151480110232955362716057 183113610082674716522037043)
          ·
            refine ⟨274670415124012074783055565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 183113610082674716522037043 274670415124012074783055565)
            ·
              refine ⟨103001405671504528043645837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 274670415124012074783055565 103001405671504528043645837)
              ·
                refine ⟨38625527126814198016367189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 103001405671504528043645837 38625527126814198016367189)
                ·
                  refine ⟨452642896017353883004303, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 38625527126814198016367189 452642896017353883004303)
                  ·
                    rfl

theorem cell22_3966835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 3, 8].length) (baseStart_3966835 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3966835 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3966835 prefixEnd_3966835 := by exact prefixLift 3966835
  have htrace : WordTrace (prefixWord ++ tailWord_3966835) baseStart_3966835 baseEnd_3966835 := by
    simpa [prefixWord, tailWord_3966835, baseEnd_3966835] using wordTrace_append hprefix tailTrace_3966835
  have hstable : (prefixWord ++ tailWord_3966835).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3966835).length < 2 ^ (prefixWord ++ tailWord_3966835).sum := by decide
  have hdescent : baseEnd_3966835 < baseStart_3966835 := by decide
  rcases family_descends (prefixWord ++ tailWord_3966835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3966862 : List Nat := [4, 1, 1, 5, 1, 2, 2, 2, 1, 3]
def baseStart_3966862 : Nat := 118140960795 + 3966862 * 2 ^ 59
def prefixEnd_3966862 : Nat := 4983230072969 + 3 ^ 40 * 3966862 * 2
def baseEnd_3966862 : Nat := 1357937930703842578587827

theorem tailTrace_3966862 : CollatzResearch.WordTrace tailWord_3966862 prefixEnd_3966862 1357937930703842578587827 := by
  unfold tailWord_3966862
  simp only [CollatzResearch.WordTrace]
  refine ⟨18085417919342991867160855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 96455562236495956624857893 18085417919342991867160855)
  ·
    refine ⟨27128126879014487800741283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18085417919342991867160855 27128126879014487800741283)
    ·
      refine ⟨40692190318521731701111925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27128126879014487800741283 40692190318521731701111925)
      ·
        refine ⟨3814892842361412346979243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 40692190318521731701111925 3814892842361412346979243)
        ·
          refine ⟨5722339263542118520468865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3814892842361412346979243 5722339263542118520468865)
          ·
            refine ⟨4291754447656588890351649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5722339263542118520468865 4291754447656588890351649)
            ·
              refine ⟨3218815835742441667763737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4291754447656588890351649 3218815835742441667763737)
              ·
                refine ⟨2414111876806831250822803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3218815835742441667763737 2414111876806831250822803)
                ·
                  refine ⟨3621167815210246876234205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2414111876806831250822803 3621167815210246876234205)
                  ·
                    refine ⟨1357937930703842578587827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3621167815210246876234205 1357937930703842578587827)
                    ·
                      rfl

theorem cell22_3966862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 2, 2, 2, 1, 3].length) (baseStart_3966862 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3966862 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3966862 prefixEnd_3966862 := by exact prefixLift 3966862
  have htrace : WordTrace (prefixWord ++ tailWord_3966862) baseStart_3966862 baseEnd_3966862 := by
    simpa [prefixWord, tailWord_3966862, baseEnd_3966862] using wordTrace_append hprefix tailTrace_3966862
  have hstable : (prefixWord ++ tailWord_3966862).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3966862).length < 2 ^ (prefixWord ++ tailWord_3966862).sum := by decide
  have hdescent : baseEnd_3966862 < baseStart_3966862 := by decide
  rcases family_descends (prefixWord ++ tailWord_3966862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3966867 : List Nat := [1, 1, 1, 2, 1, 2, 1, 2, 8, 3]
def baseStart_3966867 : Nat := 118140960795 + 3966867 * 2 ^ 59
def prefixEnd_3966867 : Nat := 4983230072969 + 3 ^ 40 * 3966867 * 2
def baseEnd_3966867 : Nat := 1357939642306024232212811

theorem tailTrace_3966867 : CollatzResearch.WordTrace tailWord_3966867 prefixEnd_3966867 1357939642306024232212811 := by
  unfold tailWord_3966867
  simp only [CollatzResearch.WordTrace]
  refine ⟨144683525719725820791218855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96455683813150547194145903 144683525719725820791218855)
  ·
    refine ⟨217025288579588731186828283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144683525719725820791218855 217025288579588731186828283)
    ·
      refine ⟨325537932869383096780242425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217025288579588731186828283 325537932869383096780242425)
      ·
        refine ⟨244153449652037322585181819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 325537932869383096780242425 244153449652037322585181819)
        ·
          refine ⟨366230174478055983877772729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 244153449652037322585181819 366230174478055983877772729)
          ·
            refine ⟨274672630858541987908329547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 366230174478055983877772729 274672630858541987908329547)
            ·
              refine ⟨412008946287812981862494321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 274672630858541987908329547 412008946287812981862494321)
              ·
                refine ⟨309006709715859736396870741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 412008946287812981862494321 309006709715859736396870741)
                ·
                  refine ⟨3621172379482731285900829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 309006709715859736396870741 3621172379482731285900829)
                  ·
                    refine ⟨1357939642306024232212811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3621172379482731285900829 1357939642306024232212811)
                    ·
                      rfl

theorem cell22_3966867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 2, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 2, 8, 3].length) (baseStart_3966867 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3966867 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3966867 prefixEnd_3966867 := by exact prefixLift 3966867
  have htrace : WordTrace (prefixWord ++ tailWord_3966867) baseStart_3966867 baseEnd_3966867 := by
    simpa [prefixWord, tailWord_3966867, baseEnd_3966867] using wordTrace_append hprefix tailTrace_3966867
  have hstable : (prefixWord ++ tailWord_3966867).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3966867).length < 2 ^ (prefixWord ++ tailWord_3966867).sum := by decide
  have hdescent : baseEnd_3966867 < baseStart_3966867 := by decide
  rcases family_descends (prefixWord ++ tailWord_3966867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3966869 : List Nat := [1, 3, 2, 1, 1, 3, 3, 4, 4]
def baseStart_3966869 : Nat := 118140960795 + 3966869 * 2 ^ 59
def prefixEnd_3966869 : Nat := 4983230072969 + 3 ^ 40 * 3966869 * 2
def baseEnd_3966869 : Nat := 452646775648965631220935

theorem tailTrace_3966869 : CollatzResearch.WordTrace tailWord_3966869 prefixEnd_3966869 452646775648965631220935 := by
  unfold tailWord_3966869
  simp only [CollatzResearch.WordTrace]
  refine ⟨144683598665718575132791661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96455732443812383421861107 144683598665718575132791661)
  ·
    refine ⟨54256349499644465674796873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 144683598665718575132791661 54256349499644465674796873)
    ·
      refine ⟨40692262124733349256097655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54256349499644465674796873 40692262124733349256097655)
      ·
        refine ⟨61038393187100023884146483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40692262124733349256097655 61038393187100023884146483)
        ·
          refine ⟨91557589780650035826219725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61038393187100023884146483 91557589780650035826219725)
          ·
            refine ⟨34334096167743763434832397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 91557589780650035826219725 34334096167743763434832397)
            ·
              refine ⟨12875286062903911288062149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34334096167743763434832397 12875286062903911288062149)
              ·
                refine ⟨2414116136794483366511653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12875286062903911288062149 2414116136794483366511653)
                ·
                  refine ⟨452646775648965631220935, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2414116136794483366511653 452646775648965631220935)
                  ·
                    rfl

theorem cell22_3966869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 3, 4, 4].length) (baseStart_3966869 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3966869 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3966869 prefixEnd_3966869 := by exact prefixLift 3966869
  have htrace : WordTrace (prefixWord ++ tailWord_3966869) baseStart_3966869 baseEnd_3966869 := by
    simpa [prefixWord, tailWord_3966869, baseEnd_3966869] using wordTrace_append hprefix tailTrace_3966869
  have hstable : (prefixWord ++ tailWord_3966869).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3966869).length < 2 ^ (prefixWord ++ tailWord_3966869).sum := by decide
  have hdescent : baseEnd_3966869 < baseStart_3966869 := by decide
  rcases family_descends (prefixWord ++ tailWord_3966869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3966884 : List Nat := [2, 3, 1, 2, 1, 4, 2, 1, 1, 5]
def baseStart_3966884 : Nat := 118140960795 + 3966884 * 2 ^ 59
def prefixEnd_3966884 : Nat := 4983230072969 + 3 ^ 40 * 3966884 * 2
def baseEnd_3966884 : Nat := 1357945461753441854537759

theorem tailTrace_3966884 : CollatzResearch.WordTrace tailWord_3966884 prefixEnd_3966884 1357945461753441854537759 := by
  unfold tailWord_3966884
  simp only [CollatzResearch.WordTrace]
  refine ⟨72342072880332116347293853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96456097173776155129725137 72342072880332116347293853)
  ·
    refine ⟨27128277330124543630235195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72342072880332116347293853 27128277330124543630235195)
    ·
      refine ⟨40692415995186815445352793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27128277330124543630235195 40692415995186815445352793)
      ·
        refine ⟨30519311996390111584014595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40692415995186815445352793 30519311996390111584014595)
        ·
          refine ⟨45778967994585167376021893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30519311996390111584014595 45778967994585167376021893)
          ·
            refine ⟨8583556498984718883004105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45778967994585167376021893 8583556498984718883004105)
            ·
              refine ⟨6437667374238539162253079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8583556498984718883004105 6437667374238539162253079)
              ·
                refine ⟨9656501061357808743379619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6437667374238539162253079 9656501061357808743379619)
                ·
                  refine ⟨14484751592036713115069429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9656501061357808743379619 14484751592036713115069429)
                  ·
                    refine ⟨1357945461753441854537759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14484751592036713115069429 1357945461753441854537759)
                    ·
                      rfl

theorem cell22_3966884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 2, 1, 1, 5].length) (baseStart_3966884 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3966884 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3966884 prefixEnd_3966884 := by exact prefixLift 3966884
  have htrace : WordTrace (prefixWord ++ tailWord_3966884) baseStart_3966884 baseEnd_3966884 := by
    simpa [prefixWord, tailWord_3966884, baseEnd_3966884] using wordTrace_append hprefix tailTrace_3966884
  have hstable : (prefixWord ++ tailWord_3966884).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3966884).length < 2 ^ (prefixWord ++ tailWord_3966884).sum := by decide
  have hdescent : baseEnd_3966884 < baseStart_3966884 := by decide
  rcases family_descends (prefixWord ++ tailWord_3966884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3966980 : List Nat := [2, 3, 2, 4, 1, 2, 1, 1, 3, 3]
def baseStart_3966980 : Nat := 118140960795 + 3966980 * 2 ^ 59
def prefixEnd_3966980 : Nat := 4983230072969 + 3 ^ 40 * 3966980 * 2
def baseEnd_3966980 : Nat := 1357978324515329604137465

theorem tailTrace_3966980 : CollatzResearch.WordTrace tailWord_3966980 prefixEnd_3966980 1357978324515329604137465 := by
  unfold tailWord_3966980
  simp only [CollatzResearch.WordTrace]
  refine ⟨72343823584158220545041197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96458431445544294060054929 72343823584158220545041197)
  ·
    refine ⟨27128933844059332704390449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72343823584158220545041197 27128933844059332704390449)
    ·
      refine ⟨20346700383044499528292837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27128933844059332704390449 20346700383044499528292837)
      ·
        refine ⟨3815006321820843661554907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20346700383044499528292837 3815006321820843661554907)
        ·
          refine ⟨5722509482731265492332361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3815006321820843661554907 5722509482731265492332361)
          ·
            refine ⟨4291882112048449119249271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5722509482731265492332361 4291882112048449119249271)
            ·
              refine ⟨6437823168072673678873907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4291882112048449119249271 6437823168072673678873907)
              ·
                refine ⟨9656734752109010518310861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6437823168072673678873907 9656734752109010518310861)
                ·
                  refine ⟨3621275532040878944366573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9656734752109010518310861 3621275532040878944366573)
                  ·
                    refine ⟨1357978324515329604137465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3621275532040878944366573 1357978324515329604137465)
                    ·
                      rfl

theorem cell22_3966980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 2, 1, 1, 3, 3].length) (baseStart_3966980 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3966980 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3966980 prefixEnd_3966980 := by exact prefixLift 3966980
  have htrace : WordTrace (prefixWord ++ tailWord_3966980) baseStart_3966980 baseEnd_3966980 := by
    simpa [prefixWord, tailWord_3966980, baseEnd_3966980] using wordTrace_append hprefix tailTrace_3966980
  have hstable : (prefixWord ++ tailWord_3966980).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3966980).length < 2 ^ (prefixWord ++ tailWord_3966980).sum := by decide
  have hdescent : baseEnd_3966980 < baseStart_3966980 := by decide
  rcases family_descends (prefixWord ++ tailWord_3966980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3967017 : List Nat := [1, 2, 1, 1, 1, 1, 1, 1, 7, 6]
def baseStart_3967017 : Nat := 118140960795 + 3967017 * 2 ^ 59
def prefixEnd_3967017 : Nat := 4983230072969 + 3 ^ 40 * 3967017 * 2
def baseEnd_3967017 : Nat := 1357990990371473840962351

theorem tailTrace_3967017 : CollatzResearch.WordTrace tailWord_3967017 prefixEnd_3967017 1357990990371473840962351 := by
  unfold tailWord_3967017
  simp only [CollatzResearch.WordTrace]
  refine ⟨144688996669182396409179305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96459331112788264272786203 144688996669182396409179305)
  ·
    refine ⟨108516747501886797306884479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144688996669182396409179305 108516747501886797306884479)
    ·
      refine ⟨162775121252830195960326719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108516747501886797306884479 162775121252830195960326719)
      ·
        refine ⟨244162681879245293940490079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162775121252830195960326719 244162681879245293940490079)
        ·
          refine ⟨366244022818867940910735119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 244162681879245293940490079 366244022818867940910735119)
          ·
            refine ⟨549366034228301911366102679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 366244022818867940910735119 549366034228301911366102679)
            ·
              refine ⟨824049051342452867049154019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 549366034228301911366102679 824049051342452867049154019)
              ·
                refine ⟨1236073577013679300573731029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 824049051342452867049154019 1236073577013679300573731029)
                ·
                  refine ⟨28970474461258108607196821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1236073577013679300573731029 28970474461258108607196821)
                  ·
                    refine ⟨1357990990371473840962351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28970474461258108607196821 1357990990371473840962351)
                    ·
                      rfl

theorem cell22_3967017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 7, 6].length) (baseStart_3967017 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3967017 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3967017 prefixEnd_3967017 := by exact prefixLift 3967017
  have htrace : WordTrace (prefixWord ++ tailWord_3967017) baseStart_3967017 baseEnd_3967017 := by
    simpa [prefixWord, tailWord_3967017, baseEnd_3967017] using wordTrace_append hprefix tailTrace_3967017
  have hstable : (prefixWord ++ tailWord_3967017).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3967017).length < 2 ^ (prefixWord ++ tailWord_3967017).sum := by decide
  have hdescent : baseEnd_3967017 < baseStart_3967017 := by decide
  rcases family_descends (prefixWord ++ tailWord_3967017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3967019 : List Nat := [1, 1, 1, 1, 2, 1, 4, 4, 4, 3]
def baseStart_3967019 : Nat := 118140960795 + 3967019 * 2 ^ 59
def prefixEnd_3967019 : Nat := 4983230072969 + 3 ^ 40 * 3967019 * 2
def baseEnd_3967019 : Nat := 1357991675012346502412345

theorem tailTrace_3967019 : CollatzResearch.WordTrace tailWord_3967019 prefixEnd_3967019 1357991675012346502412345 := by
  unfold tailWord_3967019
  simp only [CollatzResearch.WordTrace]
  refine ⟨144689069615175150750752111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96459379743450100500501407 144689069615175150750752111)
  ·
    refine ⟨217033604422762726126128167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144689069615175150750752111 217033604422762726126128167)
    ·
      refine ⟨325550406634144089189192251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217033604422762726126128167 325550406634144089189192251)
      ·
        refine ⟨488325609951216133783788377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 325550406634144089189192251 488325609951216133783788377)
        ·
          refine ⟨366244207463412100337841283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 488325609951216133783788377 366244207463412100337841283)
          ·
            refine ⟨549366311195118150506761925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 366244207463412100337841283 549366311195118150506761925)
            ·
              refine ⟨103006183349084653220017861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 549366311195118150506761925 103006183349084653220017861)
              ·
                refine ⟨19313659377953372478753349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 103006183349084653220017861 19313659377953372478753349)
                ·
                  refine ⟨3621311133366257339766253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19313659377953372478753349 3621311133366257339766253)
                  ·
                    refine ⟨1357991675012346502412345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3621311133366257339766253 1357991675012346502412345)
                    ·
                      rfl

theorem cell22_3967019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 4, 4, 3].length) (baseStart_3967019 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3967019 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3967019 prefixEnd_3967019 := by exact prefixLift 3967019
  have htrace : WordTrace (prefixWord ++ tailWord_3967019) baseStart_3967019 baseEnd_3967019 := by
    simpa [prefixWord, tailWord_3967019, baseEnd_3967019] using wordTrace_append hprefix tailTrace_3967019
  have hstable : (prefixWord ++ tailWord_3967019).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3967019).length < 2 ^ (prefixWord ++ tailWord_3967019).sum := by decide
  have hdescent : baseEnd_3967019 < baseStart_3967019 := by decide
  rcases family_descends (prefixWord ++ tailWord_3967019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3967032 : List Nat := [2, 1, 2, 1, 16]
def baseStart_3967032 : Nat := 118140960795 + 3967032 * 2 ^ 59
def prefixEnd_3967032 : Nat := 4983230072969 + 3 ^ 40 * 3967032 * 2
def baseEnd_3967032 : Nat := 5588461420485674081635

theorem tailTrace_3967032 : CollatzResearch.WordTrace tailWord_3967032 prefixEnd_3967032 5588461420485674081635 := by
  unfold tailWord_3967032
  simp only [CollatzResearch.WordTrace]
  refine ⟨72344771882064026985487675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96459695842752035980650233 72344771882064026985487675)
  ·
    refine ⟨108517157823096040478231513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72344771882064026985487675 108517157823096040478231513)
    ·
      refine ⟨81387868367322030358673635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108517157823096040478231513 81387868367322030358673635)
      ·
        refine ⟨122081802550983045538010453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81387868367322030358673635 122081802550983045538010453)
        ·
          refine ⟨5588461420485674081635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 16 122081802550983045538010453 5588461420485674081635)
          ·
            rfl

theorem cell22_3967032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 16].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 16].length) (baseStart_3967032 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3967032 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3967032 prefixEnd_3967032 := by exact prefixLift 3967032
  have htrace : WordTrace (prefixWord ++ tailWord_3967032) baseStart_3967032 baseEnd_3967032 := by
    simpa [prefixWord, tailWord_3967032, baseEnd_3967032] using wordTrace_append hprefix tailTrace_3967032
  have hstable : (prefixWord ++ tailWord_3967032).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3967032).length < 2 ^ (prefixWord ++ tailWord_3967032).sum := by decide
  have hdescent : baseEnd_3967032 < baseStart_3967032 := by decide
  rcases family_descends (prefixWord ++ tailWord_3967032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3967053 : List Nat := [1, 6, 1, 1, 1, 1, 1, 5, 2, 3]
def baseStart_3967053 : Nat := 118140960795 + 3967053 * 2 ^ 59
def prefixEnd_3967053 : Nat := 4983230072969 + 3 ^ 40 * 3967053 * 2
def baseEnd_3967053 : Nat := 1358003313907181747062241

theorem tailTrace_3967053 : CollatzResearch.WordTrace tailWord_3967053 prefixEnd_3967053 1358003313907181747062241 := by
  unfold tailWord_3967053
  simp only [CollatzResearch.WordTrace]
  refine ⟨144690309697051974557489813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96460206464701316371659875 144690309697051974557489813)
  ·
    refine ⟨6782358267049311307382335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 144690309697051974557489813 6782358267049311307382335)
    ·
      refine ⟨10173537400573966961073503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6782358267049311307382335 10173537400573966961073503)
      ·
        refine ⟨15260306100860950441610255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10173537400573966961073503 15260306100860950441610255)
        ·
          refine ⟨22890459151291425662415383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15260306100860950441610255 22890459151291425662415383)
          ·
            refine ⟨34335688726937138493623075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22890459151291425662415383 34335688726937138493623075)
            ·
              refine ⟨51503533090405707740434613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34335688726937138493623075 51503533090405707740434613)
              ·
                refine ⟨4828456227225535100665745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 51503533090405707740434613 4828456227225535100665745)
                ·
                  refine ⟨3621342170419151325499309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4828456227225535100665745 3621342170419151325499309)
                  ·
                    refine ⟨1358003313907181747062241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3621342170419151325499309 1358003313907181747062241)
                    ·
                      rfl

theorem cell22_3967053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 5, 2, 3].length) (baseStart_3967053 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3967053 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3967053 prefixEnd_3967053 := by exact prefixLift 3967053
  have htrace : WordTrace (prefixWord ++ tailWord_3967053) baseStart_3967053 baseEnd_3967053 := by
    simpa [prefixWord, tailWord_3967053, baseEnd_3967053] using wordTrace_append hprefix tailTrace_3967053
  have hstable : (prefixWord ++ tailWord_3967053).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3967053).length < 2 ^ (prefixWord ++ tailWord_3967053).sum := by decide
  have hdescent : baseEnd_3967053 < baseStart_3967053 := by decide
  rcases family_descends (prefixWord ++ tailWord_3967053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3967068 : List Nat := [2, 2, 4, 1, 1, 4, 1, 1, 2, 4]
def baseStart_3967068 : Nat := 118140960795 + 3967068 * 2 ^ 59
def prefixEnd_3967068 : Nat := 4983230072969 + 3 ^ 40 * 3967068 * 2
def baseEnd_3967068 : Nat := 1358008448713726707937195

theorem tailTrace_3967068 : CollatzResearch.WordTrace tailWord_3967068 prefixEnd_3967068 1358008448713726707937195 := by
  unfold tailWord_3967068
  simp only [CollatzResearch.WordTrace]
  refine ⟨72345428395998816059642929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96460571194665088079523905 72345428395998816059642929)
  ·
    refine ⟨54259071296999112044732197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72345428395998816059642929 54259071296999112044732197)
    ·
      refine ⟨10173575868187333508387287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 54259071296999112044732197 10173575868187333508387287)
      ·
        refine ⟨15260363802281000262580931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10173575868187333508387287 15260363802281000262580931)
        ·
          refine ⟨22890545703421500393871397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15260363802281000262580931 22890545703421500393871397)
          ·
            refine ⟨4291977319391531323850887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22890545703421500393871397 4291977319391531323850887)
            ·
              refine ⟨6437965979087296985776331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4291977319391531323850887 6437965979087296985776331)
              ·
                refine ⟨9656948968630945478664497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6437965979087296985776331 9656948968630945478664497)
                ·
                  refine ⟨7242711726473209108998373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9656948968630945478664497 7242711726473209108998373)
                  ·
                    refine ⟨1358008448713726707937195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7242711726473209108998373 1358008448713726707937195)
                    ·
                      rfl

theorem cell22_3967068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 4, 1, 1, 2, 4].length) (baseStart_3967068 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3967068 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3967068 prefixEnd_3967068 := by exact prefixLift 3967068
  have htrace : WordTrace (prefixWord ++ tailWord_3967068) baseStart_3967068 baseEnd_3967068 := by
    simpa [prefixWord, tailWord_3967068, baseEnd_3967068] using wordTrace_append hprefix tailTrace_3967068
  have hstable : (prefixWord ++ tailWord_3967068).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3967068).length < 2 ^ (prefixWord ++ tailWord_3967068).sum := by decide
  have hdescent : baseEnd_3967068 < baseStart_3967068 := by decide
  rcases family_descends (prefixWord ++ tailWord_3967068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3967141 : List Nat := [1, 3, 1, 2, 1, 3, 1, 5, 1, 4]
def baseStart_3967141 : Nat := 118140960795 + 3967141 * 2 ^ 59
def prefixEnd_3967141 : Nat := 4983230072969 + 3 ^ 40 * 3967141 * 2
def baseEnd_3967141 : Nat := 1358033438105578850861971

theorem tailTrace_3967141 : CollatzResearch.WordTrace tailWord_3967141 prefixEnd_3967141 1358033438105578850861971 := by
  unfold tailWord_3967141
  simp only [CollatzResearch.WordTrace]
  refine ⟨144693519320733165586693277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96462346213822110391128851 144693519320733165586693277)
  ·
    refine ⟨54260069745274937095009979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 144693519320733165586693277 54260069745274937095009979)
    ·
      refine ⟨81390104617912405642514969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54260069745274937095009979 81390104617912405642514969)
      ·
        refine ⟨61042578463434304231886227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81390104617912405642514969 61042578463434304231886227)
        ·
          refine ⟨91563867695151456347829341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61042578463434304231886227 91563867695151456347829341)
          ·
            refine ⟨34336450385681796130436003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 91563867695151456347829341 34336450385681796130436003)
            ·
              refine ⟨51504675578522694195654005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34336450385681796130436003 51504675578522694195654005)
              ·
                refine ⟨4828563335486502580842563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 51504675578522694195654005 4828563335486502580842563)
                ·
                  refine ⟨7242845003229753871263845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4828563335486502580842563 7242845003229753871263845)
                  ·
                    refine ⟨1358033438105578850861971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7242845003229753871263845 1358033438105578850861971)
                    ·
                      rfl

theorem cell22_3967141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 5, 1, 4].length) (baseStart_3967141 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3967141 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3967141 prefixEnd_3967141 := by exact prefixLift 3967141
  have htrace : WordTrace (prefixWord ++ tailWord_3967141) baseStart_3967141 baseEnd_3967141 := by
    simpa [prefixWord, tailWord_3967141, baseEnd_3967141] using wordTrace_append hprefix tailTrace_3967141
  have hstable : (prefixWord ++ tailWord_3967141).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3967141).length < 2 ^ (prefixWord ++ tailWord_3967141).sum := by decide
  have hdescent : baseEnd_3967141 < baseStart_3967141 := by decide
  rcases family_descends (prefixWord ++ tailWord_3967141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3967205 : List Nat := [1, 3, 1, 4, 2, 2, 2, 2, 2, 3]
def baseStart_3967205 : Nat := 118140960795 + 3967205 * 2 ^ 59
def prefixEnd_3967205 : Nat := 4983230072969 + 3 ^ 40 * 3967205 * 2
def baseEnd_3967205 : Nat := 1358055346613504017261775

theorem tailTrace_3967205 : CollatzResearch.WordTrace tailWord_3967205 prefixEnd_3967205 1358055346613504017261775 := by
  unfold tailWord_3967205
  simp only [CollatzResearch.WordTrace]
  refine ⟨144695853592501304517023069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96463902395000869678015379 144695853592501304517023069)
  ·
    refine ⟨54260945097187989193883651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 144695853592501304517023069 54260945097187989193883651)
    ·
      refine ⟨81391417645781983790825477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54260945097187989193883651 81391417645781983790825477)
      ·
        refine ⟨15260890808584121960779777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 81391417645781983790825477 15260890808584121960779777)
        ·
          refine ⟨11445668106438091470584833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15260890808584121960779777 11445668106438091470584833)
          ·
            refine ⟨8584251079828568602938625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11445668106438091470584833 8584251079828568602938625)
            ·
              refine ⟨6438188309871426452203969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8584251079828568602938625 6438188309871426452203969)
              ·
                refine ⟨4828641232403569839152977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6438188309871426452203969 4828641232403569839152977)
                ·
                  refine ⟨3621480924302677379364733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4828641232403569839152977 3621480924302677379364733)
                  ·
                    refine ⟨1358055346613504017261775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3621480924302677379364733 1358055346613504017261775)
                    ·
                      rfl

theorem cell22_3967205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 2, 2, 2, 3].length) (baseStart_3967205 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3967205 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3967205 prefixEnd_3967205 := by exact prefixLift 3967205
  have htrace : WordTrace (prefixWord ++ tailWord_3967205) baseStart_3967205 baseEnd_3967205 := by
    simpa [prefixWord, tailWord_3967205, baseEnd_3967205] using wordTrace_append hprefix tailTrace_3967205
  have hstable : (prefixWord ++ tailWord_3967205).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3967205).length < 2 ^ (prefixWord ++ tailWord_3967205).sum := by decide
  have hdescent : baseEnd_3967205 < baseStart_3967205 := by decide
  rcases family_descends (prefixWord ++ tailWord_3967205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3967207 : List Nat := [1, 1, 5, 3, 1, 3, 2, 2, 4]
def baseStart_3967207 : Nat := 118140960795 + 3967207 * 2 ^ 59
def prefixEnd_3967207 : Nat := 4983230072969 + 3 ^ 40 * 3967207 * 2
def baseEnd_3967207 : Nat := 452685343751458892903923

theorem tailTrace_3967207 : CollatzResearch.WordTrace tailWord_3967207 prefixEnd_3967207 452685343751458892903923 := by
  unfold tailWord_3967207
  simp only [CollatzResearch.WordTrace]
  refine ⟨144695926538494058858595875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96463951025662705905730583 144695926538494058858595875)
  ·
    refine ⟨217043889807741088287893813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144695926538494058858595875 217043889807741088287893813)
    ·
      refine ⟨20347864669475727026990045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 217043889807741088287893813 20347864669475727026990045)
      ·
        refine ⟨7630449251053397635121267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20347864669475727026990045 7630449251053397635121267)
        ·
          refine ⟨11445673876580096452681901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7630449251053397635121267 11445673876580096452681901)
          ·
            refine ⟨4292127703717536169755713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11445673876580096452681901 4292127703717536169755713)
            ·
              refine ⟨3219095777788152127316785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4292127703717536169755713 3219095777788152127316785)
              ·
                refine ⟨2414321833341114095487589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3219095777788152127316785 2414321833341114095487589)
                ·
                  refine ⟨452685343751458892903923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2414321833341114095487589 452685343751458892903923)
                  ·
                    rfl

theorem cell22_3967207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 3, 2, 2, 4].length) (baseStart_3967207 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3967207 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3967207 prefixEnd_3967207 := by exact prefixLift 3967207
  have htrace : WordTrace (prefixWord ++ tailWord_3967207) baseStart_3967207 baseEnd_3967207 := by
    simpa [prefixWord, tailWord_3967207, baseEnd_3967207] using wordTrace_append hprefix tailTrace_3967207
  have hstable : (prefixWord ++ tailWord_3967207).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3967207).length < 2 ^ (prefixWord ++ tailWord_3967207).sum := by decide
  have hdescent : baseEnd_3967207 < baseStart_3967207 := by decide
  rcases family_descends (prefixWord ++ tailWord_3967207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3967216 : List Nat := [2, 1, 1, 1, 3, 1, 1, 2, 7, 3]
def baseStart_3967216 : Nat := 118140960795 + 3967216 * 2 ^ 59
def prefixEnd_3967216 : Nat := 4983230072969 + 3 ^ 40 * 3967216 * 2
def baseEnd_3967216 : Nat := 1358059112138303655236741

theorem tailTrace_3967216 : CollatzResearch.WordTrace tailWord_3967216 prefixEnd_3967216 1358059112138303655236741 := by
  unfold tailWord_3967216
  simp only [CollatzResearch.WordTrace]
  refine ⟨72348127397730726697836751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96464169863640968930449001 72348127397730726697836751)
  ·
    refine ⟨108522191096596090046755127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72348127397730726697836751 108522191096596090046755127)
    ·
      refine ⟨162783286644894135070132691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108522191096596090046755127 162783286644894135070132691)
      ·
        refine ⟨244174929967341202605199037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162783286644894135070132691 244174929967341202605199037)
        ·
          refine ⟨91565598737752950976949639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 244174929967341202605199037 91565598737752950976949639)
          ·
            refine ⟨137348398106629426465424459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91565598737752950976949639 137348398106629426465424459)
            ·
              refine ⟨206022597159944139698136689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 137348398106629426465424459 206022597159944139698136689)
              ·
                refine ⟨154516947869958104773602517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 206022597159944139698136689 154516947869958104773602517)
                ·
                  refine ⟨3621490965702143080631309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 154516947869958104773602517 3621490965702143080631309)
                  ·
                    refine ⟨1358059112138303655236741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3621490965702143080631309 1358059112138303655236741)
                    ·
                      rfl

theorem cell22_3967216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 2, 7, 3].length) (baseStart_3967216 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3967216 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3967216 prefixEnd_3967216 := by exact prefixLift 3967216
  have htrace : WordTrace (prefixWord ++ tailWord_3967216) baseStart_3967216 baseEnd_3967216 := by
    simpa [prefixWord, tailWord_3967216, baseEnd_3967216] using wordTrace_append hprefix tailTrace_3967216
  have hstable : (prefixWord ++ tailWord_3967216).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3967216).length < 2 ^ (prefixWord ++ tailWord_3967216).sum := by decide
  have hdescent : baseEnd_3967216 < baseStart_3967216 := by decide
  rcases family_descends (prefixWord ++ tailWord_3967216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3967218 : List Nat := [3, 2, 1, 3, 2, 3, 1, 7]
def baseStart_3967218 : Nat := 118140960795 + 3967218 * 2 ^ 59
def prefixEnd_3967218 : Nat := 4983230072969 + 3 ^ 40 * 3967218 * 2
def baseEnd_3967218 : Nat := 150895532975464035187415

theorem tailTrace_3967218 : CollatzResearch.WordTrace tailWord_3967218 prefixEnd_3967218 150895532975464035187415 := by
  unfold tailWord_3967218
  simp only [CollatzResearch.WordTrace]
  refine ⟨36174081935363551934311577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96464218494302805158164205 36174081935363551934311577)
  ·
    refine ⟨27130561451522663950733683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36174081935363551934311577 27130561451522663950733683)
    ·
      refine ⟨40695842177283995926100525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27130561451522663950733683 40695842177283995926100525)
      ·
        refine ⟨15260940816481498472287697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40695842177283995926100525 15260940816481498472287697)
        ·
          refine ⟨11445705612361123854215773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15260940816481498472287697 11445705612361123854215773)
          ·
            refine ⟨4292139604635421445330915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11445705612361123854215773 4292139604635421445330915)
            ·
              refine ⟨6438209406953132167996373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4292139604635421445330915 6438209406953132167996373)
              ·
                refine ⟨150895532975464035187415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6438209406953132167996373 150895532975464035187415)
                ·
                  rfl

theorem cell22_3967218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 3, 1, 7].length) (baseStart_3967218 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3967218 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3967218 prefixEnd_3967218 := by exact prefixLift 3967218
  have htrace : WordTrace (prefixWord ++ tailWord_3967218) baseStart_3967218 baseEnd_3967218 := by
    simpa [prefixWord, tailWord_3967218, baseEnd_3967218] using wordTrace_append hprefix tailTrace_3967218
  have hstable : (prefixWord ++ tailWord_3967218).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3967218).length < 2 ^ (prefixWord ++ tailWord_3967218).sum := by decide
  have hdescent : baseEnd_3967218 < baseStart_3967218 := by decide
  rcases family_descends (prefixWord ++ tailWord_3967218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3967233 : List Nat := [1, 2, 4, 1, 1, 2, 3, 2, 3, 3]
def baseStart_3967233 : Nat := 118140960795 + 3967233 * 2 ^ 59
def prefixEnd_3967233 : Nat := 4983230072969 + 3 ^ 40 * 3967233 * 2
def baseEnd_3967233 : Nat := 1358064931585721277561689

theorem tailTrace_3967233 : CollatzResearch.WordTrace tailWord_3967233 prefixEnd_3967233 1358064931585721277561689 := by
  unfold tailWord_3967233
  simp only [CollatzResearch.WordTrace]
  refine ⟨144696874836399865299042353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96464583224266576866028235 144696874836399865299042353)
  ·
    refine ⟨108522656127299898974281765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144696874836399865299042353 108522656127299898974281765)
    ·
      refine ⟨20347998023868731057677831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 108522656127299898974281765 20347998023868731057677831)
      ·
        refine ⟨30521997035803096586516747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20347998023868731057677831 30521997035803096586516747)
        ·
          refine ⟨45782995553704644879775121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30521997035803096586516747 45782995553704644879775121)
          ·
            refine ⟨34337246665278483659831341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45782995553704644879775121 34337246665278483659831341)
            ·
              refine ⟨12876467499479431372436753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34337246665278483659831341 12876467499479431372436753)
              ·
                refine ⟨9657350624609573529327565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12876467499479431372436753 9657350624609573529327565)
                ·
                  refine ⟨3621506484228590073497837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9657350624609573529327565 3621506484228590073497837)
                  ·
                    refine ⟨1358064931585721277561689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3621506484228590073497837 1358064931585721277561689)
                    ·
                      rfl

theorem cell22_3967233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 3, 2, 3, 3].length) (baseStart_3967233 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3967233 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3967233 prefixEnd_3967233 := by exact prefixLift 3967233
  have htrace : WordTrace (prefixWord ++ tailWord_3967233) baseStart_3967233 baseEnd_3967233 := by
    simpa [prefixWord, tailWord_3967233, baseEnd_3967233] using wordTrace_append hprefix tailTrace_3967233
  have hstable : (prefixWord ++ tailWord_3967233).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3967233).length < 2 ^ (prefixWord ++ tailWord_3967233).sum := by decide
  have hdescent : baseEnd_3967233 < baseStart_3967233 := by decide
  rcases family_descends (prefixWord ++ tailWord_3967233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3967246 : List Nat := [4, 1, 1, 2, 1, 2, 2, 2, 7]
def baseStart_3967246 : Nat := 118140960795 + 3967246 * 2 ^ 59
def prefixEnd_3967246 : Nat := 4983230072969 + 3 ^ 40 * 3967246 * 2
def baseEnd_3967246 : Nat := 452689793917131192328883

theorem tailTrace_3967246 : CollatzResearch.WordTrace tailWord_3967246 prefixEnd_3967246 452689793917131192328883 := by
  unfold tailWord_3967246
  simp only [CollatzResearch.WordTrace]
  refine ⟨18087168623169096064908199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 96464899323568512346177061 18087168623169096064908199)
  ·
    refine ⟨27130752934753644097362299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18087168623169096064908199 27130752934753644097362299)
    ·
      refine ⟨40696129402130466146043449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27130752934753644097362299 40696129402130466146043449)
      ·
        refine ⟨30522097051597849609532587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40696129402130466146043449 30522097051597849609532587)
        ·
          refine ⟨45783145577396774414298881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30522097051597849609532587 45783145577396774414298881)
          ·
            refine ⟨34337359183047580810724161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45783145577396774414298881 34337359183047580810724161)
            ·
              refine ⟨25753019387285685608043121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34337359183047580810724161 25753019387285685608043121)
              ·
                refine ⟨19314764540464264206032341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25753019387285685608043121 19314764540464264206032341)
                ·
                  refine ⟨452689793917131192328883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19314764540464264206032341 452689793917131192328883)
                  ·
                    rfl

theorem cell22_3967246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 2, 2, 7].length) (baseStart_3967246 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3967246 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3967246 prefixEnd_3967246 := by exact prefixLift 3967246
  have htrace : WordTrace (prefixWord ++ tailWord_3967246) baseStart_3967246 baseEnd_3967246 := by
    simpa [prefixWord, tailWord_3967246, baseEnd_3967246] using wordTrace_append hprefix tailTrace_3967246
  have hstable : (prefixWord ++ tailWord_3967246).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3967246).length < 2 ^ (prefixWord ++ tailWord_3967246).sum := by decide
  have hdescent : baseEnd_3967246 < baseStart_3967246 := by decide
  rcases family_descends (prefixWord ++ tailWord_3967246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3967263 : List Nat := [1, 1, 2, 4, 3, 1, 3, 2, 5]
def baseStart_3967263 : Nat := 118140960795 + 3967263 * 2 ^ 59
def prefixEnd_3967263 : Nat := 4983230072969 + 3 ^ 40 * 3967263 * 2
def baseEnd_3967263 : Nat := 452691733732937066437199

theorem tailTrace_3967263 : CollatzResearch.WordTrace tailWord_3967263 prefixEnd_3967263 452691733732937066437199 := by
  unfold tailWord_3967263
  simp only [CollatzResearch.WordTrace]
  refine ⟨144697969026291180422634443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96465312684194120281756295 144697969026291180422634443)
  ·
    refine ⟨217046953539436770633951665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144697969026291180422634443 217046953539436770633951665)
    ·
      refine ⟨162785215154577577975463749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 217046953539436770633951665 162785215154577577975463749)
      ·
        refine ⟨30522227841483295870399453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 162785215154577577975463749 30522227841483295870399453)
        ·
          refine ⟨11445835440556235951399795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30522227841483295870399453 11445835440556235951399795)
          ·
            refine ⟨17168753160834353927099693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11445835440556235951399795 17168753160834353927099693)
            ·
              refine ⟨6438282435312882722662385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17168753160834353927099693 6438282435312882722662385)
              ·
                refine ⟨4828711826484662041996789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6438282435312882722662385 4828711826484662041996789)
                ·
                  refine ⟨452691733732937066437199, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4828711826484662041996789 452691733732937066437199)
                  ·
                    rfl

theorem cell22_3967263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 3, 2, 5].length) (baseStart_3967263 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3967263 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3967263 prefixEnd_3967263 := by exact prefixLift 3967263
  have htrace : WordTrace (prefixWord ++ tailWord_3967263) baseStart_3967263 baseEnd_3967263 := by
    simpa [prefixWord, tailWord_3967263, baseEnd_3967263] using wordTrace_append hprefix tailTrace_3967263
  have hstable : (prefixWord ++ tailWord_3967263).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3967263).length < 2 ^ (prefixWord ++ tailWord_3967263).sum := by decide
  have hdescent : baseEnd_3967263 < baseStart_3967263 := by decide
  rcases family_descends (prefixWord ++ tailWord_3967263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3967276 : List Nat := [2, 2, 1, 1, 1, 3, 2, 1, 5, 4]
def baseStart_3967276 : Nat := 118140960795 + 3967276 * 2 ^ 59
def prefixEnd_3967276 : Nat := 4983230072969 + 3 ^ 40 * 3967276 * 2
def baseEnd_3967276 : Nat := 1358079651364483498736557

theorem tailTrace_3967276 : CollatzResearch.WordTrace tailWord_3967276 prefixEnd_3967276 1358079651364483498736557 := by
  unfold tailWord_3967276
  simp only [CollatzResearch.WordTrace]
  refine ⟨72349221587622041821428841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96465628783496055761905121 72349221587622041821428841)
  ·
    refine ⟨54261916190716531366071631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72349221587622041821428841 54261916190716531366071631)
    ·
      refine ⟨81392874286074797049107447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54261916190716531366071631 81392874286074797049107447)
      ·
        refine ⟨122089311429112195573661171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81392874286074797049107447 122089311429112195573661171)
        ·
          refine ⟨183133967143668293360491757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122089311429112195573661171 183133967143668293360491757)
          ·
            refine ⟨68675237678875610010184409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 183133967143668293360491757 68675237678875610010184409)
            ·
              refine ⟨51506428259156707507638307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68675237678875610010184409 51506428259156707507638307)
              ·
                refine ⟨77259642388735061261457461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51506428259156707507638307 77259642388735061261457461)
                ·
                  refine ⟨7243091473943911993261637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 77259642388735061261457461 7243091473943911993261637)
                  ·
                    refine ⟨1358079651364483498736557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7243091473943911993261637 1358079651364483498736557)
                    ·
                      rfl

theorem cell22_3967276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 4].length) (baseStart_3967276 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3967276 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3967276 prefixEnd_3967276 := by exact prefixLift 3967276
  have htrace : WordTrace (prefixWord ++ tailWord_3967276) baseStart_3967276 baseEnd_3967276 := by
    simpa [prefixWord, tailWord_3967276, baseEnd_3967276] using wordTrace_append hprefix tailTrace_3967276
  have hstable : (prefixWord ++ tailWord_3967276).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3967276).length < 2 ^ (prefixWord ++ tailWord_3967276).sum := by decide
  have hdescent : baseEnd_3967276 < baseStart_3967276 := by decide
  rcases family_descends (prefixWord ++ tailWord_3967276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
