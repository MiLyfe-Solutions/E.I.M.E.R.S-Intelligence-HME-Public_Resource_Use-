import V185TrunkScan23Chunk0374

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_2217079 : List Nat := [1, 1, 3, 1, 1, 4, 2, 1, 3, 1, 5]
def baseStart_2217079 : Nat := 118140960795 + 2217079 * 2 ^ 59
def prefixEnd_2217079 : Nat := 4983230072969 + 3 ^ 40 * 2217079 * 2
def baseEnd_2217079 : Nat := 1138427175989636401916345

theorem tailTrace_2217079 : CollatzResearch.WordTrace tailWord_2217079 prefixEnd_2217079 1138427175989636401916345 := by
  unfold tailWord_2217079
  simp only [CollatzResearch.WordTrace]
  refine ⟨80863514334908904792686291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53909009556605936528457527 80863514334908904792686291)
  ·
    refine ⟨121295271502363357189029437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80863514334908904792686291 121295271502363357189029437)
    ·
      refine ⟨45485726813386258945886039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 121295271502363357189029437 45485726813386258945886039)
      ·
        refine ⟨68228590220079388418829059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45485726813386258945886039 68228590220079388418829059)
        ·
          refine ⟨102342885330119082628243589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68228590220079388418829059 102342885330119082628243589)
          ·
            refine ⟨19189290999397327992795673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 102342885330119082628243589 19189290999397327992795673)
            ·
              refine ⟨14391968249547995994596755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19189290999397327992795673 14391968249547995994596755)
              ·
                refine ⟨21587952374321993991895133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14391968249547995994596755 21587952374321993991895133)
                ·
                  refine ⟨8095482140370747746960675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21587952374321993991895133 8095482140370747746960675)
                  ·
                    refine ⟨12143223210556121620441013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8095482140370747746960675 12143223210556121620441013)
                    ·
                      refine ⟨1138427175989636401916345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12143223210556121620441013 1138427175989636401916345)
                      ·
                        rfl

theorem cell23_2217079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 2, 1, 3, 1, 5].length) (baseStart_2217079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2217079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2217079 prefixEnd_2217079 := by exact prefixLift 2217079
  have htrace : WordTrace (prefixWord ++ tailWord_2217079) baseStart_2217079 baseEnd_2217079 := by
    simpa [prefixWord, tailWord_2217079, baseEnd_2217079] using wordTrace_append hprefix tailTrace_2217079
  have hstable : (prefixWord ++ tailWord_2217079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2217079).length < 2 ^ (prefixWord ++ tailWord_2217079).sum := by decide
  have hdescent : baseEnd_2217079 < baseStart_2217079 := by decide
  rcases family_descends (prefixWord ++ tailWord_2217079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2217127 : List Nat := [1, 1, 6, 2, 1, 2, 2, 1, 3, 2, 2]
def baseStart_2217127 : Nat := 118140960795 + 2217127 * 2 ^ 59
def prefixEnd_2217127 : Nat := 4983230072969 + 3 ^ 40 * 2217127 * 2
def baseEnd_2217127 : Nat := 1138451823061052214116125

theorem tailTrace_2217127 : CollatzResearch.WordTrace tailWord_2217127 prefixEnd_2217127 1138451823061052214116125 := by
  unfold tailWord_2217127
  simp only [CollatzResearch.WordTrace]
  refine ⟨80865265038735008990433635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53910176692490005993622423 80865265038735008990433635)
  ·
    refine ⟨121297897558102513485650453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80865265038735008990433635 121297897558102513485650453)
    ·
      refine ⟨5685838948036055319639865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 121297897558102513485650453 5685838948036055319639865)
      ·
        refine ⟨4264379211027041489729899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5685838948036055319639865 4264379211027041489729899)
        ·
          refine ⟨6396568816540562234594849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4264379211027041489729899 6396568816540562234594849)
          ·
            refine ⟨4797426612405421675946137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6396568816540562234594849 4797426612405421675946137)
            ·
              refine ⟨3598069959304066256959603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4797426612405421675946137 3598069959304066256959603)
              ·
                refine ⟨5397104938956099385439405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3598069959304066256959603 5397104938956099385439405)
                ·
                  refine ⟨2023914352108537269539777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5397104938956099385439405 2023914352108537269539777)
                  ·
                    refine ⟨1517935764081402952154833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2023914352108537269539777 1517935764081402952154833)
                    ·
                      refine ⟨1138451823061052214116125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1517935764081402952154833 1138451823061052214116125)
                      ·
                        rfl

theorem cell23_2217127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 2, 1, 3, 2, 2].length) (baseStart_2217127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2217127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2217127 prefixEnd_2217127 := by exact prefixLift 2217127
  have htrace : WordTrace (prefixWord ++ tailWord_2217127) baseStart_2217127 baseEnd_2217127 := by
    simpa [prefixWord, tailWord_2217127, baseEnd_2217127] using wordTrace_append hprefix tailTrace_2217127
  have hstable : (prefixWord ++ tailWord_2217127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2217127).length < 2 ^ (prefixWord ++ tailWord_2217127).sum := by decide
  have hdescent : baseEnd_2217127 < baseStart_2217127 := by decide
  rcases family_descends (prefixWord ++ tailWord_2217127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2217159 : List Nat := [1, 1, 4, 1, 1, 1, 1, 4, 1, 8]
def baseStart_2217159 : Nat := 118140960795 + 2217159 * 2 ^ 59
def prefixEnd_2217159 : Nat := 4983230072969 + 3 ^ 40 * 2217159 * 2
def baseEnd_2217159 : Nat := 379489418147332029638659

theorem tailTrace_2217159 : CollatzResearch.WordTrace tailWord_2217159 prefixEnd_2217159 379489418147332029638659 := by
  unfold tailWord_2217159
  simp only [CollatzResearch.WordTrace]
  refine ⟨80866432174619078455598531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53910954783079385637065687 80866432174619078455598531)
  ·
    refine ⟨121299648261928617683397797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80866432174619078455598531 121299648261928617683397797)
    ·
      refine ⟨22743684049111615815637087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 121299648261928617683397797 22743684049111615815637087)
      ·
        refine ⟨34115526073667423723455631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22743684049111615815637087 34115526073667423723455631)
        ·
          refine ⟨51173289110501135585183447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34115526073667423723455631 51173289110501135585183447)
          ·
            refine ⟨76759933665751703377775171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51173289110501135585183447 76759933665751703377775171)
            ·
              refine ⟨115139900498627555066662757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 76759933665751703377775171 115139900498627555066662757)
              ·
                refine ⟨21588731343492666574999267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 115139900498627555066662757 21588731343492666574999267)
                ·
                  refine ⟨32383097015238999862498901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21588731343492666574999267 32383097015238999862498901)
                  ·
                    refine ⟨379489418147332029638659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 32383097015238999862498901 379489418147332029638659)
                    ·
                      rfl

theorem cell23_2217159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 4, 1, 8].length) (baseStart_2217159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2217159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2217159 prefixEnd_2217159 := by exact prefixLift 2217159
  have htrace : WordTrace (prefixWord ++ tailWord_2217159) baseStart_2217159 baseEnd_2217159 := by
    simpa [prefixWord, tailWord_2217159, baseEnd_2217159] using wordTrace_append hprefix tailTrace_2217159
  have hstable : (prefixWord ++ tailWord_2217159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2217159).length < 2 ^ (prefixWord ++ tailWord_2217159).sum := by decide
  have hdescent : baseEnd_2217159 < baseStart_2217159 := by decide
  rcases family_descends (prefixWord ++ tailWord_2217159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2217170 : List Nat := [3, 2, 2, 2, 1, 1, 1, 5, 1, 3, 2]
def baseStart_2217170 : Nat := 118140960795 + 2217170 * 2 ^ 59
def prefixEnd_2217170 : Nat := 4983230072969 + 3 ^ 40 * 2217170 * 2
def baseEnd_2217170 : Nat := 1138473902729195545878427

theorem tailTrace_2217170 : CollatzResearch.WordTrace tailWord_2217170 prefixEnd_2217170 1138473902729195545878427 := by
  unfold tailWord_2217170
  simp only [CollatzResearch.WordTrace]
  refine ⟨20216708344394806833562241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53911222251719484889499309 20216708344394806833562241)
  ·
    refine ⟨15162531258296105125171681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20216708344394806833562241 15162531258296105125171681)
    ·
      refine ⟨11371898443722078843878761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15162531258296105125171681 11371898443722078843878761)
      ·
        refine ⟨8528923832791559132909071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11371898443722078843878761 8528923832791559132909071)
        ·
          refine ⟨12793385749187338699363607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8528923832791559132909071 12793385749187338699363607)
          ·
            refine ⟨19190078623781008049045411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12793385749187338699363607 19190078623781008049045411)
            ·
              refine ⟨28785117935671512073568117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19190078623781008049045411 28785117935671512073568117)
              ·
                refine ⟨2698604806469204256897011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 28785117935671512073568117 2698604806469204256897011)
                ·
                  refine ⟨4047907209703806385345517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2698604806469204256897011 4047907209703806385345517)
                  ·
                    refine ⟨1517965203638927394504569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4047907209703806385345517 1517965203638927394504569)
                    ·
                      refine ⟨1138473902729195545878427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1517965203638927394504569 1138473902729195545878427)
                      ·
                        rfl

theorem cell23_2217170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 5, 1, 3, 2].length) (baseStart_2217170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2217170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2217170 prefixEnd_2217170 := by exact prefixLift 2217170
  have htrace : WordTrace (prefixWord ++ tailWord_2217170) baseStart_2217170 baseEnd_2217170 := by
    simpa [prefixWord, tailWord_2217170, baseEnd_2217170] using wordTrace_append hprefix tailTrace_2217170
  have hstable : (prefixWord ++ tailWord_2217170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2217170).length < 2 ^ (prefixWord ++ tailWord_2217170).sum := by decide
  have hdescent : baseEnd_2217170 < baseStart_2217170 := by decide
  rcases family_descends (prefixWord ++ tailWord_2217170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2217206 : List Nat := [5, 1, 1, 1, 1, 1, 1, 3, 9]
def baseStart_2217206 : Nat := 118140960795 + 2217206 * 2 ^ 59
def prefixEnd_2217206 : Nat := 4983230072969 + 3 ^ 40 * 2217206 * 2
def baseEnd_2217206 : Nat := 126499154225861933892029

theorem tailTrace_2217206 : CollatzResearch.WordTrace tailWord_2217206 prefixEnd_2217206 126499154225861933892029 := by
  unfold tailWord_2217206
  simp only [CollatzResearch.WordTrace]
  refine ⟨5054259150340550342659967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 53912097603632536988372981 5054259150340550342659967)
  ·
    refine ⟨7581388725510825513989951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5054259150340550342659967 7581388725510825513989951)
    ·
      refine ⟨11372083088266238270984927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7581388725510825513989951 11372083088266238270984927)
      ·
        refine ⟨17058124632399357406477391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11372083088266238270984927 17058124632399357406477391)
        ·
          refine ⟨25587186948599036109716087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17058124632399357406477391 25587186948599036109716087)
          ·
            refine ⟨38380780422898554164574131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25587186948599036109716087 38380780422898554164574131)
            ·
              refine ⟨57571170634347831246861197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38380780422898554164574131 57571170634347831246861197)
              ·
                refine ⟨21589188987880436717572949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 57571170634347831246861197 21589188987880436717572949)
                ·
                  refine ⟨126499154225861933892029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 21589188987880436717572949 126499154225861933892029)
                  ·
                    rfl

theorem cell23_2217206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 3, 9].length) (baseStart_2217206 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2217206 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2217206 prefixEnd_2217206 := by exact prefixLift 2217206
  have htrace : WordTrace (prefixWord ++ tailWord_2217206) baseStart_2217206 baseEnd_2217206 := by
    simpa [prefixWord, tailWord_2217206, baseEnd_2217206] using wordTrace_append hprefix tailTrace_2217206
  have hstable : (prefixWord ++ tailWord_2217206).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2217206).length < 2 ^ (prefixWord ++ tailWord_2217206).sum := by decide
  have hdescent : baseEnd_2217206 < baseStart_2217206 := by decide
  rcases family_descends (prefixWord ++ tailWord_2217206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2217216 : List Nat := [2, 1, 1, 2, 1, 1, 3, 2, 4, 3, 3]
def baseStart_2217216 : Nat := 118140960795 + 2217216 * 2 ^ 59
def prefixEnd_2217216 : Nat := 4983230072969 + 3 ^ 40 * 2217216 * 2
def baseEnd_2217216 : Nat := 1138497522839302365903215

theorem tailTrace_2217216 : CollatzResearch.WordTrace tailWord_2217216 prefixEnd_2217216 1138497522839302365903215 := by
  unfold tailWord_2217216
  simp only [CollatzResearch.WordTrace]
  refine ⟨40434255567706288595211751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53912340756941718126949001 40434255567706288595211751)
  ·
    refine ⟨60651383351559432892817627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40434255567706288595211751 60651383351559432892817627)
    ·
      refine ⟨90977075027339149339226441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60651383351559432892817627 90977075027339149339226441)
      ·
        refine ⟨68232806270504362004419831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 90977075027339149339226441 68232806270504362004419831)
        ·
          refine ⟨102349209405756543006629747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68232806270504362004419831 102349209405756543006629747)
          ·
            refine ⟨153523814108634814509944621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 102349209405756543006629747 153523814108634814509944621)
            ·
              refine ⟨57571430290738055441229233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 153523814108634814509944621 57571430290738055441229233)
              ·
                refine ⟨43178572718053541580921925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 57571430290738055441229233 43178572718053541580921925)
                ·
                  refine ⟨8095982384635039046422861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 43178572718053541580921925 8095982384635039046422861)
                  ·
                    refine ⟨3035993394238139642408573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8095982384635039046422861 3035993394238139642408573)
                    ·
                      refine ⟨1138497522839302365903215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3035993394238139642408573 1138497522839302365903215)
                      ·
                        rfl

theorem cell23_2217216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 2, 4, 3, 3].length) (baseStart_2217216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2217216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2217216 prefixEnd_2217216 := by exact prefixLift 2217216
  have htrace : WordTrace (prefixWord ++ tailWord_2217216) baseStart_2217216 baseEnd_2217216 := by
    simpa [prefixWord, tailWord_2217216, baseEnd_2217216] using wordTrace_append hprefix tailTrace_2217216
  have hstable : (prefixWord ++ tailWord_2217216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2217216).length < 2 ^ (prefixWord ++ tailWord_2217216).sum := by decide
  have hdescent : baseEnd_2217216 < baseStart_2217216 := by decide
  rcases family_descends (prefixWord ++ tailWord_2217216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2217240 : List Nat := [2, 1, 2, 3, 1, 3, 4, 2, 5]
def baseStart_2217240 : Nat := 118140960795 + 2217240 * 2 ^ 59
def prefixEnd_2217240 : Nat := 4983230072969 + 3 ^ 40 * 2217240 * 2
def baseEnd_2217240 : Nat := 126501094041667808000345

theorem tailTrace_2217240 : CollatzResearch.WordTrace tailWord_2217240 prefixEnd_2217240 126501094041667808000345 := by
  unfold tailWord_2217240
  simp only [CollatzResearch.WordTrace]
  refine ⟨40434693243662814644648587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53912924324883752859531449 40434693243662814644648587)
  ·
    refine ⟨60652039865494221966972881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40434693243662814644648587 60652039865494221966972881)
    ·
      refine ⟨45489029899120666475229661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60652039865494221966972881 45489029899120666475229661)
      ·
        refine ⟨17058386212170249928211123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45489029899120666475229661 17058386212170249928211123)
        ·
          refine ⟨25587579318255374892316685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17058386212170249928211123 25587579318255374892316685)
          ·
            refine ⟨9595342244345765584618757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25587579318255374892316685 9595342244345765584618757)
            ·
              refine ⟨1799126670814831047116017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9595342244345765584618757 1799126670814831047116017)
              ·
                refine ⟨1349345003111123285337013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1799126670814831047116017 1349345003111123285337013)
                ·
                  refine ⟨126501094041667808000345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1349345003111123285337013 126501094041667808000345)
                  ·
                    rfl

theorem cell23_2217240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 4, 2, 5].length) (baseStart_2217240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2217240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2217240 prefixEnd_2217240 := by exact prefixLift 2217240
  have htrace : WordTrace (prefixWord ++ tailWord_2217240) baseStart_2217240 baseEnd_2217240 := by
    simpa [prefixWord, tailWord_2217240, baseEnd_2217240] using wordTrace_append hprefix tailTrace_2217240
  have hstable : (prefixWord ++ tailWord_2217240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2217240).length < 2 ^ (prefixWord ++ tailWord_2217240).sum := by decide
  have hdescent : baseEnd_2217240 < baseStart_2217240 := by decide
  rcases family_descends (prefixWord ++ tailWord_2217240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2217250 : List Nat := [3, 3, 1, 1, 4, 1, 1, 1, 2, 3, 3]
def baseStart_2217250 : Nat := 118140960795 + 2217250 * 2 ^ 59
def prefixEnd_2217250 : Nat := 4983230072969 + 3 ^ 40 * 2217250 * 2
def baseEnd_2217250 : Nat := 1138514981181555232878059

theorem tailTrace_2217250 : CollatzResearch.WordTrace tailWord_2217250 prefixEnd_2217250 1138514981181555232878059 := by
  unfold tailWord_2217250
  simp only [CollatzResearch.WordTrace]
  refine ⟨20217437804322350249290301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53913167478192933998107469 20217437804322350249290301)
  ·
    refine ⟨7581539176620881343483863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20217437804322350249290301 7581539176620881343483863)
    ·
      refine ⟨11372308764931322015225795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7581539176620881343483863 11372308764931322015225795)
      ·
        refine ⟨17058463147396983022838693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11372308764931322015225795 17058463147396983022838693)
        ·
          refine ⟨3198461840136934316782255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17058463147396983022838693 3198461840136934316782255)
          ·
            refine ⟨4797692760205401475173383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3198461840136934316782255 4797692760205401475173383)
            ·
              refine ⟨7196539140308102212760075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4797692760205401475173383 7196539140308102212760075)
              ·
                refine ⟨10794808710462153319140113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7196539140308102212760075 10794808710462153319140113)
                ·
                  refine ⟨8096106532846614989355085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10794808710462153319140113 8096106532846614989355085)
                  ·
                    refine ⟨3036039949817480621008157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8096106532846614989355085 3036039949817480621008157)
                    ·
                      refine ⟨1138514981181555232878059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3036039949817480621008157 1138514981181555232878059)
                      ·
                        rfl

theorem cell23_2217250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 1, 1, 2, 3, 3].length) (baseStart_2217250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2217250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2217250 prefixEnd_2217250 := by exact prefixLift 2217250
  have htrace : WordTrace (prefixWord ++ tailWord_2217250) baseStart_2217250 baseEnd_2217250 := by
    simpa [prefixWord, tailWord_2217250, baseEnd_2217250] using wordTrace_append hprefix tailTrace_2217250
  have hstable : (prefixWord ++ tailWord_2217250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2217250).length < 2 ^ (prefixWord ++ tailWord_2217250).sum := by decide
  have hdescent : baseEnd_2217250 < baseStart_2217250 := by decide
  rcases family_descends (prefixWord ++ tailWord_2217250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2217296 : List Nat := [2, 1, 1, 1, 1, 5, 3, 1, 8]
def baseStart_2217296 : Nat := 118140960795 + 2217296 * 2 ^ 59
def prefixEnd_2217296 : Nat := 4983230072969 + 3 ^ 40 * 2217296 * 2
def baseEnd_2217296 : Nat := 126504289032406894766983

theorem tailTrace_2217296 : CollatzResearch.WordTrace tailWord_2217296 prefixEnd_2217296 126504289032406894766983 := by
  unfold tailWord_2217296
  simp only [CollatzResearch.WordTrace]
  refine ⟨40435714487561375426667871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53914285983415167235557161 40435714487561375426667871)
  ·
    refine ⟨60653571731342063140001807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40435714487561375426667871 60653571731342063140001807)
    ·
      refine ⟨90980357597013094710002711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60653571731342063140001807 90980357597013094710002711)
      ·
        refine ⟨136470536395519642065004067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90980357597013094710002711 136470536395519642065004067)
        ·
          refine ⟨204705804593279463097506101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 136470536395519642065004067 204705804593279463097506101)
          ·
            refine ⟨19191169180619949665391197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 204705804593279463097506101 19191169180619949665391197)
            ·
              refine ⟨7196688442732481124521699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19191169180619949665391197 7196688442732481124521699)
              ·
                refine ⟨10795032664098721686782549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7196688442732481124521699 10795032664098721686782549)
                ·
                  refine ⟨126504289032406894766983, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 10795032664098721686782549 126504289032406894766983)
                  ·
                    rfl

theorem cell23_2217296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 3, 1, 8].length) (baseStart_2217296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2217296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2217296 prefixEnd_2217296 := by exact prefixLift 2217296
  have htrace : WordTrace (prefixWord ++ tailWord_2217296) baseStart_2217296 baseEnd_2217296 := by
    simpa [prefixWord, tailWord_2217296, baseEnd_2217296] using wordTrace_append hprefix tailTrace_2217296
  have hstable : (prefixWord ++ tailWord_2217296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2217296).length < 2 ^ (prefixWord ++ tailWord_2217296).sum := by decide
  have hdescent : baseEnd_2217296 < baseStart_2217296 := by decide
  rcases family_descends (prefixWord ++ tailWord_2217296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2217300 : List Nat := [2, 4, 1, 1, 2, 1, 4, 1, 3, 4]
def baseStart_2217300 : Nat := 118140960795 + 2217300 * 2 ^ 59
def prefixEnd_2217300 : Nat := 4983230072969 + 3 ^ 40 * 2217300 * 2
def baseEnd_2217300 : Nat := 379513551738093345750943

theorem tailTrace_2217300 : CollatzResearch.WordTrace tailWord_2217300 prefixEnd_2217300 379513551738093345750943 := by
  unfold tailWord_2217300
  simp only [CollatzResearch.WordTrace]
  refine ⟨40435787433554129768240677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53914383244738839690987569 40435787433554129768240677)
  ·
    refine ⟨7581710143791399331545127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 40435787433554129768240677 7581710143791399331545127)
    ·
      refine ⟨11372565215687098997317691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7581710143791399331545127 11372565215687098997317691)
      ·
        refine ⟨17058847823530648495976537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11372565215687098997317691 17058847823530648495976537)
        ·
          refine ⟨12794135867647986371982403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17058847823530648495976537 12794135867647986371982403)
          ·
            refine ⟨19191203801471979557973605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12794135867647986371982403 19191203801471979557973605)
            ·
              refine ⟨3598350712775996167120051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19191203801471979557973605 3598350712775996167120051)
              ·
                refine ⟨5397526069163994250680077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3598350712775996167120051 5397526069163994250680077)
                ·
                  refine ⟨2024072275936497844005029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5397526069163994250680077 2024072275936497844005029)
                  ·
                    refine ⟨379513551738093345750943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2024072275936497844005029 379513551738093345750943)
                    ·
                      rfl

theorem cell23_2217300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 4, 1, 3, 4].length) (baseStart_2217300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2217300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2217300 prefixEnd_2217300 := by exact prefixLift 2217300
  have htrace : WordTrace (prefixWord ++ tailWord_2217300) baseStart_2217300 baseEnd_2217300 := by
    simpa [prefixWord, tailWord_2217300, baseEnd_2217300] using wordTrace_append hprefix tailTrace_2217300
  have hstable : (prefixWord ++ tailWord_2217300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2217300).length < 2 ^ (prefixWord ++ tailWord_2217300).sum := by decide
  have hdescent : baseEnd_2217300 < baseStart_2217300 := by decide
  rcases family_descends (prefixWord ++ tailWord_2217300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2217400 : List Nat := [2, 1, 2, 1, 2, 2, 2, 5, 1, 2, 3]
def baseStart_2217400 : Nat := 118140960795 + 2217400 * 2 ^ 59
def prefixEnd_2217400 : Nat := 4983230072969 + 3 ^ 40 * 2217400 * 2
def baseEnd_2217400 : Nat := 1138592003279729646002369

theorem tailTrace_2217400 : CollatzResearch.WordTrace tailWord_2217400 prefixEnd_2217400 1138592003279729646002369 := by
  unfold tailWord_2217400
  simp only [CollatzResearch.WordTrace]
  refine ⟨40437611083372988307560827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53916814777830651076747769 40437611083372988307560827)
  ·
    refine ⟨60656416625059482461341241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40437611083372988307560827 60656416625059482461341241)
    ·
      refine ⟨45492312468794611846005931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60656416625059482461341241 45492312468794611846005931)
      ·
        refine ⟨68238468703191917769008897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45492312468794611846005931 68238468703191917769008897)
        ·
          refine ⟨51178851527393938326756673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 68238468703191917769008897 51178851527393938326756673)
          ·
            refine ⟨38384138645545453745067505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51178851527393938326756673 38384138645545453745067505)
            ·
              refine ⟨28788103984159090308800629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38384138645545453745067505 28788103984159090308800629)
              ·
                refine ⟨2698884748514914716450059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 28788103984159090308800629 2698884748514914716450059)
                ·
                  refine ⟨4048327122772372074675089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2698884748514914716450059 4048327122772372074675089)
                  ·
                    refine ⟨3036245342079279056006317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4048327122772372074675089 3036245342079279056006317)
                    ·
                      refine ⟨1138592003279729646002369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3036245342079279056006317 1138592003279729646002369)
                      ·
                        rfl

theorem cell23_2217400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 5, 1, 2, 3].length) (baseStart_2217400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2217400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2217400 prefixEnd_2217400 := by exact prefixLift 2217400
  have htrace : WordTrace (prefixWord ++ tailWord_2217400) baseStart_2217400 baseEnd_2217400 := by
    simpa [prefixWord, tailWord_2217400, baseEnd_2217400] using wordTrace_append hprefix tailTrace_2217400
  have hstable : (prefixWord ++ tailWord_2217400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2217400).length < 2 ^ (prefixWord ++ tailWord_2217400).sum := by decide
  have hdescent : baseEnd_2217400 < baseStart_2217400 := by decide
  rcases family_descends (prefixWord ++ tailWord_2217400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2217420 : List Nat := [2, 2, 1, 4, 2, 3, 1, 8]
def baseStart_2217420 : Nat := 118140960795 + 2217420 * 2 ^ 59
def prefixEnd_2217420 : Nat := 4983230072969 + 3 ^ 40 * 2217420 * 2
def baseEnd_2217420 : Nat := 42170454551585909916751

theorem tailTrace_2217420 : CollatzResearch.WordTrace tailWord_2217420 prefixEnd_2217420 42170454551585909916751 := by
  unfold tailWord_2217420
  simp only [CollatzResearch.WordTrace]
  refine ⟨40437975813336760015424857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53917301084449013353899809 40437975813336760015424857)
  ·
    refine ⟨30328481860002570011568643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40437975813336760015424857 30328481860002570011568643)
    ·
      refine ⟨45492722790003855017352965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30328481860002570011568643 45492722790003855017352965)
      ·
        refine ⟨8529885523125722815753681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 45492722790003855017352965 8529885523125722815753681)
        ·
          refine ⟨6397414142344292111815261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8529885523125722815753681 6397414142344292111815261)
          ·
            refine ⟨2399030303379109541930723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6397414142344292111815261 2399030303379109541930723)
            ·
              refine ⟨3598545455068664312896085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2399030303379109541930723 3598545455068664312896085)
              ·
                refine ⟨42170454551585909916751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3598545455068664312896085 42170454551585909916751)
                ·
                  rfl

theorem cell23_2217420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 3, 1, 8].length) (baseStart_2217420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2217420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2217420 prefixEnd_2217420 := by exact prefixLift 2217420
  have htrace : WordTrace (prefixWord ++ tailWord_2217420) baseStart_2217420 baseEnd_2217420 := by
    simpa [prefixWord, tailWord_2217420, baseEnd_2217420] using wordTrace_append hprefix tailTrace_2217420
  have hstable : (prefixWord ++ tailWord_2217420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2217420).length < 2 ^ (prefixWord ++ tailWord_2217420).sum := by decide
  have hdescent : baseEnd_2217420 < baseStart_2217420 := by decide
  rcases family_descends (prefixWord ++ tailWord_2217420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2217464 : List Nat := [2, 1, 2, 1, 1, 7, 1, 2, 2, 1, 3]
def baseStart_2217464 : Nat := 118140960795 + 2217464 * 2 ^ 59
def prefixEnd_2217464 : Nat := 4983230072969 + 3 ^ 40 * 2217464 * 2
def baseEnd_2217464 : Nat := 1138624866041617395602075

theorem tailTrace_2217464 : CollatzResearch.WordTrace tailWord_2217464 prefixEnd_2217464 1138624866041617395602075 := by
  unfold tailWord_2217464
  simp only [CollatzResearch.WordTrace]
  refine ⟨40438778219257057772725723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53918370959009410363634297 40438778219257057772725723)
  ·
    refine ⟨60658167328885586659088585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40438778219257057772725723 60658167328885586659088585)
    ·
      refine ⟨45493625496664189994316439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60658167328885586659088585 45493625496664189994316439)
      ·
        refine ⟨68240438244996284991474659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45493625496664189994316439 68240438244996284991474659)
        ·
          refine ⟨102360657367494427487211989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68240438244996284991474659 102360657367494427487211989)
          ·
            refine ⟨2399077907050650644231531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 102360657367494427487211989 2399077907050650644231531)
            ·
              refine ⟨3598616860575975966347297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2399077907050650644231531 3598616860575975966347297)
              ·
                refine ⟨2698962645431981974760473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3598616860575975966347297 2698962645431981974760473)
                ·
                  refine ⟨2024221984073986481070355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2698962645431981974760473 2024221984073986481070355)
                  ·
                    refine ⟨3036332976110979721605533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2024221984073986481070355 3036332976110979721605533)
                    ·
                      refine ⟨1138624866041617395602075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3036332976110979721605533 1138624866041617395602075)
                      ·
                        rfl

theorem cell23_2217464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 7, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 7, 1, 2, 2, 1, 3].length) (baseStart_2217464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2217464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2217464 prefixEnd_2217464 := by exact prefixLift 2217464
  have htrace : WordTrace (prefixWord ++ tailWord_2217464) baseStart_2217464 baseEnd_2217464 := by
    simpa [prefixWord, tailWord_2217464, baseEnd_2217464] using wordTrace_append hprefix tailTrace_2217464
  have hstable : (prefixWord ++ tailWord_2217464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2217464).length < 2 ^ (prefixWord ++ tailWord_2217464).sum := by decide
  have hdescent : baseEnd_2217464 < baseStart_2217464 := by decide
  rcases family_descends (prefixWord ++ tailWord_2217464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2217478 : List Nat := [6, 2, 1, 1, 2, 2, 1, 1, 1, 2, 4]
def baseStart_2217478 : Nat := 118140960795 + 2217478 * 2 ^ 59
def prefixEnd_2217478 : Nat := 4983230072969 + 3 ^ 40 * 2217478 * 2
def baseEnd_2217478 : Nat := 1138632054770780340827011

theorem tailTrace_2217478 : CollatzResearch.WordTrace tailWord_2217478 prefixEnd_2217478 1138632054770780340827011 := by
  unfold tailWord_2217478
  simp only [CollatzResearch.WordTrace]
  refine ⟨2527439595639481123014409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 53918711373642263957640725 2527439595639481123014409)
  ·
    refine ⟨1895579696729610842260807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2527439595639481123014409 1895579696729610842260807)
    ·
      refine ⟨2843369545094416263391211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1895579696729610842260807 2843369545094416263391211)
      ·
        refine ⟨4265054317641624395086817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2843369545094416263391211 4265054317641624395086817)
        ·
          refine ⟨3198790738231218296315113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4265054317641624395086817 3198790738231218296315113)
          ·
            refine ⟨2399093053673413722236335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3198790738231218296315113 2399093053673413722236335)
            ·
              refine ⟨3598639580510120583354503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2399093053673413722236335 3598639580510120583354503)
              ·
                refine ⟨5397959370765180875031755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3598639580510120583354503 5397959370765180875031755)
                ·
                  refine ⟨8096939056147771312547633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5397959370765180875031755 8096939056147771312547633)
                  ·
                    refine ⟨6072704292110828484410725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8096939056147771312547633 6072704292110828484410725)
                    ·
                      refine ⟨1138632054770780340827011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6072704292110828484410725 1138632054770780340827011)
                      ·
                        rfl

theorem cell23_2217478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 2, 1, 1, 1, 2, 4].length) (baseStart_2217478 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2217478 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2217478 prefixEnd_2217478 := by exact prefixLift 2217478
  have htrace : WordTrace (prefixWord ++ tailWord_2217478) baseStart_2217478 baseEnd_2217478 := by
    simpa [prefixWord, tailWord_2217478, baseEnd_2217478] using wordTrace_append hprefix tailTrace_2217478
  have hstable : (prefixWord ++ tailWord_2217478).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2217478).length < 2 ^ (prefixWord ++ tailWord_2217478).sum := by decide
  have hdescent : baseEnd_2217478 < baseStart_2217478 := by decide
  rcases family_descends (prefixWord ++ tailWord_2217478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2217504 : List Nat := [2, 1, 1, 6, 1, 1, 1, 2, 4, 2, 2]
def baseStart_2217504 : Nat := 118140960795 + 2217504 * 2 ^ 59
def prefixEnd_2217504 : Nat := 4983230072969 + 3 ^ 40 * 2217504 * 2
def baseEnd_2217504 : Nat := 1138645405267797239101891

theorem tailTrace_2217504 : CollatzResearch.WordTrace tailWord_2217504 prefixEnd_2217504 1138645405267797239101891 := by
  unfold tailWord_2217504
  simp only [CollatzResearch.WordTrace]
  refine ⟨40439507679184601188453783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53919343572246134917938377 40439507679184601188453783)
  ·
    refine ⟨60659261518776901782680675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40439507679184601188453783 60659261518776901782680675)
    ·
      refine ⟨90988892278165352674021013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60659261518776901782680675 90988892278165352674021013)
      ·
        refine ⟨4265104325539000906594735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 90988892278165352674021013 4265104325539000906594735)
        ·
          refine ⟨6397656488308501359892103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4265104325539000906594735 6397656488308501359892103)
          ·
            refine ⟨9596484732462752039838155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6397656488308501359892103 9596484732462752039838155)
            ·
              refine ⟨14394727098694128059757233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9596484732462752039838155 14394727098694128059757233)
              ·
                refine ⟨10796045324020596044817925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14394727098694128059757233 10796045324020596044817925)
                ·
                  refine ⟨2024258498253861758403361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10796045324020596044817925 2024258498253861758403361)
                  ·
                    refine ⟨1518193873690396318802521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2024258498253861758403361 1518193873690396318802521)
                    ·
                      refine ⟨1138645405267797239101891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1518193873690396318802521 1138645405267797239101891)
                      ·
                        rfl

theorem cell23_2217504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 1, 2, 4, 2, 2].length) (baseStart_2217504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2217504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2217504 prefixEnd_2217504 := by exact prefixLift 2217504
  have htrace : WordTrace (prefixWord ++ tailWord_2217504) baseStart_2217504 baseEnd_2217504 := by
    simpa [prefixWord, tailWord_2217504, baseEnd_2217504] using wordTrace_append hprefix tailTrace_2217504
  have hstable : (prefixWord ++ tailWord_2217504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2217504).length < 2 ^ (prefixWord ++ tailWord_2217504).sum := by decide
  have hdescent : baseEnd_2217504 < baseStart_2217504 := by decide
  rcases family_descends (prefixWord ++ tailWord_2217504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2217580 : List Nat := [2, 2, 1, 1, 3, 1, 1, 2, 3, 4, 3]
def baseStart_2217580 : Nat := 118140960795 + 2217580 * 2 ^ 59
def prefixEnd_2217580 : Nat := 4983230072969 + 3 ^ 40 * 2217580 * 2
def baseEnd_2217580 : Nat := 1138684429797538941751541

theorem tailTrace_2217580 : CollatzResearch.WordTrace tailWord_2217580 prefixEnd_2217580 1138684429797538941751541 := by
  unfold tailWord_2217580
  simp only [CollatzResearch.WordTrace]
  refine ⟨40440893653046933678337097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53921191537395911571116129 40440893653046933678337097)
  ·
    refine ⟨30330670239785200258752823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40440893653046933678337097 30330670239785200258752823)
    ·
      refine ⟨45496005359677800388129235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30330670239785200258752823 45496005359677800388129235)
      ·
        refine ⟨68244008039516700582193853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45496005359677800388129235 68244008039516700582193853)
        ·
          refine ⟨25591503014818762718322695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 68244008039516700582193853 25591503014818762718322695)
          ·
            refine ⟨38387254522228144077484043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25591503014818762718322695 38387254522228144077484043)
            ·
              refine ⟨57580881783342216116226065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38387254522228144077484043 57580881783342216116226065)
              ·
                refine ⟨43185661337506662087169549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 57580881783342216116226065 43185661337506662087169549)
                ·
                  refine ⟨16194623001564998282688581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 43185661337506662087169549 16194623001564998282688581)
                  ·
                    refine ⟨3036491812793437178004109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16194623001564998282688581 3036491812793437178004109)
                    ·
                      refine ⟨1138684429797538941751541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3036491812793437178004109 1138684429797538941751541)
                      ·
                        rfl

theorem cell23_2217580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 4, 3].length) (baseStart_2217580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2217580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2217580 prefixEnd_2217580 := by exact prefixLift 2217580
  have htrace : WordTrace (prefixWord ++ tailWord_2217580) baseStart_2217580 baseEnd_2217580 := by
    simpa [prefixWord, tailWord_2217580, baseEnd_2217580] using wordTrace_append hprefix tailTrace_2217580
  have hstable : (prefixWord ++ tailWord_2217580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2217580).length < 2 ^ (prefixWord ++ tailWord_2217580).sum := by decide
  have hdescent : baseEnd_2217580 < baseStart_2217580 := by decide
  rcases family_descends (prefixWord ++ tailWord_2217580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2217600 : List Nat := [2, 1, 1, 2, 1, 4, 1, 5, 6]
def baseStart_2217600 : Nat := 118140960795 + 2217600 * 2 ^ 59
def prefixEnd_2217600 : Nat := 4983230072969 + 3 ^ 40 * 2217600 * 2
def baseEnd_2217600 : Nat := 126521633267847651500161

theorem tailTrace_2217600 : CollatzResearch.WordTrace tailWord_2217600 prefixEnd_2217600 126521633267847651500161 := by
  unfold tailWord_2217600
  simp only [CollatzResearch.WordTrace]
  refine ⟨40441258383010705386201127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53921677844014273848268169 40441258383010705386201127)
  ·
    refine ⟨60661887574516058079301691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40441258383010705386201127 60661887574516058079301691)
    ·
      refine ⟨90992831361774087118952537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60661887574516058079301691 90992831361774087118952537)
      ·
        refine ⟨68244623521330565339214403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 90992831361774087118952537 68244623521330565339214403)
        ·
          refine ⟨102366935281995848008821605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68244623521330565339214403 102366935281995848008821605)
          ·
            refine ⟨19193800365374221501654051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 102366935281995848008821605 19193800365374221501654051)
            ·
              refine ⟨28790700548061332252481077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19193800365374221501654051 28790700548061332252481077)
              ·
                refine ⟨2699128176380749898670101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 28790700548061332252481077 2699128176380749898670101)
                ·
                  refine ⟨126521633267847651500161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2699128176380749898670101 126521633267847651500161)
                  ·
                    rfl

theorem cell23_2217600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 5, 6].length) (baseStart_2217600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2217600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2217600 prefixEnd_2217600 := by exact prefixLift 2217600
  have htrace : WordTrace (prefixWord ++ tailWord_2217600) baseStart_2217600 baseEnd_2217600 := by
    simpa [prefixWord, tailWord_2217600, baseEnd_2217600] using wordTrace_append hprefix tailTrace_2217600
  have hstable : (prefixWord ++ tailWord_2217600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2217600).length < 2 ^ (prefixWord ++ tailWord_2217600).sum := by decide
  have hdescent : baseEnd_2217600 < baseStart_2217600 := by decide
  rcases family_descends (prefixWord ++ tailWord_2217600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2217604 : List Nat := [2, 3, 2, 1, 4, 1, 1, 2, 3, 4]
def baseStart_2217604 : Nat := 118140960795 + 2217604 * 2 ^ 59
def prefixEnd_2217604 : Nat := 4983230072969 + 3 ^ 40 * 2217604 * 2
def baseEnd_2217604 : Nat := 379565584444415615950477

theorem tailTrace_2217604 : CollatzResearch.WordTrace tailWord_2217604 prefixEnd_2217604 379565584444415615950477 := by
  unfold tailWord_2217604
  simp only [CollatzResearch.WordTrace]
  refine ⟨40441331329003459727773933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53921775105337946303698577 40441331329003459727773933)
  ·
    refine ⟨15165499248376297397915225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40441331329003459727773933 15165499248376297397915225)
    ·
      refine ⟨11374124436282223048436419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15165499248376297397915225 11374124436282223048436419)
      ·
        refine ⟨17061186654423334572654629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11374124436282223048436419 17061186654423334572654629)
        ·
          refine ⟨3198972497704375232372743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17061186654423334572654629 3198972497704375232372743)
          ·
            refine ⟨4798458746556562848559115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3198972497704375232372743 4798458746556562848559115)
            ·
              refine ⟨7197688119834844272838673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4798458746556562848559115 7197688119834844272838673)
              ·
                refine ⟨5398266089876133204629005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7197688119834844272838673 5398266089876133204629005)
                ·
                  refine ⟨2024349783703549951735877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5398266089876133204629005 2024349783703549951735877)
                  ·
                    refine ⟨379565584444415615950477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2024349783703549951735877 379565584444415615950477)
                    ·
                      rfl

theorem cell23_2217604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 1, 2, 3, 4].length) (baseStart_2217604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2217604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2217604 prefixEnd_2217604 := by exact prefixLift 2217604
  have htrace : WordTrace (prefixWord ++ tailWord_2217604) baseStart_2217604 baseEnd_2217604 := by
    simpa [prefixWord, tailWord_2217604, baseEnd_2217604] using wordTrace_append hprefix tailTrace_2217604
  have hstable : (prefixWord ++ tailWord_2217604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2217604).length < 2 ^ (prefixWord ++ tailWord_2217604).sum := by decide
  have hdescent : baseEnd_2217604 < baseStart_2217604 := by decide
  rcases family_descends (prefixWord ++ tailWord_2217604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2217614 : List Nat := [4, 1, 1, 3, 1, 2, 3, 1, 2, 2, 3]
def baseStart_2217614 : Nat := 118140960795 + 2217614 * 2 ^ 59
def prefixEnd_2217614 : Nat := 4983230072969 + 3 ^ 40 * 2217614 * 2
def baseEnd_2217614 : Nat := 1138701888139791808726385

theorem tailTrace_2217614 : CollatzResearch.WordTrace tailWord_2217614 prefixEnd_2217614 1138701888139791808726385 := by
  unfold tailWord_2217614
  simp only [CollatzResearch.WordTrace]
  refine ⟨10110378423496336395426487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 53922018258647127442274597 10110378423496336395426487)
  ·
    refine ⟨15165567635244504593139731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10110378423496336395426487 15165567635244504593139731)
    ·
      refine ⟨22748351452866756889709597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15165567635244504593139731 22748351452866756889709597)
      ·
        refine ⟨8530631794825033833641099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22748351452866756889709597 8530631794825033833641099)
        ·
          refine ⟨12795947692237550750461649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8530631794825033833641099 12795947692237550750461649)
          ·
            refine ⟨9596960769178163062846237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12795947692237550750461649 9596960769178163062846237)
            ·
              refine ⟨3598860288441811148567339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9596960769178163062846237 3598860288441811148567339)
              ·
                refine ⟨5398290432662716722851009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3598860288441811148567339 5398290432662716722851009)
                ·
                  refine ⟨4048717824497037542138257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5398290432662716722851009 4048717824497037542138257)
                  ·
                    refine ⟨3036538368372778156603693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4048717824497037542138257 3036538368372778156603693)
                    ·
                      refine ⟨1138701888139791808726385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3036538368372778156603693 1138701888139791808726385)
                      ·
                        rfl

theorem cell23_2217614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 3, 1, 2, 2, 3].length) (baseStart_2217614 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2217614 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2217614 prefixEnd_2217614 := by exact prefixLift 2217614
  have htrace : WordTrace (prefixWord ++ tailWord_2217614) baseStart_2217614 baseEnd_2217614 := by
    simpa [prefixWord, tailWord_2217614, baseEnd_2217614] using wordTrace_append hprefix tailTrace_2217614
  have hstable : (prefixWord ++ tailWord_2217614).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2217614).length < 2 ^ (prefixWord ++ tailWord_2217614).sum := by decide
  have hdescent : baseEnd_2217614 < baseStart_2217614 := by decide
  rcases family_descends (prefixWord ++ tailWord_2217614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2217634 : List Nat := [3, 3, 1, 4, 1, 1, 1, 1, 8]
def baseStart_2217634 : Nat := 118140960795 + 2217634 * 2 ^ 59
def prefixEnd_2217634 : Nat := 4983230072969 + 3 ^ 40 * 2217634 * 2
def baseEnd_2217634 : Nat := 126523573083653525608477

theorem tailTrace_2217634 : CollatzResearch.WordTrace tailWord_2217634 prefixEnd_2217634 126523573083653525608477 := by
  unfold tailWord_2217634
  simp only [CollatzResearch.WordTrace]
  refine ⟨20220939211974558644784989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53922504565265489719426637 20220939211974558644784989)
  ·
    refine ⟨7582852204490459491794371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20220939211974558644784989 7582852204490459491794371)
    ·
      refine ⟨11374278306735689237691557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7582852204490459491794371 11374278306735689237691557)
      ·
        refine ⟨2132677182512941732067167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11374278306735689237691557 2132677182512941732067167)
        ·
          refine ⟨3199015773769412598100751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2132677182512941732067167 3199015773769412598100751)
          ·
            refine ⟨4798523660654118897151127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3199015773769412598100751 4798523660654118897151127)
            ·
              refine ⟨7197785490981178345726691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4798523660654118897151127 7197785490981178345726691)
              ·
                refine ⟨10796678236471767518590037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7197785490981178345726691 10796678236471767518590037)
                ·
                  refine ⟨126523573083653525608477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 10796678236471767518590037 126523573083653525608477)
                  ·
                    rfl

theorem cell23_2217634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 1, 1, 8].length) (baseStart_2217634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2217634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2217634 prefixEnd_2217634 := by exact prefixLift 2217634
  have htrace : WordTrace (prefixWord ++ tailWord_2217634) baseStart_2217634 baseEnd_2217634 := by
    simpa [prefixWord, tailWord_2217634, baseEnd_2217634] using wordTrace_append hprefix tailTrace_2217634
  have hstable : (prefixWord ++ tailWord_2217634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2217634).length < 2 ^ (prefixWord ++ tailWord_2217634).sum := by decide
  have hdescent : baseEnd_2217634 < baseStart_2217634 := by decide
  rcases family_descends (prefixWord ++ tailWord_2217634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2217687 : List Nat := [1, 1, 3, 2, 1, 3, 4, 1, 1, 1, 5]
def baseStart_2217687 : Nat := 118140960795 + 2217687 * 2 ^ 59
def prefixEnd_2217687 : Nat := 4983230072969 + 3 ^ 40 * 2217687 * 2
def baseEnd_2217687 : Nat := 1138739372227570023113549

theorem tailTrace_2217687 : CollatzResearch.WordTrace tailWord_2217687 prefixEnd_2217687 1138739372227570023113549 := by
  unfold tailWord_2217687
  simp only [CollatzResearch.WordTrace]
  refine ⟨80885689916706224630819315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53923793277804149753879543 80885689916706224630819315)
  ·
    refine ⟨121328534875059336946228973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80885689916706224630819315 121328534875059336946228973)
    ·
      refine ⟨45498200578147251354835865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 121328534875059336946228973 45498200578147251354835865)
      ·
        refine ⟨34123650433610438516126899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45498200578147251354835865 34123650433610438516126899)
        ·
          refine ⟨51185475650415657774190349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34123650433610438516126899 51185475650415657774190349)
          ·
            refine ⟨19194553368905871665321381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 51185475650415657774190349 19194553368905871665321381)
            ·
              refine ⟨3598978756669850937247759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19194553368905871665321381 3598978756669850937247759)
              ·
                refine ⟨5398468135004776405871639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3598978756669850937247759 5398468135004776405871639)
                ·
                  refine ⟨8097702202507164608807459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5398468135004776405871639 8097702202507164608807459)
                  ·
                    refine ⟨12146553303760746913211189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8097702202507164608807459 12146553303760746913211189)
                    ·
                      refine ⟨1138739372227570023113549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12146553303760746913211189 1138739372227570023113549)
                      ·
                        rfl

theorem cell23_2217687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 4, 1, 1, 1, 5].length) (baseStart_2217687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2217687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2217687 prefixEnd_2217687 := by exact prefixLift 2217687
  have htrace : WordTrace (prefixWord ++ tailWord_2217687) baseStart_2217687 baseEnd_2217687 := by
    simpa [prefixWord, tailWord_2217687, baseEnd_2217687] using wordTrace_append hprefix tailTrace_2217687
  have hstable : (prefixWord ++ tailWord_2217687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2217687).length < 2 ^ (prefixWord ++ tailWord_2217687).sum := by decide
  have hdescent : baseEnd_2217687 < baseStart_2217687 := by decide
  rcases family_descends (prefixWord ++ tailWord_2217687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2217690 : List Nat := [3, 1, 1, 2, 2, 3, 11]
def baseStart_2217690 : Nat := 118140960795 + 2217690 * 2 ^ 59
def prefixEnd_2217690 : Nat := 4983230072969 + 3 ^ 40 * 2217690 * 2
def baseEnd_2217690 : Nat := 14058529786043623597235

theorem tailTrace_2217690 : CollatzResearch.WordTrace tailWord_2217690 prefixEnd_2217690 14058529786043623597235 := by
  unfold tailWord_2217690
  simp only [CollatzResearch.WordTrace]
  refine ⟨20221449833923839035794631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53923866223796904095452349 20221449833923839035794631)
  ·
    refine ⟨30332174750885758553691947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20221449833923839035794631 30332174750885758553691947)
    ·
      refine ⟨45498262126328637830537921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30332174750885758553691947 45498262126328637830537921)
      ·
        refine ⟨34123696594746478372903441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45498262126328637830537921 34123696594746478372903441)
        ·
          refine ⟨25592772446059858779677581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34123696594746478372903441 25592772446059858779677581)
          ·
            refine ⟨9597289667272447042379093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25592772446059858779677581 9597289667272447042379093)
            ·
              refine ⟨14058529786043623597235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 9597289667272447042379093 14058529786043623597235)
              ·
                rfl

theorem cell23_2217690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 11].length) (baseStart_2217690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2217690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2217690 prefixEnd_2217690 := by exact prefixLift 2217690
  have htrace : WordTrace (prefixWord ++ tailWord_2217690) baseStart_2217690 baseEnd_2217690 := by
    simpa [prefixWord, tailWord_2217690, baseEnd_2217690] using wordTrace_append hprefix tailTrace_2217690
  have hstable : (prefixWord ++ tailWord_2217690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2217690).length < 2 ^ (prefixWord ++ tailWord_2217690).sum := by decide
  have hdescent : baseEnd_2217690 < baseStart_2217690 := by decide
  rcases family_descends (prefixWord ++ tailWord_2217690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2217720 : List Nat := [2, 1, 2, 1, 1, 2, 2, 1, 4, 7]
def baseStart_2217720 : Nat := 118140960795 + 2217720 * 2 ^ 59
def prefixEnd_2217720 : Nat := 4983230072969 + 3 ^ 40 * 2217720 * 2
def baseEnd_2217720 : Nat := 379585439029722798000299

theorem tailTrace_2217720 : CollatzResearch.WordTrace tailWord_2217720 prefixEnd_2217720 379585439029722798000299 := by
  unfold tailWord_2217720
  simp only [CollatzResearch.WordTrace]
  refine ⟨40443446762793335633385307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53924595683724447511180409 40443446762793335633385307)
  ·
    refine ⟨60665170144190003450077961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40443446762793335633385307 60665170144190003450077961)
    ·
      refine ⟨45498877608142502587558471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60665170144190003450077961 45498877608142502587558471)
      ·
        refine ⟨68248316412213753881337707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45498877608142502587558471 68248316412213753881337707)
        ·
          refine ⟨102372474618320630822006561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68248316412213753881337707 102372474618320630822006561)
          ·
            refine ⟨76779355963740473116504921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 102372474618320630822006561 76779355963740473116504921)
            ·
              refine ⟨57584516972805354837378691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 76779355963740473116504921 57584516972805354837378691)
              ·
                refine ⟨86376775459208032256068037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 57584516972805354837378691 86376775459208032256068037)
                ·
                  refine ⟨16195645398601506048012757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 86376775459208032256068037 16195645398601506048012757)
                  ·
                    refine ⟨379585439029722798000299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 16195645398601506048012757 379585439029722798000299)
                    ·
                      rfl

theorem cell23_2217720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 1, 4, 7].length) (baseStart_2217720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2217720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2217720 prefixEnd_2217720 := by exact prefixLift 2217720
  have htrace : WordTrace (prefixWord ++ tailWord_2217720) baseStart_2217720 baseEnd_2217720 := by
    simpa [prefixWord, tailWord_2217720, baseEnd_2217720] using wordTrace_append hprefix tailTrace_2217720
  have hstable : (prefixWord ++ tailWord_2217720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2217720).length < 2 ^ (prefixWord ++ tailWord_2217720).sum := by decide
  have hdescent : baseEnd_2217720 < baseStart_2217720 := by decide
  rcases family_descends (prefixWord ++ tailWord_2217720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2217741 : List Nat := [1, 7, 2, 1, 12]
def baseStart_2217741 : Nat := 118140960795 + 2217741 * 2 ^ 59
def prefixEnd_2217741 : Nat := 4983230072969 + 3 ^ 40 * 2217741 * 2
def baseEnd_2217741 : Nat := 1562094787630881772069

theorem tailTrace_2217741 : CollatzResearch.WordTrace tailWord_2217741 prefixEnd_2217741 1562094787630881772069 := by
  unfold tailWord_2217741
  simp only [CollatzResearch.WordTrace]
  refine ⟨80887659458510591853285077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53925106305673727902190051 80887659458510591853285077)
  ·
    refine ⟨1895804518558841996561369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 80887659458510591853285077 1895804518558841996561369)
    ·
      refine ⟨1421853388919131497421027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1895804518558841996561369 1421853388919131497421027)
      ·
        refine ⟨2132780083378697246131541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1421853388919131497421027 2132780083378697246131541)
        ·
          refine ⟨1562094787630881772069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 2132780083378697246131541 1562094787630881772069)
          ·
            rfl

theorem cell23_2217741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 12].length) (baseStart_2217741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2217741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2217741 prefixEnd_2217741 := by exact prefixLift 2217741
  have htrace : WordTrace (prefixWord ++ tailWord_2217741) baseStart_2217741 baseEnd_2217741 := by
    simpa [prefixWord, tailWord_2217741, baseEnd_2217741] using wordTrace_append hprefix tailTrace_2217741
  have hstable : (prefixWord ++ tailWord_2217741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2217741).length < 2 ^ (prefixWord ++ tailWord_2217741).sum := by decide
  have hdescent : baseEnd_2217741 < baseStart_2217741 := by decide
  rcases family_descends (prefixWord ++ tailWord_2217741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2217751 : List Nat := [1, 1, 3, 4, 2, 1, 1, 4, 2, 1, 3]
def baseStart_2217751 : Nat := 118140960795 + 2217751 * 2 ^ 59
def prefixEnd_2217751 : Nat := 4983230072969 + 3 ^ 40 * 2217751 * 2
def baseEnd_2217751 : Nat := 1138772234989457772713255

theorem tailTrace_2217751 : CollatzResearch.WordTrace tailWord_2217751 prefixEnd_2217751 1138772234989457772713255 := by
  unfold tailWord_2217751
  simp only [CollatzResearch.WordTrace]
  refine ⟨80888024188474363561149107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53925349458982909040766071 80888024188474363561149107)
  ·
    refine ⟨121332036282711545341723661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80888024188474363561149107 121332036282711545341723661)
    ·
      refine ⟨45499513606016829503146373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 121332036282711545341723661 45499513606016829503146373)
      ·
        refine ⟨8531158801128155531839945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 45499513606016829503146373 8531158801128155531839945)
        ·
          refine ⟨6398369100846116648879959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8531158801128155531839945 6398369100846116648879959)
          ·
            refine ⟨9597553651269174973319939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6398369100846116648879959 9597553651269174973319939)
            ·
              refine ⟨14396330476903762459979909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9597553651269174973319939 14396330476903762459979909)
              ·
                refine ⟨2699311964419455461246233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14396330476903762459979909 2699311964419455461246233)
                ·
                  refine ⟨2024483973314591595934675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2699311964419455461246233 2024483973314591595934675)
                  ·
                    refine ⟨3036725959971887393902013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2024483973314591595934675 3036725959971887393902013)
                    ·
                      refine ⟨1138772234989457772713255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3036725959971887393902013 1138772234989457772713255)
                      ·
                        rfl

theorem cell23_2217751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 1, 4, 2, 1, 3].length) (baseStart_2217751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2217751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2217751 prefixEnd_2217751 := by exact prefixLift 2217751
  have htrace : WordTrace (prefixWord ++ tailWord_2217751) baseStart_2217751 baseEnd_2217751 := by
    simpa [prefixWord, tailWord_2217751, baseEnd_2217751] using wordTrace_append hprefix tailTrace_2217751
  have hstable : (prefixWord ++ tailWord_2217751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2217751).length < 2 ^ (prefixWord ++ tailWord_2217751).sum := by decide
  have hdescent : baseEnd_2217751 < baseStart_2217751 := by decide
  rcases family_descends (prefixWord ++ tailWord_2217751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2217758 : List Nat := [4, 3, 2, 2, 1, 2, 1, 8]
def baseStart_2217758 : Nat := 118140960795 + 2217758 * 2 ^ 59
def prefixEnd_2217758 : Nat := 4983230072969 + 3 ^ 40 * 2217758 * 2
def baseEnd_2217758 : Nat := 42176882568668120197249

theorem tailTrace_2217758 : CollatzResearch.WordTrace tailWord_2217758 prefixEnd_2217758 42176882568668120197249 := by
  unfold tailWord_2217758
  simp only [CollatzResearch.WordTrace]
  refine ⟨10111034937431125469581741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 53925519666299335837769285 10111034937431125469581741)
  ·
    refine ⟨3791638101536672051093153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10111034937431125469581741 3791638101536672051093153)
    ·
      refine ⟨2843728576152504038319865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3791638101536672051093153 2843728576152504038319865)
      ·
        refine ⟨2132796432114378028739899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2843728576152504038319865 2132796432114378028739899)
        ·
          refine ⟨3199194648171567043109849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2132796432114378028739899 3199194648171567043109849)
          ·
            refine ⟨2399395986128675282332387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3199194648171567043109849 2399395986128675282332387)
            ·
              refine ⟨3599093979193012923498581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2399395986128675282332387 3599093979193012923498581)
              ·
                refine ⟨42176882568668120197249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3599093979193012923498581 42176882568668120197249)
                ·
                  rfl

theorem cell23_2217758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 2, 1, 8].length) (baseStart_2217758 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2217758 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2217758 prefixEnd_2217758 := by exact prefixLift 2217758
  have htrace : WordTrace (prefixWord ++ tailWord_2217758) baseStart_2217758 baseEnd_2217758 := by
    simpa [prefixWord, tailWord_2217758, baseEnd_2217758] using wordTrace_append hprefix tailTrace_2217758
  have hstable : (prefixWord ++ tailWord_2217758).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2217758).length < 2 ^ (prefixWord ++ tailWord_2217758).sum := by decide
  have hdescent : baseEnd_2217758 < baseStart_2217758 := by decide
  rcases family_descends (prefixWord ++ tailWord_2217758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2217824 : List Nat := [2, 1, 1, 3, 3, 2, 2, 1, 2, 3, 3]
def baseStart_2217824 : Nat := 118140960795 + 2217824 * 2 ^ 59
def prefixEnd_2217824 : Nat := 4983230072969 + 3 ^ 40 * 2217824 * 2
def baseEnd_2217824 : Nat := 1138809719077235987100419

theorem tailTrace_2217824 : CollatzResearch.WordTrace tailWord_2217824 prefixEnd_2217824 1138809719077235987100419 := by
  unfold tailWord_2217824
  simp only [CollatzResearch.WordTrace]
  refine ⟨40445343358604948514278263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53927124478139931352371017 40445343358604948514278263)
  ·
    refine ⟨60668015037907422771417395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40445343358604948514278263 60668015037907422771417395)
    ·
      refine ⟨91002022556861134157126093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60668015037907422771417395 91002022556861134157126093)
      ·
        refine ⟨34125758458822925308922285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 91002022556861134157126093 34125758458822925308922285)
        ·
          refine ⟨12797159422058596990845857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34125758458822925308922285 12797159422058596990845857)
          ·
            refine ⟨9597869566543947743134393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12797159422058596990845857 9597869566543947743134393)
            ·
              refine ⟨7198402174907960807350795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9597869566543947743134393 7198402174907960807350795)
              ·
                refine ⟨10797603262361941211026193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7198402174907960807350795 10797603262361941211026193)
                ·
                  refine ⟨8098202446771455908269645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10797603262361941211026193 8098202446771455908269645)
                  ·
                    refine ⟨3036825917539295965601117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8098202446771455908269645 3036825917539295965601117)
                    ·
                      refine ⟨1138809719077235987100419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3036825917539295965601117 1138809719077235987100419)
                      ·
                        rfl

theorem cell23_2217824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 2, 1, 2, 3, 3].length) (baseStart_2217824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2217824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2217824 prefixEnd_2217824 := by exact prefixLift 2217824
  have htrace : WordTrace (prefixWord ++ tailWord_2217824) baseStart_2217824 baseEnd_2217824 := by
    simpa [prefixWord, tailWord_2217824, baseEnd_2217824] using wordTrace_append hprefix tailTrace_2217824
  have hstable : (prefixWord ++ tailWord_2217824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2217824).length < 2 ^ (prefixWord ++ tailWord_2217824).sum := by decide
  have hdescent : baseEnd_2217824 < baseStart_2217824 := by decide
  rcases family_descends (prefixWord ++ tailWord_2217824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2217931 : List Nat := [1, 1, 1, 1, 3, 4, 2, 3, 3, 1, 3]
def baseStart_2217931 : Nat := 118140960795 + 2217931 * 2 ^ 59
def prefixEnd_2217931 : Nat := 4983230072969 + 3 ^ 40 * 2217931 * 2
def baseEnd_2217931 : Nat := 1138864661507267068462427

theorem tailTrace_2217931 : CollatzResearch.WordTrace tailWord_2217931 prefixEnd_2217931 1138864661507267068462427 := by
  unfold tailWord_2217931
  simp only [CollatzResearch.WordTrace]
  refine ⟨80894589327822254302701647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53929726218548169535134431 80894589327822254302701647)
  ·
    refine ⟨121341883991733381454052471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80894589327822254302701647 121341883991733381454052471)
    ·
      refine ⟨182012825987600072181078707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121341883991733381454052471 182012825987600072181078707)
      ·
        refine ⟨273019238981400108271618061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 182012825987600072181078707 273019238981400108271618061)
        ·
          refine ⟨102382214618025040601856773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 273019238981400108271618061 102382214618025040601856773)
          ·
            refine ⟨19196665240879695112848145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 102382214618025040601856773 19196665240879695112848145)
            ·
              refine ⟨14397498930659771334636109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19196665240879695112848145 14397498930659771334636109)
              ·
                refine ⟨5399062098997414250488541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14397498930659771334636109 5399062098997414250488541)
                ·
                  refine ⟨2024648287124030343933203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5399062098997414250488541 2024648287124030343933203)
                  ·
                    refine ⟨3036972430686045515899805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2024648287124030343933203 3036972430686045515899805)
                    ·
                      refine ⟨1138864661507267068462427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3036972430686045515899805 1138864661507267068462427)
                      ·
                        rfl

theorem cell23_2217931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 2, 3, 3, 1, 3].length) (baseStart_2217931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2217931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2217931 prefixEnd_2217931 := by exact prefixLift 2217931
  have htrace : WordTrace (prefixWord ++ tailWord_2217931) baseStart_2217931 baseEnd_2217931 := by
    simpa [prefixWord, tailWord_2217931, baseEnd_2217931] using wordTrace_append hprefix tailTrace_2217931
  have hstable : (prefixWord ++ tailWord_2217931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2217931).length < 2 ^ (prefixWord ++ tailWord_2217931).sum := by decide
  have hdescent : baseEnd_2217931 < baseStart_2217931 := by decide
  rcases family_descends (prefixWord ++ tailWord_2217931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2217934 : List Nat := [4, 1, 1, 1, 2, 2, 1, 1, 5, 5]
def baseStart_2217934 : Nat := 118140960795 + 2217934 * 2 ^ 59
def prefixEnd_2217934 : Nat := 4983230072969 + 3 ^ 40 * 2217934 * 2
def baseEnd_2217934 : Nat := 379622067316410185574971

theorem tailTrace_2217934 : CollatzResearch.WordTrace tailWord_2217934 prefixEnd_2217934 379622067316410185574971 := by
  unfold tailWord_2217934
  simp only [CollatzResearch.WordTrace]
  refine ⟨10111837343351423226882607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 53929799164540923876707237 10111837343351423226882607)
  ·
    refine ⟨15167756015027134840323911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10111837343351423226882607 15167756015027134840323911)
    ·
      refine ⟨22751634022540702260485867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15167756015027134840323911 22751634022540702260485867)
      ·
        refine ⟨34127451033811053390728801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22751634022540702260485867 34127451033811053390728801)
        ·
          refine ⟨25595588275358290043046601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34127451033811053390728801 25595588275358290043046601)
          ·
            refine ⟨19196691206518717532284951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25595588275358290043046601 19196691206518717532284951)
            ·
              refine ⟨28795036809778076298427427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19196691206518717532284951 28795036809778076298427427)
              ·
                refine ⟨43192555214667114447641141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28795036809778076298427427 43192555214667114447641141)
                ·
                  refine ⟨4049302051375041979466357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 43192555214667114447641141 4049302051375041979466357)
                  ·
                    refine ⟨379622067316410185574971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4049302051375041979466357 379622067316410185574971)
                    ·
                      rfl

theorem cell23_2217934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 1, 5, 5].length) (baseStart_2217934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2217934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2217934 prefixEnd_2217934 := by exact prefixLift 2217934
  have htrace : WordTrace (prefixWord ++ tailWord_2217934) baseStart_2217934 baseEnd_2217934 := by
    simpa [prefixWord, tailWord_2217934, baseEnd_2217934] using wordTrace_append hprefix tailTrace_2217934
  have hstable : (prefixWord ++ tailWord_2217934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2217934).length < 2 ^ (prefixWord ++ tailWord_2217934).sum := by decide
  have hdescent : baseEnd_2217934 < baseStart_2217934 := by decide
  rcases family_descends (prefixWord ++ tailWord_2217934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2217982 : List Nat := [4, 2, 2, 2, 1, 1, 2, 4, 1, 1, 3]
def baseStart_2217982 : Nat := 118140960795 + 2217982 * 2 ^ 59
def prefixEnd_2217982 : Nat := 4983230072969 + 3 ^ 40 * 2217982 * 2
def baseEnd_2217982 : Nat := 1138890849020646368924693

theorem tailTrace_2217982 : CollatzResearch.WordTrace tailWord_2217982 prefixEnd_2217982 1138890849020646368924693 := by
  unfold tailWord_2217982
  simp only [CollatzResearch.WordTrace]
  refine ⟨10112056181329686251601025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 53930966300424993341872133 10112056181329686251601025)
  ·
    refine ⟨7584042135997264688700769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10112056181329686251601025 7584042135997264688700769)
    ·
      refine ⟨5688031601997948516525577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7584042135997264688700769 5688031601997948516525577)
      ·
        refine ⟨4266023701498461387394183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5688031601997948516525577 4266023701498461387394183)
        ·
          refine ⟨6399035552247692081091275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4266023701498461387394183 6399035552247692081091275)
          ·
            refine ⟨9598553328371538121636913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6399035552247692081091275 9598553328371538121636913)
            ·
              refine ⟨7198914996278653591227685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9598553328371538121636913 7198914996278653591227685)
              ·
                refine ⟨1349796561802247548355191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7198914996278653591227685 1349796561802247548355191)
                ·
                  refine ⟨2024694842703371322532787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1349796561802247548355191 2024694842703371322532787)
                  ·
                    refine ⟨3037042264055056983799181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2024694842703371322532787 3037042264055056983799181)
                    ·
                      refine ⟨1138890849020646368924693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3037042264055056983799181 1138890849020646368924693)
                      ·
                        rfl

theorem cell23_2217982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 2, 4, 1, 1, 3].length) (baseStart_2217982 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2217982 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2217982 prefixEnd_2217982 := by exact prefixLift 2217982
  have htrace : WordTrace (prefixWord ++ tailWord_2217982) baseStart_2217982 baseEnd_2217982 := by
    simpa [prefixWord, tailWord_2217982, baseEnd_2217982] using wordTrace_append hprefix tailTrace_2217982
  have hstable : (prefixWord ++ tailWord_2217982).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2217982).length < 2 ^ (prefixWord ++ tailWord_2217982).sum := by decide
  have hdescent : baseEnd_2217982 < baseStart_2217982 := by decide
  rcases family_descends (prefixWord ++ tailWord_2217982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2217991 : List Nat := [1, 1, 4, 3, 1, 3, 1, 2, 1, 1, 5]
def baseStart_2217991 : Nat := 118140960795 + 2217991 * 2 ^ 59
def prefixEnd_2217991 : Nat := 4983230072969 + 3 ^ 40 * 2217991 * 2
def baseEnd_2217991 : Nat := 1138895470346536833712151

theorem tailTrace_2217991 : CollatzResearch.WordTrace tailWord_2217991 prefixEnd_2217991 1138895470346536833712151 := by
  unfold tailWord_2217991
  simp only [CollatzResearch.WordTrace]
  refine ⟨80896777707604884549885827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53931185138403256366590551 80896777707604884549885827)
  ·
    refine ⟨121345166561407326824828741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80896777707604884549885827 121345166561407326824828741)
    ·
      refine ⟨22752218730263873779655389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 121345166561407326824828741 22752218730263873779655389)
      ·
        refine ⟨8532082023848952667370771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22752218730263873779655389 8532082023848952667370771)
        ·
          refine ⟨12798123035773429001056157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8532082023848952667370771 12798123035773429001056157)
          ·
            refine ⟨4799296138415035875396059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12798123035773429001056157 4799296138415035875396059)
            ·
              refine ⟨7198944207622553813094089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4799296138415035875396059 7198944207622553813094089)
              ·
                refine ⟨5399208155716915359820567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7198944207622553813094089 5399208155716915359820567)
                ·
                  refine ⟨8098812233575373039730851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5399208155716915359820567 8098812233575373039730851)
                  ·
                    refine ⟨12148218350363059559596277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8098812233575373039730851 12148218350363059559596277)
                    ·
                      refine ⟨1138895470346536833712151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12148218350363059559596277 1138895470346536833712151)
                      ·
                        rfl

theorem cell23_2217991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 1, 2, 1, 1, 5].length) (baseStart_2217991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2217991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2217991 prefixEnd_2217991 := by exact prefixLift 2217991
  have htrace : WordTrace (prefixWord ++ tailWord_2217991) baseStart_2217991 baseEnd_2217991 := by
    simpa [prefixWord, tailWord_2217991, baseEnd_2217991] using wordTrace_append hprefix tailTrace_2217991
  have hstable : (prefixWord ++ tailWord_2217991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2217991).length < 2 ^ (prefixWord ++ tailWord_2217991).sum := by decide
  have hdescent : baseEnd_2217991 < baseStart_2217991 := by decide
  rcases family_descends (prefixWord ++ tailWord_2217991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2218008 : List Nat := [2, 1, 2, 3, 2, 1, 4, 2, 1, 2, 3]
def baseStart_2218008 : Nat := 118140960795 + 2218008 * 2 ^ 59
def prefixEnd_2218008 : Nat := 4983230072969 + 3 ^ 40 * 2218008 * 2
def baseEnd_2218008 : Nat := 1138904199517663267199573

theorem tailTrace_2218008 : CollatzResearch.WordTrace tailWord_2218008 prefixEnd_2218008 1138904199517663267199573 := by
  unfold tailWord_2218008
  simp only [CollatzResearch.WordTrace]
  refine ⟨40448698874271648226627339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53931598499028864302169785 40448698874271648226627339)
  ·
    refine ⟨60673048311407472339941009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40448698874271648226627339 60673048311407472339941009)
    ·
      refine ⟨45504786233555604254955757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60673048311407472339941009 45504786233555604254955757)
      ·
        refine ⟨17064294837583351595608409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45504786233555604254955757 17064294837583351595608409)
        ·
          refine ⟨12798221128187513696706307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17064294837583351595608409 12798221128187513696706307)
          ·
            refine ⟨19197331692281270545059461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12798221128187513696706307 19197331692281270545059461)
            ·
              refine ⟨3599499692302738227198649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19197331692281270545059461 3599499692302738227198649)
              ·
                refine ⟨2699624769227053670398987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3599499692302738227198649 2699624769227053670398987)
                ·
                  refine ⟨4049437153840580505598481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2699624769227053670398987 4049437153840580505598481)
                  ·
                    refine ⟨3037077865380435379198861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4049437153840580505598481 3037077865380435379198861)
                    ·
                      refine ⟨1138904199517663267199573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3037077865380435379198861 1138904199517663267199573)
                      ·
                        rfl

theorem cell23_2218008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 4, 2, 1, 2, 3].length) (baseStart_2218008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2218008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2218008 prefixEnd_2218008 := by exact prefixLift 2218008
  have htrace : WordTrace (prefixWord ++ tailWord_2218008) baseStart_2218008 baseEnd_2218008 := by
    simpa [prefixWord, tailWord_2218008, baseEnd_2218008] using wordTrace_append hprefix tailTrace_2218008
  have hstable : (prefixWord ++ tailWord_2218008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2218008).length < 2 ^ (prefixWord ++ tailWord_2218008).sum := by decide
  have hdescent : baseEnd_2218008 < baseStart_2218008 := by decide
  rcases family_descends (prefixWord ++ tailWord_2218008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2218095 : List Nat := [1, 1, 2, 1, 3, 4, 1, 4, 2, 2, 2]
def baseStart_2218095 : Nat := 118140960795 + 2218095 * 2 ^ 59
def prefixEnd_2218095 : Nat := 4983230072969 + 3 ^ 40 * 2218095 * 2
def baseEnd_2218095 : Nat := 1138948872334604426811673

theorem tailTrace_2218095 : CollatzResearch.WordTrace tailWord_2218095 prefixEnd_2218095 1138948872334604426811673 := by
  unfold tailWord_2218095
  simp only [CollatzResearch.WordTrace]
  refine ⟨80900570899228110311671739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53933713932818740207781159 80900570899228110311671739)
  ·
    refine ⟨121350856348842165467507609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80900570899228110311671739 121350856348842165467507609)
    ·
      refine ⟨91013142261631624100630707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 121350856348842165467507609 91013142261631624100630707)
      ·
        refine ⟨136519713392447436150946061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91013142261631624100630707 136519713392447436150946061)
        ·
          refine ⟨51194892522167788556604773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 136519713392447436150946061 51194892522167788556604773)
          ·
            refine ⟨9599042347906460354363395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 51194892522167788556604773 9599042347906460354363395)
            ·
              refine ⟨14398563521859690531545093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9599042347906460354363395 14398563521859690531545093)
              ·
                refine ⟨2699730660348691974664705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14398563521859690531545093 2699730660348691974664705)
                ·
                  refine ⟨2024797995261518980998529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2699730660348691974664705 2024797995261518980998529)
                  ·
                    refine ⟨1518598496446139235748897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2024797995261518980998529 1518598496446139235748897)
                    ·
                      refine ⟨1138948872334604426811673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1518598496446139235748897 1138948872334604426811673)
                      ·
                        rfl

theorem cell23_2218095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 1, 4, 2, 2, 2].length) (baseStart_2218095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2218095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2218095 prefixEnd_2218095 := by exact prefixLift 2218095
  have htrace : WordTrace (prefixWord ++ tailWord_2218095) baseStart_2218095 baseEnd_2218095 := by
    simpa [prefixWord, tailWord_2218095, baseEnd_2218095] using wordTrace_append hprefix tailTrace_2218095
  have hstable : (prefixWord ++ tailWord_2218095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2218095).length < 2 ^ (prefixWord ++ tailWord_2218095).sum := by decide
  have hdescent : baseEnd_2218095 < baseStart_2218095 := by decide
  rcases family_descends (prefixWord ++ tailWord_2218095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2218104 : List Nat := [2, 1, 2, 1, 1, 1, 3, 1, 2, 1, 8]
def baseStart_2218104 : Nat := 118140960795 + 2218104 * 2 ^ 59
def prefixEnd_2218104 : Nat := 4983230072969 + 3 ^ 40 * 2218104 * 2
def baseEnd_2218104 : Nat := 1138953493660494891599131

theorem tailTrace_2218104 : CollatzResearch.WordTrace tailWord_2218104 prefixEnd_2218104 1138953493660494891599131 := by
  unfold tailWord_2218104
  simp only [CollatzResearch.WordTrace]
  refine ⟨40450449578097752424374683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53933932770797003232499577 40450449578097752424374683)
  ·
    refine ⟨60675674367146628636562025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40450449578097752424374683 60675674367146628636562025)
    ·
      refine ⟨45506755775359971477421519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60675674367146628636562025 45506755775359971477421519)
      ·
        refine ⟨68260133663039957216132279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45506755775359971477421519 68260133663039957216132279)
        ·
          refine ⟨102390200494559935824198419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68260133663039957216132279 102390200494559935824198419)
          ·
            refine ⟨153585300741839903736297629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 102390200494559935824198419 153585300741839903736297629)
            ·
              refine ⟨57594487778189963901111611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 153585300741839903736297629 57594487778189963901111611)
              ·
                refine ⟨86391731667284945851667417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 57594487778189963901111611 86391731667284945851667417)
                ·
                  refine ⟨64793798750463709388750563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 86391731667284945851667417 64793798750463709388750563)
                  ·
                    refine ⟨97190698125695564083125845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 64793798750463709388750563 97190698125695564083125845)
                    ·
                      refine ⟨1138953493660494891599131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 97190698125695564083125845 1138953493660494891599131)
                      ·
                        rfl

theorem cell23_2218104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 1, 2, 1, 8].length) (baseStart_2218104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2218104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2218104 prefixEnd_2218104 := by exact prefixLift 2218104
  have htrace : WordTrace (prefixWord ++ tailWord_2218104) baseStart_2218104 baseEnd_2218104 := by
    simpa [prefixWord, tailWord_2218104, baseEnd_2218104] using wordTrace_append hprefix tailTrace_2218104
  have hstable : (prefixWord ++ tailWord_2218104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2218104).length < 2 ^ (prefixWord ++ tailWord_2218104).sum := by decide
  have hdescent : baseEnd_2218104 < baseStart_2218104 := by decide
  rcases family_descends (prefixWord ++ tailWord_2218104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2218135 : List Nat := [1, 1, 3, 3, 4, 1, 2, 3, 5]
def baseStart_2218135 : Nat := 118140960795 + 2218135 * 2 ^ 59
def prefixEnd_2218135 : Nat := 4983230072969 + 3 ^ 40 * 2218135 * 2
def baseEnd_2218135 : Nat := 126552156840087141145721

theorem tailTrace_2218135 : CollatzResearch.WordTrace tailWord_2218135 prefixEnd_2218135 126552156840087141145721 := by
  unfold tailWord_2218135
  simp only [CollatzResearch.WordTrace]
  refine ⟨80902029819083197143127859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53934686546055464762085239 80902029819083197143127859)
  ·
    refine ⟨121353044728624795714691789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80902029819083197143127859 121353044728624795714691789)
    ·
      refine ⟨45507391773234298393009421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 121353044728624795714691789 45507391773234298393009421)
      ·
        refine ⟨17065271914962861897378533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45507391773234298393009421 17065271914962861897378533)
        ·
          refine ⟨3199738484055536605758475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17065271914962861897378533 3199738484055536605758475)
          ·
            refine ⟨4799607726083304908637713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3199738484055536605758475 4799607726083304908637713)
            ·
              refine ⟨3599705794562478681478285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4799607726083304908637713 3599705794562478681478285)
              ·
                refine ⟨1349889672960929505554357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3599705794562478681478285 1349889672960929505554357)
                ·
                  refine ⟨126552156840087141145721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1349889672960929505554357 126552156840087141145721)
                  ·
                    rfl

theorem cell23_2218135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 2, 3, 5].length) (baseStart_2218135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2218135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2218135 prefixEnd_2218135 := by exact prefixLift 2218135
  have htrace : WordTrace (prefixWord ++ tailWord_2218135) baseStart_2218135 baseEnd_2218135 := by
    simpa [prefixWord, tailWord_2218135, baseEnd_2218135] using wordTrace_append hprefix tailTrace_2218135
  have hstable : (prefixWord ++ tailWord_2218135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2218135).length < 2 ^ (prefixWord ++ tailWord_2218135).sum := by decide
  have hdescent : baseEnd_2218135 < baseStart_2218135 := by decide
  rcases family_descends (prefixWord ++ tailWord_2218135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2218168 : List Nat := [2, 1, 2, 1, 2, 1, 3, 3, 2, 4, 2]
def baseStart_2218168 : Nat := 118140960795 + 2218168 * 2 ^ 59
def prefixEnd_2218168 : Nat := 4983230072969 + 3 ^ 40 * 2218168 * 2
def baseEnd_2218168 : Nat := 1138986356422382641198837

theorem tailTrace_2218168 : CollatzResearch.WordTrace tailWord_2218168 prefixEnd_2218168 1138986356422382641198837 := by
  unfold tailWord_2218168
  simp only [CollatzResearch.WordTrace]
  refine ⟨40451616713981821889539579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53935488951975762519386105 40451616713981821889539579)
  ·
    refine ⟨60677425070972732834309369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40451616713981821889539579 60677425070972732834309369)
    ·
      refine ⟨45508068803229549625732027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60677425070972732834309369 45508068803229549625732027)
      ·
        refine ⟨68262103204844324438598041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45508068803229549625732027 68262103204844324438598041)
        ·
          refine ⟨51196577403633243328948531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 68262103204844324438598041 51196577403633243328948531)
          ·
            refine ⟨76794866105449864993422797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51196577403633243328948531 76794866105449864993422797)
            ·
              refine ⟨28798074789543699372533549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 76794866105449864993422797 28798074789543699372533549)
              ·
                refine ⟨10799278046078887264700081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28798074789543699372533549 10799278046078887264700081)
                ·
                  refine ⟨8099458534559165448525061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10799278046078887264700081 8099458534559165448525061)
                  ·
                    refine ⟨1518648475229843521598449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8099458534559165448525061 1518648475229843521598449)
                    ·
                      refine ⟨1138986356422382641198837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1518648475229843521598449 1138986356422382641198837)
                      ·
                        rfl

theorem cell23_2218168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 3, 2, 4, 2].length) (baseStart_2218168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2218168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2218168 prefixEnd_2218168 := by exact prefixLift 2218168
  have htrace : WordTrace (prefixWord ++ tailWord_2218168) baseStart_2218168 baseEnd_2218168 := by
    simpa [prefixWord, tailWord_2218168, baseEnd_2218168] using wordTrace_append hprefix tailTrace_2218168
  have hstable : (prefixWord ++ tailWord_2218168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2218168).length < 2 ^ (prefixWord ++ tailWord_2218168).sum := by decide
  have hdescent : baseEnd_2218168 < baseStart_2218168 := by decide
  rcases family_descends (prefixWord ++ tailWord_2218168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2218171 : List Nat := [1, 1, 1, 1, 1, 2, 5, 1, 3, 4, 3]
def baseStart_2218171 : Nat := 118140960795 + 2218171 * 2 ^ 59
def prefixEnd_2218171 : Nat := 4983230072969 + 3 ^ 40 * 2218171 * 2
def baseEnd_2218171 : Nat := 1138987896864346129461323

theorem tailTrace_2218171 : CollatzResearch.WordTrace tailWord_2218171 prefixEnd_2218171 1138987896864346129461323 := by
  unfold tailWord_2218171
  simp only [CollatzResearch.WordTrace]
  refine ⟨80903342846952775291438367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53935561897968516860958911 80903342846952775291438367)
  ·
    refine ⟨121355014270429162937157551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80903342846952775291438367 121355014270429162937157551)
    ·
      refine ⟨182032521405643744405736327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121355014270429162937157551 182032521405643744405736327)
      ·
        refine ⟨273048782108465616608604491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 182032521405643744405736327 273048782108465616608604491)
        ·
          refine ⟨409573173162698424912906737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 273048782108465616608604491 409573173162698424912906737)
          ·
            refine ⟨307179879872023818684680053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 409573173162698424912906737 307179879872023818684680053)
            ·
              refine ⟨28798113738002233001688755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 307179879872023818684680053 28798113738002233001688755)
              ·
                refine ⟨43197170607003349502533133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28798113738002233001688755 43197170607003349502533133)
                ·
                  refine ⟨16198938977626256063449925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 43197170607003349502533133 16198938977626256063449925)
                  ·
                    refine ⟨3037301058304923011896861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16198938977626256063449925 3037301058304923011896861)
                    ·
                      refine ⟨1138987896864346129461323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3037301058304923011896861 1138987896864346129461323)
                      ·
                        rfl

theorem cell23_2218171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 1, 3, 4, 3].length) (baseStart_2218171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2218171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2218171 prefixEnd_2218171 := by exact prefixLift 2218171
  have htrace : WordTrace (prefixWord ++ tailWord_2218171) baseStart_2218171 baseEnd_2218171 := by
    simpa [prefixWord, tailWord_2218171, baseEnd_2218171] using wordTrace_append hprefix tailTrace_2218171
  have hstable : (prefixWord ++ tailWord_2218171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2218171).length < 2 ^ (prefixWord ++ tailWord_2218171).sum := by decide
  have hdescent : baseEnd_2218171 < baseStart_2218171 := by decide
  rcases family_descends (prefixWord ++ tailWord_2218171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2218205 : List Nat := [1, 4, 3, 2, 1, 1, 1, 1, 4, 2, 3]
def baseStart_2218205 : Nat := 118140960795 + 2218205 * 2 ^ 59
def prefixEnd_2218205 : Nat := 4983230072969 + 3 ^ 40 * 2218205 * 2
def baseEnd_2218205 : Nat := 1139005355206598996436167

theorem tailTrace_2218205 : CollatzResearch.WordTrace tailWord_2218205 prefixEnd_2218205 1139005355206598996436167 := by
  unfold tailWord_2218205
  simp only [CollatzResearch.WordTrace]
  refine ⟨80904582928829599098176069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53936388619219732732117379 80904582928829599098176069)
  ·
    refine ⟨15169609299155549830908013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 80904582928829599098176069 15169609299155549830908013)
    ·
      refine ⟨5688603487183331186590505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15169609299155549830908013 5688603487183331186590505)
      ·
        refine ⟨4266452615387498389942879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5688603487183331186590505 4266452615387498389942879)
        ·
          refine ⟨6399678923081247584914319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4266452615387498389942879 6399678923081247584914319)
          ·
            refine ⟨9599518384621871377371479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6399678923081247584914319 9599518384621871377371479)
            ·
              refine ⟨14399277576932807066057219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9599518384621871377371479 14399277576932807066057219)
              ·
                refine ⟨21598916365399210599085829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14399277576932807066057219 21598916365399210599085829)
                ·
                  refine ⟨4049796818512351987328593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21598916365399210599085829 4049796818512351987328593)
                  ·
                    refine ⟨3037347613884263990496445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4049796818512351987328593 3037347613884263990496445)
                    ·
                      refine ⟨1139005355206598996436167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3037347613884263990496445 1139005355206598996436167)
                      ·
                        rfl

theorem cell23_2218205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 1, 1, 4, 2, 3].length) (baseStart_2218205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2218205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2218205 prefixEnd_2218205 := by exact prefixLift 2218205
  have htrace : WordTrace (prefixWord ++ tailWord_2218205) baseStart_2218205 baseEnd_2218205 := by
    simpa [prefixWord, tailWord_2218205, baseEnd_2218205] using wordTrace_append hprefix tailTrace_2218205
  have hstable : (prefixWord ++ tailWord_2218205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2218205).length < 2 ^ (prefixWord ++ tailWord_2218205).sum := by decide
  have hdescent : baseEnd_2218205 < baseStart_2218205 := by decide
  rcases family_descends (prefixWord ++ tailWord_2218205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2218252 : List Nat := [2, 2, 1, 2, 2, 2, 2, 5, 1, 1, 3]
def baseStart_2218252 : Nat := 118140960795 + 2218252 * 2 ^ 59
def prefixEnd_2218252 : Nat := 4983230072969 + 3 ^ 40 * 2218252 * 2
def baseEnd_2218252 : Nat := 1139029488797360312548451

theorem tailTrace_2218252 : CollatzResearch.WordTrace tailWord_2218252 prefixEnd_2218252 1139029488797360312548451 := by
  unfold tailWord_2218252
  simp only [CollatzResearch.WordTrace]
  refine ⟨40453148579829663062568505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53937531439772884083424673 40453148579829663062568505)
  ·
    refine ⟨30339861434872247296926379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40453148579829663062568505 30339861434872247296926379)
    ·
      refine ⟨45509792152308370945389569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30339861434872247296926379 45509792152308370945389569)
      ·
        refine ⟨34132344114231278209042177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45509792152308370945389569 34132344114231278209042177)
        ·
          refine ⟨25599258085673458656781633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34132344114231278209042177 25599258085673458656781633)
          ·
            refine ⟨19199443564255093992586225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25599258085673458656781633 19199443564255093992586225)
            ·
              refine ⟨14399582673191320494439669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19199443564255093992586225 14399582673191320494439669)
              ·
                refine ⟨1349960875611686296353719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 14399582673191320494439669 1349960875611686296353719)
                ·
                  refine ⟨2024941313417529444530579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1349960875611686296353719 2024941313417529444530579)
                  ·
                    refine ⟨3037411970126294166795869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2024941313417529444530579 3037411970126294166795869)
                    ·
                      refine ⟨1139029488797360312548451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3037411970126294166795869 1139029488797360312548451)
                      ·
                        rfl

theorem cell23_2218252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 2, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 2, 5, 1, 1, 3].length) (baseStart_2218252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2218252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2218252 prefixEnd_2218252 := by exact prefixLift 2218252
  have htrace : WordTrace (prefixWord ++ tailWord_2218252) baseStart_2218252 baseEnd_2218252 := by
    simpa [prefixWord, tailWord_2218252, baseEnd_2218252] using wordTrace_append hprefix tailTrace_2218252
  have hstable : (prefixWord ++ tailWord_2218252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2218252).length < 2 ^ (prefixWord ++ tailWord_2218252).sum := by decide
  have hdescent : baseEnd_2218252 < baseStart_2218252 := by decide
  rcases family_descends (prefixWord ++ tailWord_2218252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2218312 : List Nat := [2, 1, 3, 1, 1, 2, 6, 1, 1, 2, 3]
def baseStart_2218312 : Nat := 118140960795 + 2218312 * 2 ^ 59
def prefixEnd_2218312 : Nat := 4983230072969 + 3 ^ 40 * 2218312 * 2
def baseEnd_2218312 : Nat := 1139060297636630077798175

theorem tailTrace_2218312 : CollatzResearch.WordTrace tailWord_2218312 prefixEnd_2218312 1139060297636630077798175 := by
  unfold tailWord_2218312
  simp only [CollatzResearch.WordTrace]
  refine ⟨40454242769720978186160595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53938990359627970914880793 40454242769720978186160595)
  ·
    refine ⟨60681364154581467279240893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40454242769720978186160595 60681364154581467279240893)
    ·
      refine ⟨22755511557968050229715335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 60681364154581467279240893 22755511557968050229715335)
      ·
        refine ⟨34133267336952075344573003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22755511557968050229715335 34133267336952075344573003)
        ·
          refine ⟨51199901005428113016859505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34133267336952075344573003 51199901005428113016859505)
          ·
            refine ⟨38399925754071084762644629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51199901005428113016859505 38399925754071084762644629)
            ·
              refine ⟨1799996519722082098248967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 38399925754071084762644629 1799996519722082098248967)
              ·
                refine ⟨2699994779583123147373451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1799996519722082098248967 2699994779583123147373451)
                ·
                  refine ⟨4049992169374684721060177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2699994779583123147373451 4049992169374684721060177)
                  ·
                    refine ⟨3037494127031013540795133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4049992169374684721060177 3037494127031013540795133)
                    ·
                      refine ⟨1139060297636630077798175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3037494127031013540795133 1139060297636630077798175)
                      ·
                        rfl

theorem cell23_2218312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 6, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 6, 1, 1, 2, 3].length) (baseStart_2218312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2218312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2218312 prefixEnd_2218312 := by exact prefixLift 2218312
  have htrace : WordTrace (prefixWord ++ tailWord_2218312) baseStart_2218312 baseEnd_2218312 := by
    simpa [prefixWord, tailWord_2218312, baseEnd_2218312] using wordTrace_append hprefix tailTrace_2218312
  have hstable : (prefixWord ++ tailWord_2218312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2218312).length < 2 ^ (prefixWord ++ tailWord_2218312).sum := by decide
  have hdescent : baseEnd_2218312 < baseStart_2218312 := by decide
  rcases family_descends (prefixWord ++ tailWord_2218312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2218335 : List Nat := [1, 1, 2, 3, 1, 2, 2, 1, 5, 3, 2]
def baseStart_2218335 : Nat := 118140960795 + 2218335 * 2 ^ 59
def prefixEnd_2218335 : Nat := 4983230072969 + 3 ^ 40 * 2218335 * 2
def baseEnd_2218335 : Nat := 1139072107691683487810569

theorem tailTrace_2218335 : CollatzResearch.WordTrace tailWord_2218335 prefixEnd_2218335 1139072107691683487810569 := by
  unfold tailWord_2218335
  simp only [CollatzResearch.WordTrace]
  refine ⟨80909324418358631300408459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53939549612239087533605639 80909324418358631300408459)
  ·
    refine ⟨121363986627537946950612689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80909324418358631300408459 121363986627537946950612689)
    ·
      refine ⟨91022989970653460212959517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 121363986627537946950612689 91022989970653460212959517)
      ·
        refine ⟨34133621238995047579859819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 91022989970653460212959517 34133621238995047579859819)
        ·
          refine ⟨51200431858492571369789729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34133621238995047579859819 51200431858492571369789729)
          ·
            refine ⟨38400323893869428527342297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51200431858492571369789729 38400323893869428527342297)
            ·
              refine ⟨28800242920402071395506723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38400323893869428527342297 28800242920402071395506723)
              ·
                refine ⟨43200364380603107093260085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28800242920402071395506723 43200364380603107093260085)
                ·
                  refine ⟨4050034160681541289993133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 43200364380603107093260085 4050034160681541289993133)
                  ·
                    refine ⟨1518762810255577983747425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4050034160681541289993133 1518762810255577983747425)
                    ·
                      refine ⟨1139072107691683487810569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1518762810255577983747425 1139072107691683487810569)
                      ·
                        rfl

theorem cell23_2218335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 1, 5, 3, 2].length) (baseStart_2218335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2218335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2218335 prefixEnd_2218335 := by exact prefixLift 2218335
  have htrace : WordTrace (prefixWord ++ tailWord_2218335) baseStart_2218335 baseEnd_2218335 := by
    simpa [prefixWord, tailWord_2218335, baseEnd_2218335] using wordTrace_append hprefix tailTrace_2218335
  have hstable : (prefixWord ++ tailWord_2218335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2218335).length < 2 ^ (prefixWord ++ tailWord_2218335).sum := by decide
  have hdescent : baseEnd_2218335 < baseStart_2218335 := by decide
  rcases family_descends (prefixWord ++ tailWord_2218335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2218352 : List Nat := [2, 1, 1, 1, 4, 3, 1, 4, 1, 3, 2]
def baseStart_2218352 : Nat := 118140960795 + 2218352 * 2 ^ 59
def prefixEnd_2218352 : Nat := 4983230072969 + 3 ^ 40 * 2218352 * 2
def baseEnd_2218352 : Nat := 1139080836862809921297991

theorem tailTrace_2218352 : CollatzResearch.WordTrace tailWord_2218352 prefixEnd_2218352 1139080836862809921297991 := by
  unfold tailWord_2218352
  simp only [CollatzResearch.WordTrace]
  refine ⟨40454972229648521601888655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53939962972864695469184873 40454972229648521601888655)
  ·
    refine ⟨60682458344472782402832983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40454972229648521601888655 60682458344472782402832983)
    ·
      refine ⟨91023687516709173604249475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60682458344472782402832983 91023687516709173604249475)
      ·
        refine ⟨136535531275063760406374213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91023687516709173604249475 136535531275063760406374213)
        ·
          refine ⟨25600412114074455076195165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 136535531275063760406374213 25600412114074455076195165)
          ·
            refine ⟨9600154542777920653573187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25600412114074455076195165 9600154542777920653573187)
            ·
              refine ⟨14400231814166880980359781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9600154542777920653573187 14400231814166880980359781)
              ·
                refine ⟨2700043465156290183817459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14400231814166880980359781 2700043465156290183817459)
                ·
                  refine ⟨4050065197734435275726189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2700043465156290183817459 4050065197734435275726189)
                  ·
                    refine ⟨1518774449150413228397321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4050065197734435275726189 1518774449150413228397321)
                    ·
                      refine ⟨1139080836862809921297991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1518774449150413228397321 1139080836862809921297991)
                      ·
                        rfl

theorem cell23_2218352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 1, 4, 1, 3, 2].length) (baseStart_2218352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2218352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2218352 prefixEnd_2218352 := by exact prefixLift 2218352
  have htrace : WordTrace (prefixWord ++ tailWord_2218352) baseStart_2218352 baseEnd_2218352 := by
    simpa [prefixWord, tailWord_2218352, baseEnd_2218352] using wordTrace_append hprefix tailTrace_2218352
  have hstable : (prefixWord ++ tailWord_2218352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2218352).length < 2 ^ (prefixWord ++ tailWord_2218352).sum := by decide
  have hdescent : baseEnd_2218352 < baseStart_2218352 := by decide
  rcases family_descends (prefixWord ++ tailWord_2218352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2218368 : List Nat := [2, 1, 1, 2, 1, 2, 1, 1, 3, 6, 3]
def baseStart_2218368 : Nat := 118140960795 + 2218368 * 2 ^ 59
def prefixEnd_2218368 : Nat := 4983230072969 + 3 ^ 40 * 2218368 * 2
def baseEnd_2218368 : Nat := 1139089052553281858697917

theorem tailTrace_2218368 : CollatzResearch.WordTrace tailWord_2218368 prefixEnd_2218368 1139089052553281858697917 := by
  unfold tailWord_2218368
  simp only [CollatzResearch.WordTrace]
  refine ⟨40455264013619538968179879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53940352018159385290906505 40455264013619538968179879)
  ·
    refine ⟨60682896020429308452269819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40455264013619538968179879 60682896020429308452269819)
    ·
      refine ⟨91024344030643962678404729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60682896020429308452269819 91024344030643962678404729)
      ·
        refine ⟨68268258022982972008803547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 91024344030643962678404729 68268258022982972008803547)
        ·
          refine ⟨102402387034474458013205321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68268258022982972008803547 102402387034474458013205321)
          ·
            refine ⟨76801790275855843509903991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 102402387034474458013205321 76801790275855843509903991)
            ·
              refine ⟨115202685413783765264855987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 76801790275855843509903991 115202685413783765264855987)
              ·
                refine ⟨172804028120675647897283981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 115202685413783765264855987 172804028120675647897283981)
                ·
                  refine ⟨64801510545253367961481493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 172804028120675647897283981 64801510545253367961481493)
                  ·
                    refine ⟨3037570806808751623194445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 64801510545253367961481493 3037570806808751623194445)
                    ·
                      refine ⟨1139089052553281858697917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3037570806808751623194445 1139089052553281858697917)
                      ·
                        rfl

theorem cell23_2218368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 1, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 1, 3, 6, 3].length) (baseStart_2218368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2218368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2218368 prefixEnd_2218368 := by exact prefixLift 2218368
  have htrace : WordTrace (prefixWord ++ tailWord_2218368) baseStart_2218368 baseEnd_2218368 := by
    simpa [prefixWord, tailWord_2218368, baseEnd_2218368] using wordTrace_append hprefix tailTrace_2218368
  have hstable : (prefixWord ++ tailWord_2218368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2218368).length < 2 ^ (prefixWord ++ tailWord_2218368).sum := by decide
  have hdescent : baseEnd_2218368 < baseStart_2218368 := by decide
  rcases family_descends (prefixWord ++ tailWord_2218368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2218369 : List Nat := [1, 2, 4, 3, 1, 1, 2, 3, 1, 3, 2]
def baseStart_2218369 : Nat := 118140960795 + 2218369 * 2 ^ 59
def prefixEnd_2218369 : Nat := 4983230072969 + 3 ^ 40 * 2218369 * 2
def baseEnd_2218369 : Nat := 1139089566033936354785413

theorem tailTrace_2218369 : CollatzResearch.WordTrace tailWord_2218369 prefixEnd_2218369 1139089566033936354785413 := by
  unfold tailWord_2218369
  simp only [CollatzResearch.WordTrace]
  refine ⟨80910564500235455107146161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53940376333490303404764107 80910564500235455107146161)
  ·
    refine ⟨60682923375176591330359621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80910564500235455107146161 60682923375176591330359621)
    ·
      refine ⟨11378048132845610874442429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 60682923375176591330359621 11378048132845610874442429)
      ·
        refine ⟨4266768049817104077915911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11378048132845610874442429 4266768049817104077915911)
        ·
          refine ⟨6400152074725656116873867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4266768049817104077915911 6400152074725656116873867)
          ·
            refine ⟨9600228112088484175310801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6400152074725656116873867 9600228112088484175310801)
            ·
              refine ⟨7200171084066363131483101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9600228112088484175310801 7200171084066363131483101)
              ·
                refine ⟨2700064156524886174306163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7200171084066363131483101 2700064156524886174306163)
                ·
                  refine ⟨4050096234787329261459245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2700064156524886174306163 4050096234787329261459245)
                  ·
                    refine ⟨1518786088045248473047217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4050096234787329261459245 1518786088045248473047217)
                    ·
                      refine ⟨1139089566033936354785413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1518786088045248473047217 1139089566033936354785413)
                      ·
                        rfl

theorem cell23_2218369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 2, 3, 1, 3, 2].length) (baseStart_2218369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2218369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2218369 prefixEnd_2218369 := by exact prefixLift 2218369
  have htrace : WordTrace (prefixWord ++ tailWord_2218369) baseStart_2218369 baseEnd_2218369 := by
    simpa [prefixWord, tailWord_2218369, baseEnd_2218369] using wordTrace_append hprefix tailTrace_2218369
  have hstable : (prefixWord ++ tailWord_2218369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2218369).length < 2 ^ (prefixWord ++ tailWord_2218369).sum := by decide
  have hdescent : baseEnd_2218369 < baseStart_2218369 := by decide
  rcases family_descends (prefixWord ++ tailWord_2218369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2218399 : List Nat := [1, 1, 2, 5, 1, 1, 3, 3, 2, 2, 2]
def baseStart_2218399 : Nat := 118140960795 + 2218399 * 2 ^ 59
def prefixEnd_2218399 : Nat := 4983230072969 + 3 ^ 40 * 2218399 * 2
def baseEnd_2218399 : Nat := 1139104970453571237410275

theorem tailTrace_2218399 : CollatzResearch.WordTrace tailWord_2218399 prefixEnd_2218399 1139104970453571237410275 := by
  unfold tailWord_2218399
  simp only [CollatzResearch.WordTrace]
  refine ⟨80911658690126770230738251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53941105793417846820492167 80911658690126770230738251)
  ·
    refine ⟨121367488035190155346107377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80911658690126770230738251 121367488035190155346107377)
    ·
      refine ⟨91025616026392616509580533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 121367488035190155346107377 91025616026392616509580533)
      ·
        refine ⟨8533651502474307797773175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 91025616026392616509580533 8533651502474307797773175)
        ·
          refine ⟨12800477253711461696659763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8533651502474307797773175 12800477253711461696659763)
          ·
            refine ⟨19200715880567192544989645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12800477253711461696659763 19200715880567192544989645)
            ·
              refine ⟨7200268455212697204371117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19200715880567192544989645 7200268455212697204371117)
              ·
                refine ⟨2700100670704761451639169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7200268455212697204371117 2700100670704761451639169)
                ·
                  refine ⟨2025075503028571088729377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2700100670704761451639169 2025075503028571088729377)
                  ·
                    refine ⟨1518806627271428316547033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2025075503028571088729377 1518806627271428316547033)
                    ·
                      refine ⟨1139104970453571237410275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1518806627271428316547033 1139104970453571237410275)
                      ·
                        rfl

theorem cell23_2218399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 3, 3, 2, 2, 2].length) (baseStart_2218399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2218399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2218399 prefixEnd_2218399 := by exact prefixLift 2218399
  have htrace : WordTrace (prefixWord ++ tailWord_2218399) baseStart_2218399 baseEnd_2218399 := by
    simpa [prefixWord, tailWord_2218399, baseEnd_2218399] using wordTrace_append hprefix tailTrace_2218399
  have hstable : (prefixWord ++ tailWord_2218399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2218399).length < 2 ^ (prefixWord ++ tailWord_2218399).sum := by decide
  have hdescent : baseEnd_2218399 < baseStart_2218399 := by decide
  rcases family_descends (prefixWord ++ tailWord_2218399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2218420 : List Nat := [2, 5, 2, 2, 1, 1, 3, 1, 1, 3, 2]
def baseStart_2218420 : Nat := 118140960795 + 2218420 * 2 ^ 59
def prefixEnd_2218420 : Nat := 4983230072969 + 3 ^ 40 * 2218420 * 2
def baseEnd_2218420 : Nat := 1139115753547315655247679

theorem tailTrace_2218420 : CollatzResearch.WordTrace tailWord_2218420 prefixEnd_2218420 1139115753547315655247679 := by
  unfold tailWord_2218420
  simp only [CollatzResearch.WordTrace]
  refine ⟨40456212311525345408626357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53941616415367127211501809 40456212311525345408626357)
  ·
    refine ⟨3792769904205501132058721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 40456212311525345408626357 3792769904205501132058721)
    ·
      refine ⟨2844577428154125849044041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3792769904205501132058721 2844577428154125849044041)
      ·
        refine ⟨2133433071115594386783031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2844577428154125849044041 2133433071115594386783031)
        ·
          refine ⟨3200149606673391580174547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2133433071115594386783031 3200149606673391580174547)
          ·
            refine ⟨4800224410010087370261821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3200149606673391580174547 4800224410010087370261821)
            ·
              refine ⟨1800084153753782763848183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4800224410010087370261821 1800084153753782763848183)
              ·
                refine ⟨2700126230630674145772275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1800084153753782763848183 2700126230630674145772275)
                ·
                  refine ⟨4050189345946011218658413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2700126230630674145772275 4050189345946011218658413)
                  ·
                    refine ⟨1518821004729754206996905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4050189345946011218658413 1518821004729754206996905)
                    ·
                      refine ⟨1139115753547315655247679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1518821004729754206996905 1139115753547315655247679)
                      ·
                        rfl

theorem cell23_2218420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 3, 1, 1, 3, 2].length) (baseStart_2218420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2218420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2218420 prefixEnd_2218420 := by exact prefixLift 2218420
  have htrace : WordTrace (prefixWord ++ tailWord_2218420) baseStart_2218420 baseEnd_2218420 := by
    simpa [prefixWord, tailWord_2218420, baseEnd_2218420] using wordTrace_append hprefix tailTrace_2218420
  have hstable : (prefixWord ++ tailWord_2218420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2218420).length < 2 ^ (prefixWord ++ tailWord_2218420).sum := by decide
  have hdescent : baseEnd_2218420 < baseStart_2218420 := by decide
  rcases family_descends (prefixWord ++ tailWord_2218420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2218439 : List Nat := [1, 1, 4, 1, 1, 6, 2, 2, 5]
def baseStart_2218439 : Nat := 118140960795 + 2218439 * 2 ^ 59
def prefixEnd_2218439 : Nat := 4983230072969 + 3 ^ 40 * 2218439 * 2
def baseEnd_2218439 : Nat := 126569501075527897878899

theorem tailTrace_2218439 : CollatzResearch.WordTrace tailWord_2218439 prefixEnd_2218439 126569501075527897878899 := by
  unfold tailWord_2218439
  simp only [CollatzResearch.WordTrace]
  refine ⟨80913117609981857062194371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53942078406654571374796247 80913117609981857062194371)
  ·
    refine ⟨121369676414972785593291557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80913117609981857062194371 121369676414972785593291557)
    ·
      refine ⟨22756814327807397298742167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 121369676414972785593291557 22756814327807397298742167)
      ·
        refine ⟨34135221491711095948113251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22756814327807397298742167 34135221491711095948113251)
        ·
          refine ⟨51202832237566643922169877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34135221491711095948113251 51202832237566643922169877)
          ·
            refine ⟨2400132761135936433851713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 51202832237566643922169877 2400132761135936433851713)
            ·
              refine ⟨1800099570851952325388785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2400132761135936433851713 1800099570851952325388785)
              ·
                refine ⟨1350074678138964244041589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1800099570851952325388785 1350074678138964244041589)
                ·
                  refine ⟨126569501075527897878899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1350074678138964244041589 126569501075527897878899)
                  ·
                    rfl

theorem cell23_2218439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 6, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 6, 2, 2, 5].length) (baseStart_2218439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2218439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2218439 prefixEnd_2218439 := by exact prefixLift 2218439
  have htrace : WordTrace (prefixWord ++ tailWord_2218439) baseStart_2218439 baseEnd_2218439 := by
    simpa [prefixWord, tailWord_2218439, baseEnd_2218439] using wordTrace_append hprefix tailTrace_2218439
  have hstable : (prefixWord ++ tailWord_2218439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2218439).length < 2 ^ (prefixWord ++ tailWord_2218439).sum := by decide
  have hdescent : baseEnd_2218439 < baseStart_2218439 := by decide
  rcases family_descends (prefixWord ++ tailWord_2218439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2218469 : List Nat := [1, 3, 1, 5, 2, 2, 1, 1, 2, 5]
def baseStart_2218469 : Nat := 118140960795 + 2218469 * 2 ^ 59
def prefixEnd_2218469 : Nat := 4983230072969 + 3 ^ 40 * 2218469 * 2
def baseEnd_2218469 : Nat := 379713638033128654511651

theorem tailTrace_2218469 : CollatzResearch.WordTrace tailWord_2218469 prefixEnd_2218469 379713638033128654511651 := by
  unfold tailWord_2218469
  simp only [CollatzResearch.WordTrace]
  refine ⟨80914211799873172185786461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53942807866582114790524307 80914211799873172185786461)
  ·
    refine ⟨30342829424952439569669923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 80914211799873172185786461 30342829424952439569669923)
    ·
      refine ⟨45514244137428659354504885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30342829424952439569669923 45514244137428659354504885)
      ·
        refine ⟨4266960387883936814484833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 45514244137428659354504885 4266960387883936814484833)
        ·
          refine ⟨3200220290912952610863625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4266960387883936814484833 3200220290912952610863625)
          ·
            refine ⟨2400165218184714458147719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3200220290912952610863625 2400165218184714458147719)
            ·
              refine ⟨3600247827277071687221579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2400165218184714458147719 3600247827277071687221579)
              ·
                refine ⟨5400371740915607530832369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3600247827277071687221579 5400371740915607530832369)
                ·
                  refine ⟨4050278805686705648124277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5400371740915607530832369 4050278805686705648124277)
                  ·
                    refine ⟨379713638033128654511651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4050278805686705648124277 379713638033128654511651)
                    ·
                      rfl

theorem cell23_2218469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 2, 1, 1, 2, 5].length) (baseStart_2218469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2218469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2218469 prefixEnd_2218469 := by exact prefixLift 2218469
  have htrace : WordTrace (prefixWord ++ tailWord_2218469) baseStart_2218469 baseEnd_2218469 := by
    simpa [prefixWord, tailWord_2218469, baseEnd_2218469] using wordTrace_append hprefix tailTrace_2218469
  have hstable : (prefixWord ++ tailWord_2218469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2218469).length < 2 ^ (prefixWord ++ tailWord_2218469).sum := by decide
  have hdescent : baseEnd_2218469 < baseStart_2218469 := by decide
  rcases family_descends (prefixWord ++ tailWord_2218469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2218472 : List Nat := [2, 1, 4, 1, 1, 3, 3, 1, 2, 1, 4]
def baseStart_2218472 : Nat := 118140960795 + 2218472 * 2 ^ 59
def prefixEnd_2218472 : Nat := 4983230072969 + 3 ^ 40 * 2218472 * 2
def baseEnd_2218472 : Nat := 1139142454541349451797439

theorem tailTrace_2218472 : CollatzResearch.WordTrace tailWord_2218472 prefixEnd_2218472 1139142454541349451797439 := by
  unfold tailWord_2218472
  simp only [CollatzResearch.WordTrace]
  refine ⟨40457160609431151849072835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53942880812574869132097113 40457160609431151849072835)
  ·
    refine ⟨60685740914146727773609253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40457160609431151849072835 60685740914146727773609253)
    ·
      refine ⟨11378576421402511457551735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 60685740914146727773609253 11378576421402511457551735)
      ·
        refine ⟨17067864632103767186327603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11378576421402511457551735 17067864632103767186327603)
        ·
          refine ⟨25601796948155650779491405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17067864632103767186327603 25601796948155650779491405)
          ·
            refine ⟨9600673855558369042309277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25601796948155650779491405 9600673855558369042309277)
            ·
              refine ⟨3600252695834388390865979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9600673855558369042309277 3600252695834388390865979)
              ·
                refine ⟨5400379043751582586298969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3600252695834388390865979 5400379043751582586298969)
                ·
                  refine ⟨4050284282813686939724227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5400379043751582586298969 4050284282813686939724227)
                  ·
                    refine ⟨6075426424220530409586341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4050284282813686939724227 6075426424220530409586341)
                    ·
                      refine ⟨1139142454541349451797439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6075426424220530409586341 1139142454541349451797439)
                      ·
                        rfl

theorem cell23_2218472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 3, 1, 2, 1, 4].length) (baseStart_2218472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2218472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2218472 prefixEnd_2218472 := by exact prefixLift 2218472
  have htrace : WordTrace (prefixWord ++ tailWord_2218472) baseStart_2218472 baseEnd_2218472 := by
    simpa [prefixWord, tailWord_2218472, baseEnd_2218472] using wordTrace_append hprefix tailTrace_2218472
  have hstable : (prefixWord ++ tailWord_2218472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2218472).length < 2 ^ (prefixWord ++ tailWord_2218472).sum := by decide
  have hdescent : baseEnd_2218472 < baseStart_2218472 := by decide
  rcases family_descends (prefixWord ++ tailWord_2218472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2218475 : List Nat := [1, 1, 1, 1, 2, 3, 5, 1, 1, 4, 3]
def baseStart_2218475 : Nat := 118140960795 + 2218475 * 2 ^ 59
def prefixEnd_2218475 : Nat := 4983230072969 + 3 ^ 40 * 2218475 * 2
def baseEnd_2218475 : Nat := 1139143994983312940059925

theorem tailTrace_2218475 : CollatzResearch.WordTrace tailWord_2218475 prefixEnd_2218475 1139143994983312940059925 := by
  unfold tailWord_2218475
  simp only [CollatzResearch.WordTrace]
  refine ⟨80914430637851435210504879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53942953758567623473669919 80914430637851435210504879)
  ·
    refine ⟨121371645956777152815757319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80914430637851435210504879 121371645956777152815757319)
    ·
      refine ⟨182057468935165729223635979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121371645956777152815757319 182057468935165729223635979)
      ·
        refine ⟨273086203402748593835453969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 182057468935165729223635979 273086203402748593835453969)
        ·
          refine ⟨204814652552061445376590477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 273086203402748593835453969 204814652552061445376590477)
          ·
            refine ⟨76805494707023042016221429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 204814652552061445376590477 76805494707023042016221429)
            ·
              refine ⟨7200515128783410189020759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 76805494707023042016221429 7200515128783410189020759)
              ·
                refine ⟨10800772693175115283531139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7200515128783410189020759 10800772693175115283531139)
                ·
                  refine ⟨16201159039762672925296709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10800772693175115283531139 16201159039762672925296709)
                  ·
                    refine ⟨3037717319955501173493133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16201159039762672925296709 3037717319955501173493133)
                    ·
                      refine ⟨1139143994983312940059925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3037717319955501173493133 1139143994983312940059925)
                      ·
                        rfl

theorem cell23_2218475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 5, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 5, 1, 1, 4, 3].length) (baseStart_2218475 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2218475 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2218475 prefixEnd_2218475 := by exact prefixLift 2218475
  have htrace : WordTrace (prefixWord ++ tailWord_2218475) baseStart_2218475 baseEnd_2218475 := by
    simpa [prefixWord, tailWord_2218475, baseEnd_2218475] using wordTrace_append hprefix tailTrace_2218475
  have hstable : (prefixWord ++ tailWord_2218475).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2218475).length < 2 ^ (prefixWord ++ tailWord_2218475).sum := by decide
  have hdescent : baseEnd_2218475 < baseStart_2218475 := by decide
  rcases family_descends (prefixWord ++ tailWord_2218475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2218549 : List Nat := [1, 3, 3, 1, 1, 2, 3, 2, 2, 3, 2]
def baseStart_2218549 : Nat := 118140960795 + 2218549 * 2 ^ 59
def prefixEnd_2218549 : Nat := 4983230072969 + 3 ^ 40 * 2218549 * 2
def baseEnd_2218549 : Nat := 1139181992551745650534585

theorem tailTrace_2218549 : CollatzResearch.WordTrace tailWord_2218549 prefixEnd_2218549 1139181992551745650534585 := by
  unfold tailWord_2218549
  simp only [CollatzResearch.WordTrace]
  refine ⟨80917129639583345848698701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53944753093055563899132467 80917129639583345848698701)
  ·
    refine ⟨30343923614843754693262013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 80917129639583345848698701 30343923614843754693262013)
    ·
      refine ⟨11378971355566408009973255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30343923614843754693262013 11378971355566408009973255)
      ·
        refine ⟨17068457033349612014959883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11378971355566408009973255 17068457033349612014959883)
        ·
          refine ⟨25602685550024418022439825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17068457033349612014959883 25602685550024418022439825)
          ·
            refine ⟨19202014162518313516829869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25602685550024418022439825 19202014162518313516829869)
            ·
              refine ⟨7200755310944367568811201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19202014162518313516829869 7200755310944367568811201)
              ·
                refine ⟨5400566483208275676608401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7200755310944367568811201 5400566483208275676608401)
                ·
                  refine ⟨4050424862406206757456301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5400566483208275676608401 4050424862406206757456301)
                  ·
                    refine ⟨1518909323402327534046113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4050424862406206757456301 1518909323402327534046113)
                    ·
                      refine ⟨1139181992551745650534585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1518909323402327534046113 1139181992551745650534585)
                      ·
                        rfl

theorem cell23_2218549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 3, 2, 2, 3, 2].length) (baseStart_2218549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2218549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2218549 prefixEnd_2218549 := by exact prefixLift 2218549
  have htrace : WordTrace (prefixWord ++ tailWord_2218549) baseStart_2218549 baseEnd_2218549 := by
    simpa [prefixWord, tailWord_2218549, baseEnd_2218549] using wordTrace_append hprefix tailTrace_2218549
  have hstable : (prefixWord ++ tailWord_2218549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2218549).length < 2 ^ (prefixWord ++ tailWord_2218549).sum := by decide
  have hdescent : baseEnd_2218549 < baseStart_2218549 := by decide
  rcases family_descends (prefixWord ++ tailWord_2218549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2218556 : List Nat := [2, 2, 2, 2, 3, 3, 1, 1, 3, 1, 3]
def baseStart_2218556 : Nat := 118140960795 + 2218556 * 2 ^ 59
def prefixEnd_2218556 : Nat := 4983230072969 + 3 ^ 40 * 2218556 * 2
def baseEnd_2218556 : Nat := 1139185586916327123147053

theorem tailTrace_2218556 : CollatzResearch.WordTrace tailWord_2218556 prefixEnd_2218556 1139185586916327123147053 := by
  unfold tailWord_2218556
  simp only [CollatzResearch.WordTrace]
  refine ⟨40458692475278993022101761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53944923300371990696135681 40458692475278993022101761)
  ·
    refine ⟨30344019356459244766576321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40458692475278993022101761 30344019356459244766576321)
    ·
      refine ⟨22758014517344433574932241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30344019356459244766576321 22758014517344433574932241)
      ·
        refine ⟨17068510888008325181199181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22758014517344433574932241 17068510888008325181199181)
        ·
          refine ⟨6400691583003121942949693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17068510888008325181199181 6400691583003121942949693)
          ·
            refine ⟨2400259343626170728606135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6400691583003121942949693 2400259343626170728606135)
            ·
              refine ⟨3600389015439256092909203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2400259343626170728606135 3600389015439256092909203)
              ·
                refine ⟨5400583523158884139363805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3600389015439256092909203 5400583523158884139363805)
                ·
                  refine ⟨2025218821184581552261427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5400583523158884139363805 2025218821184581552261427)
                  ·
                    refine ⟨3037828231776872328392141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2025218821184581552261427 3037828231776872328392141)
                    ·
                      refine ⟨1139185586916327123147053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3037828231776872328392141 1139185586916327123147053)
                      ·
                        rfl

theorem cell23_2218556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 3, 1, 1, 3, 1, 3].length) (baseStart_2218556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2218556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2218556 prefixEnd_2218556 := by exact prefixLift 2218556
  have htrace : WordTrace (prefixWord ++ tailWord_2218556) baseStart_2218556 baseEnd_2218556 := by
    simpa [prefixWord, tailWord_2218556, baseEnd_2218556] using wordTrace_append hprefix tailTrace_2218556
  have hstable : (prefixWord ++ tailWord_2218556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2218556).length < 2 ^ (prefixWord ++ tailWord_2218556).sum := by decide
  have hdescent : baseEnd_2218556 < baseStart_2218556 := by decide
  rcases family_descends (prefixWord ++ tailWord_2218556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2218575 : List Nat := [1, 1, 2, 1, 1, 2, 6, 1, 1, 1, 6]
def baseStart_2218575 : Nat := 118140960795 + 2218575 * 2 ^ 59
def prefixEnd_2218575 : Nat := 4983230072969 + 3 ^ 40 * 2218575 * 2
def baseEnd_2218575 : Nat := 1139195343048762548809465

theorem tailTrace_2218575 : CollatzResearch.WordTrace tailWord_2218575 prefixEnd_2218575 1139195343048762548809465 := by
  unfold tailWord_2218575
  simp only [CollatzResearch.WordTrace]
  refine ⟨80918077937489152289145179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53945385291659434859430119 80918077937489152289145179)
  ·
    refine ⟨121377116906233728433717769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80918077937489152289145179 121377116906233728433717769)
    ·
      refine ⟨91032837679675296325288327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 121377116906233728433717769 91032837679675296325288327)
      ·
        refine ⟨136549256519512944487932491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91032837679675296325288327 136549256519512944487932491)
        ·
          refine ⟨204823884779269416731898737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 136549256519512944487932491 204823884779269416731898737)
          ·
            refine ⟨153617913584452062548924053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 204823884779269416731898737 153617913584452062548924053)
            ·
              refine ⟨7200839699271190431980815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 153617913584452062548924053 7200839699271190431980815)
              ·
                refine ⟨10801259548906785647971223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7200839699271190431980815 10801259548906785647971223)
                ·
                  refine ⟨16201889323360178471956835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10801259548906785647971223 16201889323360178471956835)
                  ·
                    refine ⟨24302833985040267707935253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16201889323360178471956835 24302833985040267707935253)
                    ·
                      refine ⟨1139195343048762548809465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 24302833985040267707935253 1139195343048762548809465)
                      ·
                        rfl

theorem cell23_2218575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 6, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 6, 1, 1, 1, 6].length) (baseStart_2218575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2218575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2218575 prefixEnd_2218575 := by exact prefixLift 2218575
  have htrace : WordTrace (prefixWord ++ tailWord_2218575) baseStart_2218575 baseEnd_2218575 := by
    simpa [prefixWord, tailWord_2218575, baseEnd_2218575] using wordTrace_append hprefix tailTrace_2218575
  have hstable : (prefixWord ++ tailWord_2218575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2218575).length < 2 ^ (prefixWord ++ tailWord_2218575).sum := by decide
  have hdescent : baseEnd_2218575 < baseStart_2218575 := by decide
  rcases family_descends (prefixWord ++ tailWord_2218575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2218606 : List Nat := [4, 1, 2, 2, 2, 2, 2, 2, 2, 4]
def baseStart_2218606 : Nat := 118140960795 + 2218606 * 2 ^ 59
def prefixEnd_2218606 : Nat := 4983230072969 + 3 ^ 40 * 2218606 * 2
def baseEnd_2218606 : Nat := 379737086983017309173941

theorem tailTrace_2218606 : CollatzResearch.WordTrace tailWord_2218606 prefixEnd_2218606 379737086983017309173941 := by
  unfold tailWord_2218606
  simp only [CollatzResearch.WordTrace]
  refine ⟨10114901075047105572940459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 53946139066917896389015781 10114901075047105572940459)
  ·
    refine ⟨15172351612570658359410689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10114901075047105572940459 15172351612570658359410689)
    ·
      refine ⟨11379263709427993769558017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15172351612570658359410689 11379263709427993769558017)
      ·
        refine ⟨8534447782070995327168513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11379263709427993769558017 8534447782070995327168513)
        ·
          refine ⟨6400835836553246495376385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8534447782070995327168513 6400835836553246495376385)
          ·
            refine ⟨4800626877414934871532289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6400835836553246495376385 4800626877414934871532289)
            ·
              refine ⟨3600470158061201153649217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4800626877414934871532289 3600470158061201153649217)
              ·
                refine ⟨2700352618545900865236913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3600470158061201153649217 2700352618545900865236913)
                ·
                  refine ⟨2025264463909425648927685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2700352618545900865236913 2025264463909425648927685)
                  ·
                    refine ⟨379737086983017309173941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2025264463909425648927685 379737086983017309173941)
                    ·
                      rfl

theorem cell23_2218606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 2, 2, 2, 4].length) (baseStart_2218606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2218606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2218606 prefixEnd_2218606 := by exact prefixLift 2218606
  have htrace : WordTrace (prefixWord ++ tailWord_2218606) baseStart_2218606 baseEnd_2218606 := by
    simpa [prefixWord, tailWord_2218606, baseEnd_2218606] using wordTrace_append hprefix tailTrace_2218606
  have hstable : (prefixWord ++ tailWord_2218606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2218606).length < 2 ^ (prefixWord ++ tailWord_2218606).sum := by decide
  have hdescent : baseEnd_2218606 < baseStart_2218606 := by decide
  rcases family_descends (prefixWord ++ tailWord_2218606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2218615 : List Nat := [1, 1, 3, 1, 1, 3, 3, 1, 2, 7]
def baseStart_2218615 : Nat := 118140960795 + 2218615 * 2 ^ 59
def prefixEnd_2218615 : Nat := 4983230072969 + 3 ^ 40 * 2218615 * 2
def baseEnd_2218615 : Nat := 379738627424980797436427

theorem tailTrace_2218615 : CollatzResearch.WordTrace tailWord_2218615 prefixEnd_2218615 379738627424980797436427 := by
  unfold tailWord_2218615
  simp only [CollatzResearch.WordTrace]
  refine ⟨80919536857344239120601299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53946357904896159413734199 80919536857344239120601299)
  ·
    refine ⟨121379305286016358680901949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80919536857344239120601299 121379305286016358680901949)
    ·
      refine ⟨45517239482256134505338231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 121379305286016358680901949 45517239482256134505338231)
      ·
        refine ⟨68275859223384201758007347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45517239482256134505338231 68275859223384201758007347)
        ·
          refine ⟨102413788835076302637011021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68275859223384201758007347 102413788835076302637011021)
          ·
            refine ⟨38405170813153613488879133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 102413788835076302637011021 38405170813153613488879133)
            ·
              refine ⟨14401939054932605058329675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38405170813153613488879133 14401939054932605058329675)
              ·
                refine ⟨21602908582398907587494513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14401939054932605058329675 21602908582398907587494513)
                ·
                  refine ⟨16202181436799180690620885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21602908582398907587494513 16202181436799180690620885)
                  ·
                    refine ⟨379738627424980797436427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 16202181436799180690620885 379738627424980797436427)
                    ·
                      rfl

theorem cell23_2218615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 3, 1, 2, 7].length) (baseStart_2218615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2218615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2218615 prefixEnd_2218615 := by exact prefixLift 2218615
  have htrace : WordTrace (prefixWord ++ tailWord_2218615) baseStart_2218615 baseEnd_2218615 := by
    simpa [prefixWord, tailWord_2218615, baseEnd_2218615] using wordTrace_append hprefix tailTrace_2218615
  have hstable : (prefixWord ++ tailWord_2218615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2218615).length < 2 ^ (prefixWord ++ tailWord_2218615).sum := by decide
  have hdescent : baseEnd_2218615 < baseStart_2218615 := by decide
  rcases family_descends (prefixWord ++ tailWord_2218615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2218629 : List Nat := [1, 3, 1, 1, 4, 3, 2, 1, 1, 3, 3]
def baseStart_2218629 : Nat := 118140960795 + 2218629 * 2 ^ 59
def prefixEnd_2218629 : Nat := 4983230072969 + 3 ^ 40 * 2218629 * 2
def baseEnd_2218629 : Nat := 1139223071004105337534217

theorem tailTrace_2218629 : CollatzResearch.WordTrace tailWord_2218629 prefixEnd_2218629 1139223071004105337534217 := by
  unfold tailWord_2218629
  simp only [CollatzResearch.WordTrace]
  refine ⟨80920047479293519511610941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53946698319529013007740627 80920047479293519511610941)
  ·
    refine ⟨30345017804735069816854103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 80920047479293519511610941 30345017804735069816854103)
    ·
      refine ⟨45517526707102604725281155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30345017804735069816854103 45517526707102604725281155)
      ·
        refine ⟨68276290060653907087921733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45517526707102604725281155 68276290060653907087921733)
        ·
          refine ⟨12801804386372607578985325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 68276290060653907087921733 12801804386372607578985325)
          ·
            refine ⟨4800676644889727842119497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12801804386372607578985325 4800676644889727842119497)
            ·
              refine ⟨3600507483667295881589623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4800676644889727842119497 3600507483667295881589623)
              ·
                refine ⟨5400761225500943822384435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3600507483667295881589623 5400761225500943822384435)
                ·
                  refine ⟨8101141838251415733576653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5400761225500943822384435 8101141838251415733576653)
                  ·
                    refine ⟨3037928189344280900091245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8101141838251415733576653 3037928189344280900091245)
                    ·
                      refine ⟨1139223071004105337534217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3037928189344280900091245 1139223071004105337534217)
                      ·
                        rfl

theorem cell23_2218629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 2, 1, 1, 3, 3].length) (baseStart_2218629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2218629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2218629 prefixEnd_2218629 := by exact prefixLift 2218629
  have htrace : WordTrace (prefixWord ++ tailWord_2218629) baseStart_2218629 baseEnd_2218629 := by
    simpa [prefixWord, tailWord_2218629, baseEnd_2218629] using wordTrace_append hprefix tailTrace_2218629
  have hstable : (prefixWord ++ tailWord_2218629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2218629).length < 2 ^ (prefixWord ++ tailWord_2218629).sum := by decide
  have hdescent : baseEnd_2218629 < baseStart_2218629 := by decide
  rcases family_descends (prefixWord ++ tailWord_2218629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2218650 : List Nat := [3, 1, 1, 6, 1, 2, 2, 1, 1, 2, 3]
def baseStart_2218650 : Nat := 118140960795 + 2218650 * 2 ^ 59
def prefixEnd_2218650 : Nat := 4983230072969 + 3 ^ 40 * 2218650 * 2
def baseEnd_2218650 : Nat := 1139233854097849755371621

theorem tailTrace_2218650 : CollatzResearch.WordTrace tailWord_2218650 prefixEnd_2218650 1139233854097849755371621 := by
  unfold tailWord_2218650
  simp only [CollatzResearch.WordTrace]
  refine ⟨20230203353054360024531351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53947208941478293398750269 20230203353054360024531351)
  ·
    refine ⟨30345305029581540036797027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20230203353054360024531351 30345305029581540036797027)
    ·
      refine ⟨45517957544372310055195541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30345305029581540036797027 45517957544372310055195541)
      ·
        refine ⟨2133654259892452033837291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 45517957544372310055195541 2133654259892452033837291)
        ·
          refine ⟨3200481389838678050755937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2133654259892452033837291 3200481389838678050755937)
          ·
            refine ⟨2400361042379008538066953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3200481389838678050755937 2400361042379008538066953)
            ·
              refine ⟨1800270781784256403550215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2400361042379008538066953 1800270781784256403550215)
              ·
                refine ⟨2700406172676384605325323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1800270781784256403550215 2700406172676384605325323)
                ·
                  refine ⟨4050609259014576907987985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2700406172676384605325323 4050609259014576907987985)
                  ·
                    refine ⟨3037956944260932680990989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4050609259014576907987985 3037956944260932680990989)
                    ·
                      refine ⟨1139233854097849755371621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3037956944260932680990989 1139233854097849755371621)
                      ·
                        rfl

theorem cell23_2218650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 2, 2, 1, 1, 2, 3].length) (baseStart_2218650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2218650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2218650 prefixEnd_2218650 := by exact prefixLift 2218650
  have htrace : WordTrace (prefixWord ++ tailWord_2218650) baseStart_2218650 baseEnd_2218650 := by
    simpa [prefixWord, tailWord_2218650, baseEnd_2218650] using wordTrace_append hprefix tailTrace_2218650
  have hstable : (prefixWord ++ tailWord_2218650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2218650).length < 2 ^ (prefixWord ++ tailWord_2218650).sum := by decide
  have hdescent : baseEnd_2218650 < baseStart_2218650 := by decide
  rcases family_descends (prefixWord ++ tailWord_2218650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2218663 : List Nat := [1, 1, 6, 3, 1, 1, 1, 1, 4, 1, 3]
def baseStart_2218663 : Nat := 118140960795 + 2218663 * 2 ^ 59
def prefixEnd_2218663 : Nat := 4983230072969 + 3 ^ 40 * 2218663 * 2
def baseEnd_2218663 : Nat := 1139240529346358204509061

theorem tailTrace_2218663 : CollatzResearch.WordTrace tailWord_2218663 prefixEnd_2218663 1139240529346358204509061 := by
  unfold tailWord_2218663
  simp only [CollatzResearch.WordTrace]
  refine ⟨80921287561170343318348643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53947525040780228878899095 80921287561170343318348643)
  ·
    refine ⟨121381931341755514977522965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80921287561170343318348643 121381931341755514977522965)
    ·
      refine ⟨5689778031644789764571389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 121381931341755514977522965 5689778031644789764571389)
      ·
        refine ⟨2133666761866796161714271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5689778031644789764571389 2133666761866796161714271)
        ·
          refine ⟨3200500142800194242571407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2133666761866796161714271 3200500142800194242571407)
          ·
            refine ⟨4800750214200291363857111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3200500142800194242571407 4800750214200291363857111)
            ·
              refine ⟨7201125321300437045785667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4800750214200291363857111 7201125321300437045785667)
              ·
                refine ⟨10801687981950655568678501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7201125321300437045785667 10801687981950655568678501)
                ·
                  refine ⟨2025316496615747919127219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10801687981950655568678501 2025316496615747919127219)
                  ·
                    refine ⟨3037974744923621878690829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2025316496615747919127219 3037974744923621878690829)
                    ·
                      refine ⟨1139240529346358204509061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3037974744923621878690829 1139240529346358204509061)
                      ·
                        rfl

theorem cell23_2218663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 1, 1, 4, 1, 3].length) (baseStart_2218663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2218663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2218663 prefixEnd_2218663 := by exact prefixLift 2218663
  have htrace : WordTrace (prefixWord ++ tailWord_2218663) baseStart_2218663 baseEnd_2218663 := by
    simpa [prefixWord, tailWord_2218663, baseEnd_2218663] using wordTrace_append hprefix tailTrace_2218663
  have hstable : (prefixWord ++ tailWord_2218663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2218663).length < 2 ^ (prefixWord ++ tailWord_2218663).sum := by decide
  have hdescent : baseEnd_2218663 < baseStart_2218663 := by decide
  rcases family_descends (prefixWord ++ tailWord_2218663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2218665 : List Nat := [1, 2, 1, 1, 1, 1, 2, 3, 2, 3, 6]
def baseStart_2218665 : Nat := 118140960795 + 2218665 * 2 ^ 59
def prefixEnd_2218665 : Nat := 4983230072969 + 3 ^ 40 * 2218665 * 2
def baseEnd_2218665 : Nat := 1139241556307667196684051

theorem tailTrace_2218665 : CollatzResearch.WordTrace tailWord_2218665 prefixEnd_2218665 1139241556307667196684051 := by
  unfold tailWord_2218665
  simp only [CollatzResearch.WordTrace]
  refine ⟨80921360507163097659921449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53947573671442065106614299 80921360507163097659921449)
  ·
    refine ⟨60691020380372323244941087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80921360507163097659921449 60691020380372323244941087)
    ·
      refine ⟨91036530570558484867411631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60691020380372323244941087 91036530570558484867411631)
      ·
        refine ⟨136554795855837727301117447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91036530570558484867411631 136554795855837727301117447)
        ·
          refine ⟨204832193783756590951676171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 136554795855837727301117447 204832193783756590951676171)
          ·
            refine ⟨307248290675634886427514257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 204832193783756590951676171 307248290675634886427514257)
            ·
              refine ⟨230436218006726164820635693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 307248290675634886427514257 230436218006726164820635693)
              ·
                refine ⟨86413581752522311807738385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 230436218006726164820635693 86413581752522311807738385)
                ·
                  refine ⟨64810186314391733855803789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 86413581752522311807738385 64810186314391733855803789)
                  ·
                    refine ⟨24303819867896900195926421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 64810186314391733855803789 24303819867896900195926421)
                    ·
                      refine ⟨1139241556307667196684051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 24303819867896900195926421 1139241556307667196684051)
                      ·
                        rfl

theorem cell23_2218665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 3, 2, 3, 6].length) (baseStart_2218665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2218665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2218665 prefixEnd_2218665 := by exact prefixLift 2218665
  have htrace : WordTrace (prefixWord ++ tailWord_2218665) baseStart_2218665 baseEnd_2218665 := by
    simpa [prefixWord, tailWord_2218665, baseEnd_2218665] using wordTrace_append hprefix tailTrace_2218665
  have hstable : (prefixWord ++ tailWord_2218665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2218665).length < 2 ^ (prefixWord ++ tailWord_2218665).sum := by decide
  have hdescent : baseEnd_2218665 < baseStart_2218665 := by decide
  rcases family_descends (prefixWord ++ tailWord_2218665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2218682 : List Nat := [3, 1, 1, 1, 2, 3, 1, 3, 2, 2, 4]
def baseStart_2218682 : Nat := 118140960795 + 2218682 * 2 ^ 59
def prefixEnd_2218682 : Nat := 4983230072969 + 3 ^ 40 * 2218682 * 2
def baseEnd_2218682 : Nat := 1139250285478793630171473

theorem tailTrace_2218682 : CollatzResearch.WordTrace tailWord_2218682 prefixEnd_2218682 1139250285478793630171473 := by
  unfold tailWord_2218682
  simp only [CollatzResearch.WordTrace]
  refine ⟨20230495137025377390822575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53947987032067673042193533 20230495137025377390822575)
  ·
    refine ⟨30345742705538066086233863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20230495137025377390822575 30345742705538066086233863)
    ·
      refine ⟨45518614058307099129350795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30345742705538066086233863 45518614058307099129350795)
      ·
        refine ⟨68277921087460648694026193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45518614058307099129350795 68277921087460648694026193)
        ·
          refine ⟨51208440815595486520519645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 68277921087460648694026193 51208440815595486520519645)
          ·
            refine ⟨19203165305848307445194867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 51208440815595486520519645 19203165305848307445194867)
            ·
              refine ⟨28804747958772461167792301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19203165305848307445194867 28804747958772461167792301)
              ·
                refine ⟨10801780484539672937922113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28804747958772461167792301 10801780484539672937922113)
                ·
                  refine ⟨8101335363404754703441585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10801780484539672937922113 8101335363404754703441585)
                  ·
                    refine ⟨6076001522553566027581189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8101335363404754703441585 6076001522553566027581189)
                    ·
                      refine ⟨1139250285478793630171473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6076001522553566027581189 1139250285478793630171473)
                      ·
                        rfl

theorem cell23_2218682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 3, 2, 2, 4].length) (baseStart_2218682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2218682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2218682 prefixEnd_2218682 := by exact prefixLift 2218682
  have htrace : WordTrace (prefixWord ++ tailWord_2218682) baseStart_2218682 baseEnd_2218682 := by
    simpa [prefixWord, tailWord_2218682, baseEnd_2218682] using wordTrace_append hprefix tailTrace_2218682
  have hstable : (prefixWord ++ tailWord_2218682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2218682).length < 2 ^ (prefixWord ++ tailWord_2218682).sum := by decide
  have hdescent : baseEnd_2218682 < baseStart_2218682 := by decide
  rcases family_descends (prefixWord ++ tailWord_2218682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2218833 : List Nat := [1, 2, 2, 1, 7, 1, 1, 2, 6]
def baseStart_2218833 : Nat := 118140960795 + 2218833 * 2 ^ 59
def prefixEnd_2218833 : Nat := 4983230072969 + 3 ^ 40 * 2218833 * 2
def baseEnd_2218833 : Nat := 126591980117513615487031

theorem tailTrace_2218833 : CollatzResearch.WordTrace tailWord_2218833 prefixEnd_2218833 126591980117513615487031 := by
  unfold tailWord_2218833
  simp only [CollatzResearch.WordTrace]
  refine ⟨80927487970554462352037153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53951658647036308234691435 80927487970554462352037153)
  ·
    refine ⟨60695615977915846764027865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80927487970554462352037153 60695615977915846764027865)
    ·
      refine ⟨45521711983436885073020899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60695615977915846764027865 45521711983436885073020899)
      ·
        refine ⟨68282567975155327609531349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45521711983436885073020899 68282567975155327609531349)
        ·
          refine ⟨1600372686917702990848391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 68282567975155327609531349 1600372686917702990848391)
          ·
            refine ⟨2400559030376554486272587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1600372686917702990848391 2400559030376554486272587)
            ·
              refine ⟨3600838545564831729408881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2400559030376554486272587 3600838545564831729408881)
              ·
                refine ⟨2700628909173623797056661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3600838545564831729408881 2700628909173623797056661)
                ·
                  refine ⟨126591980117513615487031, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2700628909173623797056661 126591980117513615487031)
                  ·
                    rfl

theorem cell23_2218833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 7, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 7, 1, 1, 2, 6].length) (baseStart_2218833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2218833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2218833 prefixEnd_2218833 := by exact prefixLift 2218833
  have htrace : WordTrace (prefixWord ++ tailWord_2218833) baseStart_2218833 baseEnd_2218833 := by
    simpa [prefixWord, tailWord_2218833, baseEnd_2218833] using wordTrace_append hprefix tailTrace_2218833
  have hstable : (prefixWord ++ tailWord_2218833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2218833).length < 2 ^ (prefixWord ++ tailWord_2218833).sum := by decide
  have hdescent : baseEnd_2218833 < baseStart_2218833 := by decide
  rcases family_descends (prefixWord ++ tailWord_2218833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2218849 : List Nat := [1, 2, 3, 1, 1, 1, 2, 4, 3, 1, 4]
def baseStart_2218849 : Nat := 118140960795 + 2218849 * 2 ^ 59
def prefixEnd_2218849 : Nat := 4983230072969 + 3 ^ 40 * 2218849 * 2
def baseEnd_2218849 : Nat := 1139336036748094476783205

theorem tailTrace_2218849 : CollatzResearch.WordTrace tailWord_2218849 prefixEnd_2218849 1139336036748094476783205 := by
  unfold tailWord_2218849
  simp only [CollatzResearch.WordTrace]
  refine ⟨80928071538496497084619601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53952047692330998056413067 80928071538496497084619601)
  ·
    refine ⟨60696053653872372813464701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80928071538496497084619601 60696053653872372813464701)
    ·
      refine ⟨22761020120202139805049263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 60696053653872372813464701 22761020120202139805049263)
      ·
        refine ⟨34141530180303209707573895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22761020120202139805049263 34141530180303209707573895)
        ·
          refine ⟨51212295270454814561360843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34141530180303209707573895 51212295270454814561360843)
          ·
            refine ⟨76818442905682221842041265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51212295270454814561360843 76818442905682221842041265)
            ·
              refine ⟨57613832179261666381530949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 76818442905682221842041265 57613832179261666381530949)
              ·
                refine ⟨10802593533611562446537053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 57613832179261666381530949 10802593533611562446537053)
                ·
                  refine ⟨4050972575104335917451395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10802593533611562446537053 4050972575104335917451395)
                  ·
                    refine ⟨6076458862656503876177093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4050972575104335917451395 6076458862656503876177093)
                    ·
                      refine ⟨1139336036748094476783205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6076458862656503876177093 1139336036748094476783205)
                      ·
                        rfl

theorem cell23_2218849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 4, 3, 1, 4].length) (baseStart_2218849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2218849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2218849 prefixEnd_2218849 := by exact prefixLift 2218849
  have htrace : WordTrace (prefixWord ++ tailWord_2218849) baseStart_2218849 baseEnd_2218849 := by
    simpa [prefixWord, tailWord_2218849, baseEnd_2218849] using wordTrace_append hprefix tailTrace_2218849
  have hstable : (prefixWord ++ tailWord_2218849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2218849).length < 2 ^ (prefixWord ++ tailWord_2218849).sum := by decide
  have hdescent : baseEnd_2218849 < baseStart_2218849 := by decide
  rcases family_descends (prefixWord ++ tailWord_2218849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2218859 : List Nat := [1, 1, 1, 1, 2, 2, 7, 1, 1, 6]
def baseStart_2218859 : Nat := 118140960795 + 2218859 * 2 ^ 59
def prefixEnd_2218859 : Nat := 4983230072969 + 3 ^ 40 * 2218859 * 2
def baseEnd_2218859 : Nat := 379780390518213145886053

theorem tailTrace_2218859 : CollatzResearch.WordTrace tailWord_2218859 prefixEnd_2218859 379780390518213145886053 := by
  unfold tailWord_2218859
  simp only [CollatzResearch.WordTrace]
  refine ⟨80928436268460268792483631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53952290845640179194989087 80928436268460268792483631)
  ·
    refine ⟨121392654402690403188725447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80928436268460268792483631 121392654402690403188725447)
    ·
      refine ⟨182088981604035604783088171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121392654402690403188725447 182088981604035604783088171)
      ·
        refine ⟨273133472406053407174632257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 182088981604035604783088171 273133472406053407174632257)
        ·
          refine ⟨204850104304540055380974193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 273133472406053407174632257 204850104304540055380974193)
          ·
            refine ⟨153637578228405041535730645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 204850104304540055380974193 153637578228405041535730645)
            ·
              refine ⟨3600880739728243160993687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 153637578228405041535730645 3600880739728243160993687)
              ·
                refine ⟨5401321109592364741490531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3600880739728243160993687 5401321109592364741490531)
                ·
                  refine ⟨8101981664388547112235797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5401321109592364741490531 8101981664388547112235797)
                  ·
                    refine ⟨379780390518213145886053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8101981664388547112235797 379780390518213145886053)
                    ·
                      rfl

theorem cell23_2218859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 7, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 7, 1, 1, 6].length) (baseStart_2218859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2218859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2218859 prefixEnd_2218859 := by exact prefixLift 2218859
  have htrace : WordTrace (prefixWord ++ tailWord_2218859) baseStart_2218859 baseEnd_2218859 := by
    simpa [prefixWord, tailWord_2218859, baseEnd_2218859] using wordTrace_append hprefix tailTrace_2218859
  have hstable : (prefixWord ++ tailWord_2218859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2218859).length < 2 ^ (prefixWord ++ tailWord_2218859).sum := by decide
  have hdescent : baseEnd_2218859 < baseStart_2218859 := by decide
  rcases family_descends (prefixWord ++ tailWord_2218859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2218866 : List Nat := [3, 2, 1, 2, 1, 1, 3, 4, 1, 1, 4]
def baseStart_2218866 : Nat := 118140960795 + 2218866 * 2 ^ 59
def prefixEnd_2218866 : Nat := 4983230072969 + 3 ^ 40 * 2218866 * 2
def baseEnd_2218866 : Nat := 1139344765919220910270627

theorem tailTrace_2218866 : CollatzResearch.WordTrace tailWord_2218866 prefixEnd_2218866 1139344765919220910270627 := by
  unfold tailWord_2218866
  simp only [CollatzResearch.WordTrace]
  refine ⟨20232172894858727246997113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53952461052956605991992301 20232172894858727246997113)
  ·
    refine ⟨15174129671144045435247835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20232172894858727246997113 15174129671144045435247835)
    ·
      refine ⟨22761194506716068152871753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15174129671144045435247835 22761194506716068152871753)
      ·
        refine ⟨17070895880037051114653815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22761194506716068152871753 17070895880037051114653815)
        ·
          refine ⟨25606343820055576671980723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17070895880037051114653815 25606343820055576671980723)
          ·
            refine ⟨38409515730083365007971085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25606343820055576671980723 38409515730083365007971085)
            ·
              refine ⟨14403568398781261877989157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38409515730083365007971085 14403568398781261877989157)
              ·
                refine ⟨2700669074771486602122967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14403568398781261877989157 2700669074771486602122967)
                ·
                  refine ⟨4051003612157229903184451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2700669074771486602122967 4051003612157229903184451)
                  ·
                    refine ⟨6076505418235844854776677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4051003612157229903184451 6076505418235844854776677)
                    ·
                      refine ⟨1139344765919220910270627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6076505418235844854776677 1139344765919220910270627)
                      ·
                        rfl

theorem cell23_2218866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 3, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 3, 4, 1, 1, 4].length) (baseStart_2218866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2218866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2218866 prefixEnd_2218866 := by exact prefixLift 2218866
  have htrace : WordTrace (prefixWord ++ tailWord_2218866) baseStart_2218866 baseEnd_2218866 := by
    simpa [prefixWord, tailWord_2218866, baseEnd_2218866] using wordTrace_append hprefix tailTrace_2218866
  have hstable : (prefixWord ++ tailWord_2218866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2218866).length < 2 ^ (prefixWord ++ tailWord_2218866).sum := by decide
  have hdescent : baseEnd_2218866 < baseStart_2218866 := by decide
  rcases family_descends (prefixWord ++ tailWord_2218866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2218879 : List Nat := [1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 4]
def baseStart_2218879 : Nat := 118140960795 + 2218879 * 2 ^ 59
def prefixEnd_2218879 : Nat := 4983230072969 + 3 ^ 40 * 2218879 * 2
def baseEnd_2218879 : Nat := 1139351441167729359408067

theorem tailTrace_2218879 : CollatzResearch.WordTrace tailWord_2218879 prefixEnd_2218879 1139351441167729359408067 := by
  unfold tailWord_2218879
  simp only [CollatzResearch.WordTrace]
  refine ⟨80929165728387812208211691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53952777152258541472141127 80929165728387812208211691)
  ·
    refine ⟨121393748592581718312317537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80929165728387812208211691 121393748592581718312317537)
    ·
      refine ⟨91045311444436288734238153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 121393748592581718312317537 91045311444436288734238153)
      ·
        refine ⟨68283983583327216550678615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 91045311444436288734238153 68283983583327216550678615)
        ·
          refine ⟨102425975374990824826017923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68283983583327216550678615 102425975374990824826017923)
          ·
            refine ⟨153638963062486237239026885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 102425975374990824826017923 153638963062486237239026885)
            ·
              refine ⟨28807305574216169482317541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 153638963062486237239026885 28807305574216169482317541)
              ·
                refine ⟨5401369795165531777934539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 28807305574216169482317541 5401369795165531777934539)
                ·
                  refine ⟨8102054692748297666901809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5401369795165531777934539 8102054692748297666901809)
                  ·
                    refine ⟨6076541019561223250176357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8102054692748297666901809 6076541019561223250176357)
                    ·
                      refine ⟨1139351441167729359408067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6076541019561223250176357 1139351441167729359408067)
                      ·
                        rfl

theorem cell23_2218879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 4].length) (baseStart_2218879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2218879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2218879 prefixEnd_2218879 := by exact prefixLift 2218879
  have htrace : WordTrace (prefixWord ++ tailWord_2218879) baseStart_2218879 baseEnd_2218879 := by
    simpa [prefixWord, tailWord_2218879, baseEnd_2218879] using wordTrace_append hprefix tailTrace_2218879
  have hstable : (prefixWord ++ tailWord_2218879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2218879).length < 2 ^ (prefixWord ++ tailWord_2218879).sum := by decide
  have hdescent : baseEnd_2218879 < baseStart_2218879 := by decide
  rcases family_descends (prefixWord ++ tailWord_2218879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2218889 : List Nat := [1, 2, 1, 1, 5, 4, 9]
def baseStart_2218889 : Nat := 118140960795 + 2218889 * 2 ^ 59
def prefixEnd_2218889 : Nat := 4983230072969 + 3 ^ 40 * 2218889 * 2
def baseEnd_2218889 : Nat := 14066130567583633583741

theorem tailTrace_2218889 : CollatzResearch.WordTrace tailWord_2218889 prefixEnd_2218889 14066130567583633583741 := by
  unfold tailWord_2218889
  simp only [CollatzResearch.WordTrace]
  refine ⟨80929530458351583916075721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53953020305567722610717147 80929530458351583916075721)
  ·
    refine ⟨60697147843763687937056791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80929530458351583916075721 60697147843763687937056791)
    ·
      refine ⟨91045721765645531905585187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60697147843763687937056791 91045721765645531905585187)
      ·
        refine ⟨136568582648468297858377781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91045721765645531905585187 136568582648468297858377781)
        ·
          refine ⟨12803304623293902924222917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 136568582648468297858377781 12803304623293902924222917)
          ·
            refine ⟨2400619616867606798291797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12803304623293902924222917 2400619616867606798291797)
            ·
              refine ⟨14066130567583633583741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2400619616867606798291797 14066130567583633583741)
              ·
                rfl

theorem cell23_2218889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 4, 9].length) (baseStart_2218889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2218889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2218889 prefixEnd_2218889 := by exact prefixLift 2218889
  have htrace : WordTrace (prefixWord ++ tailWord_2218889) baseStart_2218889 baseEnd_2218889 := by
    simpa [prefixWord, tailWord_2218889, baseEnd_2218889] using wordTrace_append hprefix tailTrace_2218889
  have hstable : (prefixWord ++ tailWord_2218889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2218889).length < 2 ^ (prefixWord ++ tailWord_2218889).sum := by decide
  have hdescent : baseEnd_2218889 < baseStart_2218889 := by decide
  rcases family_descends (prefixWord ++ tailWord_2218889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2218899 : List Nat := [1, 1, 1, 2, 1, 2, 1, 3, 5, 3, 3]
def baseStart_2218899 : Nat := 118140960795 + 2218899 * 2 ^ 59
def prefixEnd_2218899 : Nat := 4983230072969 + 3 ^ 40 * 2218899 * 2
def baseEnd_2218899 : Nat := 1139361710780819281157975

theorem tailTrace_2218899 : CollatzResearch.WordTrace tailWord_2218899 prefixEnd_2218899 1139361710780819281157975 := by
  unfold tailWord_2218899
  simp only [CollatzResearch.WordTrace]
  refine ⟨80929895188315355623939751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53953263458876903749293167 80929895188315355623939751)
  ·
    refine ⟨121394842782473033435909627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80929895188315355623939751 121394842782473033435909627)
    ·
      refine ⟨182092264173709550153864441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121394842782473033435909627 182092264173709550153864441)
      ·
        refine ⟨136569198130282162615398331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 182092264173709550153864441 136569198130282162615398331)
        ·
          refine ⟨204853797195423243923097497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 136569198130282162615398331 204853797195423243923097497)
          ·
            refine ⟨153640347896567432942323123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 204853797195423243923097497 153640347896567432942323123)
            ·
              refine ⟨230460521844851149413484685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 153640347896567432942323123 230460521844851149413484685)
              ·
                refine ⟨86422695691819181030056757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 230460521844851149413484685 86422695691819181030056757)
                ·
                  refine ⟨8102127721108048221567821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 86422695691819181030056757 8102127721108048221567821)
                  ·
                    refine ⟨3038297895415518083087933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8102127721108048221567821 3038297895415518083087933)
                    ·
                      refine ⟨1139361710780819281157975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3038297895415518083087933 1139361710780819281157975)
                      ·
                        rfl

theorem cell23_2218899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 3, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 3, 5, 3, 3].length) (baseStart_2218899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2218899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2218899 prefixEnd_2218899 := by exact prefixLift 2218899
  have htrace : WordTrace (prefixWord ++ tailWord_2218899) baseStart_2218899 baseEnd_2218899 := by
    simpa [prefixWord, tailWord_2218899, baseEnd_2218899] using wordTrace_append hprefix tailTrace_2218899
  have hstable : (prefixWord ++ tailWord_2218899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2218899).length < 2 ^ (prefixWord ++ tailWord_2218899).sum := by decide
  have hdescent : baseEnd_2218899 < baseStart_2218899 := by decide
  rcases family_descends (prefixWord ++ tailWord_2218899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2218906 : List Nat := [3, 1, 1, 4, 3, 1, 2, 8]
def baseStart_2218906 : Nat := 118140960795 + 2218906 * 2 ^ 59
def prefixEnd_2218906 : Nat := 4983230072969 + 3 ^ 40 * 2218906 * 2
def baseEnd_2218906 : Nat := 42198715005385213102609

theorem tailTrace_2218906 : CollatzResearch.WordTrace tailWord_2218906 prefixEnd_2218906 42198715005385213102609 := by
  unfold tailWord_2218906
  simp only [CollatzResearch.WordTrace]
  refine ⟨20232537624822498954861143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53953433666193330546296381 20232537624822498954861143)
  ·
    refine ⟨30348806437233748432291715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20232537624822498954861143 30348806437233748432291715)
    ·
      refine ⟨45523209655850622648437573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30348806437233748432291715 45523209655850622648437573)
      ·
        refine ⟨8535601810471991746582045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 45523209655850622648437573 8535601810471991746582045)
        ·
          refine ⟨3200850678926996904968267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8535601810471991746582045 3200850678926996904968267)
          ·
            refine ⟨4801276018390495357452401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3200850678926996904968267 4801276018390495357452401)
            ·
              refine ⟨3600957013792871518089301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4801276018390495357452401 3600957013792871518089301)
              ·
                refine ⟨42198715005385213102609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3600957013792871518089301 42198715005385213102609)
                ·
                  rfl

theorem cell23_2218906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 2, 8].length) (baseStart_2218906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2218906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2218906 prefixEnd_2218906 := by exact prefixLift 2218906
  have htrace : WordTrace (prefixWord ++ tailWord_2218906) baseStart_2218906 baseEnd_2218906 := by
    simpa [prefixWord, tailWord_2218906, baseEnd_2218906] using wordTrace_append hprefix tailTrace_2218906
  have hstable : (prefixWord ++ tailWord_2218906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2218906).length < 2 ^ (prefixWord ++ tailWord_2218906).sum := by decide
  have hdescent : baseEnd_2218906 < baseStart_2218906 := by decide
  rcases family_descends (prefixWord ++ tailWord_2218906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2218909 : List Nat := [1, 4, 2, 1, 2, 1, 1, 1, 2, 2, 6]
def baseStart_2218909 : Nat := 118140960795 + 2218909 * 2 ^ 59
def prefixEnd_2218909 : Nat := 4983230072969 + 3 ^ 40 * 2218909 * 2
def baseEnd_2218909 : Nat := 1139366845587364242032929

theorem tailTrace_2218909 : CollatzResearch.WordTrace tailWord_2218909 prefixEnd_2218909 1139366845587364242032929 := by
  unfold tailWord_2218909
  simp only [CollatzResearch.WordTrace]
  refine ⟨80930259918279127331803781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53953506612186084887869187 80930259918279127331803781)
  ·
    refine ⟨15174423734677336374713209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 80930259918279127331803781 15174423734677336374713209)
    ·
      refine ⟨11380817801008002281034907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15174423734677336374713209 11380817801008002281034907)
      ·
        refine ⟨17071226701512003421552361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11380817801008002281034907 17071226701512003421552361)
        ·
          refine ⟨12803420026134002566164271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17071226701512003421552361 12803420026134002566164271)
          ·
            refine ⟨19205130039201003849246407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12803420026134002566164271 19205130039201003849246407)
            ·
              refine ⟨28807695058801505773869611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19205130039201003849246407 28807695058801505773869611)
              ·
                refine ⟨43211542588202258660804417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28807695058801505773869611 43211542588202258660804417)
                ·
                  refine ⟨32408656941151693995603313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 43211542588202258660804417 32408656941151693995603313)
                  ·
                    refine ⟨24306492705863770496702485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 32408656941151693995603313 24306492705863770496702485)
                    ·
                      refine ⟨1139366845587364242032929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 24306492705863770496702485 1139366845587364242032929)
                      ·
                        rfl

theorem cell23_2218909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 1, 2, 2, 6].length) (baseStart_2218909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2218909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2218909 prefixEnd_2218909 := by exact prefixLift 2218909
  have htrace : WordTrace (prefixWord ++ tailWord_2218909) baseStart_2218909 baseEnd_2218909 := by
    simpa [prefixWord, tailWord_2218909, baseEnd_2218909] using wordTrace_append hprefix tailTrace_2218909
  have hstable : (prefixWord ++ tailWord_2218909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2218909).length < 2 ^ (prefixWord ++ tailWord_2218909).sum := by decide
  have hdescent : baseEnd_2218909 < baseStart_2218909 := by decide
  rcases family_descends (prefixWord ++ tailWord_2218909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2218916 : List Nat := [2, 3, 1, 2, 1, 2, 2, 3, 1, 3, 3]
def baseStart_2218916 : Nat := 118140960795 + 2218916 * 2 ^ 59
def prefixEnd_2218916 : Nat := 4983230072969 + 3 ^ 40 * 2218916 * 2
def baseEnd_2218916 : Nat := 1139370439951945714645397

theorem tailTrace_2218916 : CollatzResearch.WordTrace tailWord_2218916 prefixEnd_2218916 1139370439951945714645397 := by
  unfold tailWord_2218916
  simp only [CollatzResearch.WordTrace]
  refine ⟨40465257614626883763654301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53953676819502511684872401 40465257614626883763654301)
  ·
    refine ⟨15174471605485081411370363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40465257614626883763654301 15174471605485081411370363)
    ·
      refine ⟨22761707408227622117055545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15174471605485081411370363 22761707408227622117055545)
      ·
        refine ⟨17071280556170716587791659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22761707408227622117055545 17071280556170716587791659)
        ·
          refine ⟨25606920834256074881687489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17071280556170716587791659 25606920834256074881687489)
          ·
            refine ⟨19205190625692056161265617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25606920834256074881687489 19205190625692056161265617)
            ·
              refine ⟨14403892969269042120949213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19205190625692056161265617 14403892969269042120949213)
              ·
                refine ⟨5401459863475890795355955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14403892969269042120949213 5401459863475890795355955)
                ·
                  refine ⟨8102189795213836193033933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5401459863475890795355955 8102189795213836193033933)
                  ·
                    refine ⟨3038321173205188572387725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8102189795213836193033933 3038321173205188572387725)
                    ·
                      refine ⟨1139370439951945714645397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3038321173205188572387725 1139370439951945714645397)
                      ·
                        rfl

theorem cell23_2218916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 2, 3, 1, 3, 3].length) (baseStart_2218916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2218916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2218916 prefixEnd_2218916 := by exact prefixLift 2218916
  have htrace : WordTrace (prefixWord ++ tailWord_2218916) baseStart_2218916 baseEnd_2218916 := by
    simpa [prefixWord, tailWord_2218916, baseEnd_2218916] using wordTrace_append hprefix tailTrace_2218916
  have hstable : (prefixWord ++ tailWord_2218916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2218916).length < 2 ^ (prefixWord ++ tailWord_2218916).sum := by decide
  have hdescent : baseEnd_2218916 < baseStart_2218916 := by decide
  rcases family_descends (prefixWord ++ tailWord_2218916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2218957 : List Nat := [1, 6, 3, 1, 1, 2, 1, 8]
def baseStart_2218957 : Nat := 118140960795 + 2218957 * 2 ^ 59
def prefixEnd_2218957 : Nat := 4983230072969 + 3 ^ 40 * 2218957 * 2
def baseEnd_2218957 : Nat := 42199684913288150156767

theorem tailTrace_2218957 : CollatzResearch.WordTrace tailWord_2218957 prefixEnd_2218957 42199684913288150156767 := by
  unfold tailWord_2218957
  simp only [CollatzResearch.WordTrace]
  refine ⟨80932010622105231529551125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53954673748070154353034083 80932010622105231529551125)
  ·
    refine ⟨3793687997911182727947709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 80932010622105231529551125 3793687997911182727947709)
    ·
      refine ⟨1422632999216693522980391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3793687997911182727947709 1422632999216693522980391)
      ·
        refine ⟨2133949498825040284470587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1422632999216693522980391 2133949498825040284470587)
        ·
          refine ⟨3200924248237560426705881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2133949498825040284470587 3200924248237560426705881)
          ·
            refine ⟨2400693186178170320029411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3200924248237560426705881 2400693186178170320029411)
            ·
              refine ⟨3601039779267255480044117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2400693186178170320029411 3601039779267255480044117)
              ·
                refine ⟨42199684913288150156767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3601039779267255480044117 42199684913288150156767)
                ·
                  rfl

theorem cell23_2218957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 2, 1, 8].length) (baseStart_2218957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2218957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2218957 prefixEnd_2218957 := by exact prefixLift 2218957
  have htrace : WordTrace (prefixWord ++ tailWord_2218957) baseStart_2218957 baseEnd_2218957 := by
    simpa [prefixWord, tailWord_2218957, baseEnd_2218957] using wordTrace_append hprefix tailTrace_2218957
  have hstable : (prefixWord ++ tailWord_2218957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2218957).length < 2 ^ (prefixWord ++ tailWord_2218957).sum := by decide
  have hdescent : baseEnd_2218957 < baseStart_2218957 := by decide
  rcases family_descends (prefixWord ++ tailWord_2218957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2219047 : List Nat := [1, 1, 7, 1, 1, 3, 1, 3, 5]
def baseStart_2219047 : Nat := 118140960795 + 2219047 * 2 ^ 59
def prefixEnd_2219047 : Nat := 4983230072969 + 3 ^ 40 * 2219047 * 2
def baseEnd_2219047 : Nat := 126604189546409411345255

theorem tailTrace_2219047 : CollatzResearch.WordTrace tailWord_2219047 prefixEnd_2219047 126604189546409411345255 := by
  unfold tailWord_2219047
  simp only [CollatzResearch.WordTrace]
  refine ⟨80935293191779176900327395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53956862127852784600218263 80935293191779176900327395)
  ·
    refine ⟨121402939787668765350491093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80935293191779176900327395 121402939787668765350491093)
    ·
      refine ⟨2845381401273486687902135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 121402939787668765350491093 2845381401273486687902135)
      ·
        refine ⟨4268072101910230031853203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2845381401273486687902135 4268072101910230031853203)
        ·
          refine ⟨6402108152865345047779805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4268072101910230031853203 6402108152865345047779805)
          ·
            refine ⟨2400790557324504392917427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6402108152865345047779805 2400790557324504392917427)
            ·
              refine ⟨3601185835986756589376141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2400790557324504392917427 3601185835986756589376141)
              ·
                refine ⟨1350444688495033721016053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3601185835986756589376141 1350444688495033721016053)
                ·
                  refine ⟨126604189546409411345255, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1350444688495033721016053 126604189546409411345255)
                  ·
                    rfl

theorem cell23_2219047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 3, 1, 3, 5].length) (baseStart_2219047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2219047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2219047 prefixEnd_2219047 := by exact prefixLift 2219047
  have htrace : WordTrace (prefixWord ++ tailWord_2219047) baseStart_2219047 baseEnd_2219047 := by
    simpa [prefixWord, tailWord_2219047, baseEnd_2219047] using wordTrace_append hprefix tailTrace_2219047
  have hstable : (prefixWord ++ tailWord_2219047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2219047).length < 2 ^ (prefixWord ++ tailWord_2219047).sum := by decide
  have hdescent : baseEnd_2219047 < baseStart_2219047 := by decide
  rcases family_descends (prefixWord ++ tailWord_2219047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2219060 : List Nat := [2, 5, 1, 2, 1, 2, 1, 2, 2, 5]
def baseStart_2219060 : Nat := 118140960795 + 2219060 * 2 ^ 59
def prefixEnd_2219060 : Nat := 4983230072969 + 3 ^ 40 * 2219060 * 2
def baseEnd_2219060 : Nat := 379814793722064383748245

theorem tailTrace_2219060 : CollatzResearch.WordTrace tailWord_2219060 prefixEnd_2219060 379814793722064383748245 := by
  unfold tailWord_2219060
  simp only [CollatzResearch.WordTrace]
  refine ⟨40467883670366040060275317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53957178227154720080367089 40467883670366040060275317)
  ·
    refine ⟨3793864094096816255650811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 40467883670366040060275317 3793864094096816255650811)
    ·
      refine ⟨5690796141145224383476217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3793864094096816255650811 5690796141145224383476217)
      ·
        refine ⟨4268097105858918287607163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5690796141145224383476217 4268097105858918287607163)
        ·
          refine ⟨6402145658788377431410745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4268097105858918287607163 6402145658788377431410745)
          ·
            refine ⟨4801609244091283073558059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6402145658788377431410745 4801609244091283073558059)
            ·
              refine ⟨7202413866136924610337089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4801609244091283073558059 7202413866136924610337089)
              ·
                refine ⟨5401810399602693457752817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7202413866136924610337089 5401810399602693457752817)
                ·
                  refine ⟨4051357799702020093314613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5401810399602693457752817 4051357799702020093314613)
                  ·
                    refine ⟨379814793722064383748245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4051357799702020093314613 379814793722064383748245)
                    ·
                      rfl

theorem cell23_2219060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 1, 2, 2, 5].length) (baseStart_2219060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2219060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2219060 prefixEnd_2219060 := by exact prefixLift 2219060
  have htrace : WordTrace (prefixWord ++ tailWord_2219060) baseStart_2219060 baseEnd_2219060 := by
    simpa [prefixWord, tailWord_2219060, baseEnd_2219060] using wordTrace_append hprefix tailTrace_2219060
  have hstable : (prefixWord ++ tailWord_2219060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2219060).length < 2 ^ (prefixWord ++ tailWord_2219060).sum := by decide
  have hdescent : baseEnd_2219060 < baseStart_2219060 := by decide
  rcases family_descends (prefixWord ++ tailWord_2219060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2219100 : List Nat := [2, 2, 4, 1, 1, 1, 4, 1, 2, 2, 3]
def baseStart_2219100 : Nat := 118140960795 + 2219100 * 2 ^ 59
def prefixEnd_2219100 : Nat := 4983230072969 + 3 ^ 40 * 2219100 * 2
def baseEnd_2219100 : Nat := 1139464920392372994744551

theorem tailTrace_2219100 : CollatzResearch.WordTrace tailWord_2219100 prefixEnd_2219100 1139464920392372994744551 := by
  unfold tailWord_2219100
  simp only [CollatzResearch.WordTrace]
  refine ⟨40468613130293583476003377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53958150840391444634671169 40468613130293583476003377)
  ·
    refine ⟨30351459847720187607002533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40468613130293583476003377 30351459847720187607002533)
    ·
      refine ⟨5690898721447535176312975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 30351459847720187607002533 5690898721447535176312975)
      ·
        refine ⟨8536348082171302764469463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5690898721447535176312975 8536348082171302764469463)
        ·
          refine ⟨12804522123256954146704195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8536348082171302764469463 12804522123256954146704195)
          ·
            refine ⟨19206783184885431220056293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12804522123256954146704195 19206783184885431220056293)
            ·
              refine ⟨3601271847166018353760555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19206783184885431220056293 3601271847166018353760555)
              ·
                refine ⟨5401907770749027530640833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3601271847166018353760555 5401907770749027530640833)
                ·
                  refine ⟨4051430828061770647980625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5401907770749027530640833 4051430828061770647980625)
                  ·
                    refine ⟨3038573121046327985985469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4051430828061770647980625 3038573121046327985985469)
                    ·
                      refine ⟨1139464920392372994744551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3038573121046327985985469 1139464920392372994744551)
                      ·
                        rfl

theorem cell23_2219100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 4, 1, 2, 2, 3].length) (baseStart_2219100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2219100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2219100 prefixEnd_2219100 := by exact prefixLift 2219100
  have htrace : WordTrace (prefixWord ++ tailWord_2219100) baseStart_2219100 baseEnd_2219100 := by
    simpa [prefixWord, tailWord_2219100, baseEnd_2219100] using wordTrace_append hprefix tailTrace_2219100
  have hstable : (prefixWord ++ tailWord_2219100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2219100).length < 2 ^ (prefixWord ++ tailWord_2219100).sum := by decide
  have hdescent : baseEnd_2219100 < baseStart_2219100 := by decide
  rcases family_descends (prefixWord ++ tailWord_2219100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2219164 : List Nat := [2, 2, 3, 2, 1, 3, 2, 3, 1, 1, 3]
def baseStart_2219164 : Nat := 118140960795 + 2219164 * 2 ^ 59
def prefixEnd_2219164 : Nat := 4983230072969 + 3 ^ 40 * 2219164 * 2
def baseEnd_2219164 : Nat := 1139497783154260744344257

theorem tailTrace_2219164 : CollatzResearch.WordTrace tailWord_2219164 prefixEnd_2219164 1139497783154260744344257 := by
  unfold tailWord_2219164
  simp only [CollatzResearch.WordTrace]
  refine ⟨40469780266177652941168273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53959707021570203921557697 40469780266177652941168273)
  ·
    refine ⟨30352335199633239705876205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40469780266177652941168273 30352335199633239705876205)
    ·
      refine ⟨11382125699862464889703577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30352335199633239705876205 11382125699862464889703577)
      ·
        refine ⟨8536594274896848667277683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11382125699862464889703577 8536594274896848667277683)
        ·
          refine ⟨12804891412345273000916525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8536594274896848667277683 12804891412345273000916525)
          ·
            refine ⟨4801834279629477375343697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12804891412345273000916525 4801834279629477375343697)
            ·
              refine ⟨3601375709722108031507773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4801834279629477375343697 3601375709722108031507773)
              ·
                refine ⟨1350515891145790511815415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3601375709722108031507773 1350515891145790511815415)
                ·
                  refine ⟨2025773836718685767723123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1350515891145790511815415 2025773836718685767723123)
                  ·
                    refine ⟨3038660755078028651584685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2025773836718685767723123 3038660755078028651584685)
                    ·
                      refine ⟨1139497783154260744344257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3038660755078028651584685 1139497783154260744344257)
                      ·
                        rfl

theorem cell23_2219164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 2, 3, 1, 1, 3].length) (baseStart_2219164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2219164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2219164 prefixEnd_2219164 := by exact prefixLift 2219164
  have htrace : WordTrace (prefixWord ++ tailWord_2219164) baseStart_2219164 baseEnd_2219164 := by
    simpa [prefixWord, tailWord_2219164, baseEnd_2219164] using wordTrace_append hprefix tailTrace_2219164
  have hstable : (prefixWord ++ tailWord_2219164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2219164).length < 2 ^ (prefixWord ++ tailWord_2219164).sum := by decide
  have hdescent : baseEnd_2219164 < baseStart_2219164 := by decide
  rcases family_descends (prefixWord ++ tailWord_2219164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2219203 : List Nat := [1, 1, 1, 3, 1, 1, 1, 7, 1, 3, 3]
def baseStart_2219203 : Nat := 118140960795 + 2219203 * 2 ^ 59
def prefixEnd_2219203 : Nat := 4983230072969 + 3 ^ 40 * 2219203 * 2
def baseEnd_2219203 : Nat := 1139517808899786091756577

theorem tailTrace_2219203 : CollatzResearch.WordTrace tailWord_2219203 prefixEnd_2219203 1139517808899786091756577 := by
  unfold tailWord_2219203
  simp only [CollatzResearch.WordTrace]
  refine ⟨80940982979214015543006263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53960655319476010362004175 80940982979214015543006263)
  ·
    refine ⟨121411474468821023314509395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80940982979214015543006263 121411474468821023314509395)
    ·
      refine ⟨182117211703231534971764093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121411474468821023314509395 182117211703231534971764093)
      ·
        refine ⟨68293954388711825614411535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 182117211703231534971764093 68293954388711825614411535)
        ·
          refine ⟨102440931583067738421617303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68293954388711825614411535 102440931583067738421617303)
          ·
            refine ⟨153661397374601607632425955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 102440931583067738421617303 153661397374601607632425955)
            ·
              refine ⟨230492096061902411448638933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 153661397374601607632425955 230492096061902411448638933)
              ·
                refine ⟨5402158501450837768327475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 230492096061902411448638933 5402158501450837768327475)
                ·
                  refine ⟨8103237752176256652491213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5402158501450837768327475 8103237752176256652491213)
                  ·
                    refine ⟨3038714157066096244684205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8103237752176256652491213 3038714157066096244684205)
                    ·
                      refine ⟨1139517808899786091756577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3038714157066096244684205 1139517808899786091756577)
                      ·
                        rfl

theorem cell23_2219203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 7, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 7, 1, 3, 3].length) (baseStart_2219203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2219203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2219203 prefixEnd_2219203 := by exact prefixLift 2219203
  have htrace : WordTrace (prefixWord ++ tailWord_2219203) baseStart_2219203 baseEnd_2219203 := by
    simpa [prefixWord, tailWord_2219203, baseEnd_2219203] using wordTrace_append hprefix tailTrace_2219203
  have hstable : (prefixWord ++ tailWord_2219203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2219203).length < 2 ^ (prefixWord ++ tailWord_2219203).sum := by decide
  have hdescent : baseEnd_2219203 < baseStart_2219203 := by decide
  rcases family_descends (prefixWord ++ tailWord_2219203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2219210 : List Nat := [3, 1, 2, 1, 3, 4, 2, 7]
def baseStart_2219210 : Nat := 118140960795 + 2219210 * 2 ^ 59
def prefixEnd_2219210 : Nat := 4983230072969 + 3 ^ 40 * 2219210 * 2
def baseEnd_2219210 : Nat := 42204496417198798680335

theorem tailTrace_2219210 : CollatzResearch.WordTrace tailWord_2219210 prefixEnd_2219210 42204496417198798680335 := by
  unfold tailWord_2219210
  simp only [CollatzResearch.WordTrace]
  refine ⟨20235309572547163934627771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53960825526792437159007389 20235309572547163934627771)
  ·
    refine ⟨30352964358820745901941657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20235309572547163934627771 30352964358820745901941657)
    ·
      refine ⟨22764723269115559426456243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30352964358820745901941657 22764723269115559426456243)
      ·
        refine ⟨34147084903673339139684365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22764723269115559426456243 34147084903673339139684365)
        ·
          refine ⟨12805156838877502177381637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34147084903673339139684365 12805156838877502177381637)
          ·
            refine ⟨2400966907289531658259057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12805156838877502177381637 2400966907289531658259057)
            ·
              refine ⟨1800725180467148743694293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2400966907289531658259057 1800725180467148743694293)
              ·
                refine ⟨42204496417198798680335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1800725180467148743694293 42204496417198798680335)
                ·
                  rfl

theorem cell23_2219210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 4, 2, 7].length) (baseStart_2219210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2219210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2219210 prefixEnd_2219210 := by exact prefixLift 2219210
  have htrace : WordTrace (prefixWord ++ tailWord_2219210) baseStart_2219210 baseEnd_2219210 := by
    simpa [prefixWord, tailWord_2219210, baseEnd_2219210] using wordTrace_append hprefix tailTrace_2219210
  have hstable : (prefixWord ++ tailWord_2219210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2219210).length < 2 ^ (prefixWord ++ tailWord_2219210).sum := by decide
  have hdescent : baseEnd_2219210 < baseStart_2219210 := by decide
  rcases family_descends (prefixWord ++ tailWord_2219210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2219221 : List Nat := [1, 3, 2, 4, 1, 1, 3, 3, 1, 2, 2]
def baseStart_2219221 : Nat := 118140960795 + 2219221 * 2 ^ 59
def prefixEnd_2219221 : Nat := 4983230072969 + 3 ^ 40 * 2219221 * 2
def baseEnd_2219221 : Nat := 1139527051551567021331495

theorem tailTrace_2219221 : CollatzResearch.WordTrace tailWord_2219221 prefixEnd_2219221 1139527051551567021331495 := by
  unfold tailWord_2219221
  simp only [CollatzResearch.WordTrace]
  refine ⟨80941639493148804617161517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53961092995432536411441011 80941639493148804617161517)
  ·
    refine ⟨30353114809930801731435569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 80941639493148804617161517 30353114809930801731435569)
    ·
      refine ⟨22764836107448101298576677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30353114809930801731435569 22764836107448101298576677)
      ·
        refine ⟨4268406770146518993483127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22764836107448101298576677 4268406770146518993483127)
        ·
          refine ⟨6402610155219778490224691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4268406770146518993483127 6402610155219778490224691)
          ·
            refine ⟨9603915232829667735337037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6402610155219778490224691 9603915232829667735337037)
            ·
              refine ⟨3601468212311125400751389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9603915232829667735337037 3601468212311125400751389)
              ·
                refine ⟨1350550579616672025281771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3601468212311125400751389 1350550579616672025281771)
                ·
                  refine ⟨2025825869425008037922657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1350550579616672025281771 2025825869425008037922657)
                  ·
                    refine ⟨1519369402068756028441993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2025825869425008037922657 1519369402068756028441993)
                    ·
                      refine ⟨1139527051551567021331495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1519369402068756028441993 1139527051551567021331495)
                      ·
                        rfl

theorem cell23_2219221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 3, 3, 1, 2, 2].length) (baseStart_2219221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2219221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2219221 prefixEnd_2219221 := by exact prefixLift 2219221
  have htrace : WordTrace (prefixWord ++ tailWord_2219221) baseStart_2219221 baseEnd_2219221 := by
    simpa [prefixWord, tailWord_2219221, baseEnd_2219221] using wordTrace_append hprefix tailTrace_2219221
  have hstable : (prefixWord ++ tailWord_2219221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2219221).length < 2 ^ (prefixWord ++ tailWord_2219221).sum := by decide
  have hdescent : baseEnd_2219221 < baseStart_2219221 := by decide
  rcases family_descends (prefixWord ++ tailWord_2219221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2219263 : List Nat := [1, 1, 2, 2, 1, 5, 1, 2, 2, 1, 5]
def baseStart_2219263 : Nat := 118140960795 + 2219263 * 2 ^ 59
def prefixEnd_2219263 : Nat := 4983230072969 + 3 ^ 40 * 2219263 * 2
def baseEnd_2219263 : Nat := 1139548617739055857006301

theorem tailTrace_2219263 : CollatzResearch.WordTrace tailWord_2219263 prefixEnd_2219263 1139548617739055857006301 := by
  unfold tailWord_2219263
  simp only [CollatzResearch.WordTrace]
  refine ⟨80943171358996645790190443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53962114239331097193460295 80943171358996645790190443)
  ·
    refine ⟨121414757038494968685285665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80943171358996645790190443 121414757038494968685285665)
    ·
      refine ⟨91061067778871226513964249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 121414757038494968685285665 91061067778871226513964249)
      ·
        refine ⟨68295800834153419885473187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 91061067778871226513964249 68295800834153419885473187)
        ·
          refine ⟨102443701251230129828209781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68295800834153419885473187 102443701251230129828209781)
          ·
            refine ⟨9604096992302824671394667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 102443701251230129828209781 9604096992302824671394667)
            ·
              refine ⟨14406145488454237007092001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9604096992302824671394667 14406145488454237007092001)
              ·
                refine ⟨10804609116340677755319001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14406145488454237007092001 10804609116340677755319001)
                ·
                  refine ⟨8103456837255508316489251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10804609116340677755319001 8103456837255508316489251)
                  ·
                    refine ⟨12155185255883262474733877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8103456837255508316489251 12155185255883262474733877)
                    ·
                      refine ⟨1139548617739055857006301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12155185255883262474733877 1139548617739055857006301)
                      ·
                        rfl

theorem cell23_2219263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 1, 2, 2, 1, 5].length) (baseStart_2219263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2219263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2219263 prefixEnd_2219263 := by exact prefixLift 2219263
  have htrace : WordTrace (prefixWord ++ tailWord_2219263) baseStart_2219263 baseEnd_2219263 := by
    simpa [prefixWord, tailWord_2219263, baseEnd_2219263] using wordTrace_append hprefix tailTrace_2219263
  have hstable : (prefixWord ++ tailWord_2219263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2219263).length < 2 ^ (prefixWord ++ tailWord_2219263).sum := by decide
  have hdescent : baseEnd_2219263 < baseStart_2219263 := by decide
  rcases family_descends (prefixWord ++ tailWord_2219263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2219320 : List Nat := [2, 1, 2, 1, 3, 1, 1, 1, 4, 5, 2]
def baseStart_2219320 : Nat := 118140960795 + 2219320 * 2 ^ 59
def prefixEnd_2219320 : Nat := 4983230072969 + 3 ^ 40 * 2219320 * 2
def baseEnd_2219320 : Nat := 1139577886136362133993539

theorem tailTrace_2219320 : CollatzResearch.WordTrace tailWord_2219320 prefixEnd_2219320 1139577886136362133993539 := by
  unfold tailWord_2219320
  simp only [CollatzResearch.WordTrace]
  refine ⟨40472625159895072262507707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53963500213193429683343609 40472625159895072262507707)
  ·
    refine ⟨60708937739842608393761561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40472625159895072262507707 60708937739842608393761561)
    ·
      refine ⟨45531703304881956295321171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60708937739842608393761561 45531703304881956295321171)
      ·
        refine ⟨68297554957322934442981757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45531703304881956295321171 68297554957322934442981757)
        ·
          refine ⟨25611583108996100416118159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 68297554957322934442981757 25611583108996100416118159)
          ·
            refine ⟨38417374663494150624177239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25611583108996100416118159 38417374663494150624177239)
            ·
              refine ⟨57626061995241225936265859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38417374663494150624177239 57626061995241225936265859)
              ·
                refine ⟨86439092992861838904398789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 57626061995241225936265859 86439092992861838904398789)
                ·
                  refine ⟨16207329936161594794574773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 86439092992861838904398789 16207329936161594794574773)
                  ·
                    refine ⟨1519437181515149511991385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 16207329936161594794574773 1519437181515149511991385)
                    ·
                      refine ⟨1139577886136362133993539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1519437181515149511991385 1139577886136362133993539)
                      ·
                        rfl

theorem cell23_2219320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 1, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 1, 4, 5, 2].length) (baseStart_2219320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2219320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2219320 prefixEnd_2219320 := by exact prefixLift 2219320
  have htrace : WordTrace (prefixWord ++ tailWord_2219320) baseStart_2219320 baseEnd_2219320 := by
    simpa [prefixWord, tailWord_2219320, baseEnd_2219320] using wordTrace_append hprefix tailTrace_2219320
  have hstable : (prefixWord ++ tailWord_2219320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2219320).length < 2 ^ (prefixWord ++ tailWord_2219320).sum := by decide
  have hdescent : baseEnd_2219320 < baseStart_2219320 := by decide
  rcases family_descends (prefixWord ++ tailWord_2219320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2219353 : List Nat := [1, 2, 1, 2, 2, 2, 2, 1, 2, 3, 5]
def baseStart_2219353 : Nat := 118140960795 + 2219353 * 2 ^ 59
def prefixEnd_2219353 : Nat := 4983230072969 + 3 ^ 40 * 2219353 * 2
def baseEnd_2219353 : Nat := 1139594830997960504880887

theorem tailTrace_2219353 : CollatzResearch.WordTrace tailWord_2219353 prefixEnd_2219353 1139594830997960504880887 := by
  unfold tailWord_2219353
  simp only [CollatzResearch.WordTrace]
  refine ⟨80946453928670591160966713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53964302619113727440644475 80946453928670591160966713)
  ·
    refine ⟨60709840446502943370725035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80946453928670591160966713 60709840446502943370725035)
    ·
      refine ⟨91064760669754415056087553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60709840446502943370725035 91064760669754415056087553)
      ·
        refine ⟨68298570502315811292065665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 91064760669754415056087553 68298570502315811292065665)
        ·
          refine ⟨51223927876736858469049249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 68298570502315811292065665 51223927876736858469049249)
          ·
            refine ⟨38417945907552643851786937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51223927876736858469049249 38417945907552643851786937)
            ·
              refine ⟨28813459430664482888840203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38417945907552643851786937 28813459430664482888840203)
              ·
                refine ⟨43220189145996724333260305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28813459430664482888840203 43220189145996724333260305)
                ·
                  refine ⟨32415141859497543249945229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 43220189145996724333260305 32415141859497543249945229)
                  ·
                    refine ⟨12155678197311578718729461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 32415141859497543249945229 12155678197311578718729461)
                    ·
                      refine ⟨1139594830997960504880887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12155678197311578718729461 1139594830997960504880887)
                      ·
                        rfl

theorem cell23_2219353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 1, 2, 3, 5].length) (baseStart_2219353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2219353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2219353 prefixEnd_2219353 := by exact prefixLift 2219353
  have htrace : WordTrace (prefixWord ++ tailWord_2219353) baseStart_2219353 baseEnd_2219353 := by
    simpa [prefixWord, tailWord_2219353, baseEnd_2219353] using wordTrace_append hprefix tailTrace_2219353
  have hstable : (prefixWord ++ tailWord_2219353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2219353).length < 2 ^ (prefixWord ++ tailWord_2219353).sum := by decide
  have hdescent : baseEnd_2219353 < baseStart_2219353 := by decide
  rcases family_descends (prefixWord ++ tailWord_2219353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2219427 : List Nat := [1, 1, 1, 4, 1, 3, 1, 2, 4, 3, 2]
def baseStart_2219427 : Nat := 118140960795 + 2219427 * 2 ^ 59
def prefixEnd_2219427 : Nat := 4983230072969 + 3 ^ 40 * 2219427 * 2
def baseEnd_2219427 : Nat := 1139632828566393215355547

theorem tailTrace_2219427 : CollatzResearch.WordTrace tailWord_2219427 prefixEnd_2219427 1139632828566393215355547 := by
  unfold tailWord_2219427
  simp only [CollatzResearch.WordTrace]
  refine ⟨80949152930402501799160535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53966101953601667866107023 80949152930402501799160535)
  ·
    refine ⟨121423729395603752698740803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80949152930402501799160535 121423729395603752698740803)
    ·
      refine ⟨182135594093405629048111205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121423729395603752698740803 182135594093405629048111205)
      ·
        refine ⟨34150423892513555446520851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 182135594093405629048111205 34150423892513555446520851)
        ·
          refine ⟨51225635838770333169781277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34150423892513555446520851 51225635838770333169781277)
          ·
            refine ⟨19209613439538874938667979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 51225635838770333169781277 19209613439538874938667979)
            ·
              refine ⟨28814420159308312408001969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19209613439538874938667979 28814420159308312408001969)
              ·
                refine ⟨21610815119481234306001477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28814420159308312408001969 21610815119481234306001477)
                ·
                  refine ⟨4052027834902731432375277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21610815119481234306001477 4052027834902731432375277)
                  ·
                    refine ⟨1519510438088524287140729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4052027834902731432375277 1519510438088524287140729)
                    ·
                      refine ⟨1139632828566393215355547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1519510438088524287140729 1139632828566393215355547)
                      ·
                        rfl

theorem cell23_2219427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 2, 4, 3, 2].length) (baseStart_2219427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2219427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2219427 prefixEnd_2219427 := by exact prefixLift 2219427
  have htrace : WordTrace (prefixWord ++ tailWord_2219427) baseStart_2219427 baseEnd_2219427 := by
    simpa [prefixWord, tailWord_2219427, baseEnd_2219427] using wordTrace_append hprefix tailTrace_2219427
  have hstable : (prefixWord ++ tailWord_2219427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2219427).length < 2 ^ (prefixWord ++ tailWord_2219427).sum := by decide
  have hdescent : baseEnd_2219427 < baseStart_2219427 := by decide
  rcases family_descends (prefixWord ++ tailWord_2219427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2219467 : List Nat := [1, 1, 1, 1, 3, 3, 3, 4, 2, 4]
def baseStart_2219467 : Nat := 118140960795 + 2219467 * 2 ^ 59
def prefixEnd_2219467 : Nat := 4983230072969 + 3 ^ 40 * 2219467 * 2
def baseEnd_2219467 : Nat := 379884455930857686285121

theorem tailTrace_2219467 : CollatzResearch.WordTrace tailWord_2219467 prefixEnd_2219467 379884455930857686285121 := by
  unfold tailWord_2219467
  simp only [CollatzResearch.WordTrace]
  refine ⟨80950611850257588630616655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53967074566838392420411103 80950611850257588630616655)
  ·
    refine ⟨121425917775386382945924983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80950611850257588630616655 121425917775386382945924983)
    ·
      refine ⟨182138876663079574418887475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121425917775386382945924983 182138876663079574418887475)
      ·
        refine ⟨273208314994619361628331213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 182138876663079574418887475 273208314994619361628331213)
        ·
          refine ⟨102453118122982260610624205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 273208314994619361628331213 102453118122982260610624205)
          ·
            refine ⟨38419919296118347728984077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 102453118122982260610624205 38419919296118347728984077)
            ·
              refine ⟨14407469736044380398369029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38419919296118347728984077 14407469736044380398369029)
              ·
                refine ⟨2701400575508321324694193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14407469736044380398369029 2701400575508321324694193)
                ·
                  refine ⟨2026050431631240993520645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2701400575508321324694193 2026050431631240993520645)
                  ·
                    refine ⟨379884455930857686285121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2026050431631240993520645 379884455930857686285121)
                    ·
                      rfl

theorem cell23_2219467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 3, 4, 2, 4].length) (baseStart_2219467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2219467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2219467 prefixEnd_2219467 := by exact prefixLift 2219467
  have htrace : WordTrace (prefixWord ++ tailWord_2219467) baseStart_2219467 baseEnd_2219467 := by
    simpa [prefixWord, tailWord_2219467, baseEnd_2219467] using wordTrace_append hprefix tailTrace_2219467
  have hstable : (prefixWord ++ tailWord_2219467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2219467).length < 2 ^ (prefixWord ++ tailWord_2219467).sum := by decide
  have hdescent : baseEnd_2219467 < baseStart_2219467 := by decide
  rcases family_descends (prefixWord ++ tailWord_2219467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2219468 : List Nat := [2, 2, 1, 4, 2, 1, 4, 2, 1, 1, 3]
def baseStart_2219468 : Nat := 118140960795 + 2219468 * 2 ^ 59
def prefixEnd_2219468 : Nat := 4983230072969 + 3 ^ 40 * 2219468 * 2
def baseEnd_2219468 : Nat := 1139653881273227554942859

theorem tailTrace_2219468 : CollatzResearch.WordTrace tailWord_2219468 prefixEnd_2219468 1139653881273227554942859 := by
  unfold tailWord_2219468
  simp only [CollatzResearch.WordTrace]
  refine ⟨40475324161626982900701529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53967098882169310534268705 40475324161626982900701529)
  ·
    refine ⟨30356493121220237175526147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40475324161626982900701529 30356493121220237175526147)
    ·
      refine ⟨45534739681830355763289221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30356493121220237175526147 45534739681830355763289221)
      ·
        refine ⟨8537763690343191705616729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 45534739681830355763289221 8537763690343191705616729)
        ·
          refine ⟨6403322767757393779212547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8537763690343191705616729 6403322767757393779212547)
          ·
            refine ⟨9604984151636090668818821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6403322767757393779212547 9604984151636090668818821)
            ·
              refine ⟨1800934528431767000403529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9604984151636090668818821 1800934528431767000403529)
              ·
                refine ⟨1350700896323825250302647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1800934528431767000403529 1350700896323825250302647)
                ·
                  refine ⟨2026051344485737875453971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1350700896323825250302647 2026051344485737875453971)
                  ·
                    refine ⟨3039077016728606813180957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2026051344485737875453971 3039077016728606813180957)
                    ·
                      refine ⟨1139653881273227554942859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3039077016728606813180957 1139653881273227554942859)
                      ·
                        rfl

theorem cell23_2219468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 4, 2, 1, 1, 3].length) (baseStart_2219468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2219468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2219468 prefixEnd_2219468 := by exact prefixLift 2219468
  have htrace : WordTrace (prefixWord ++ tailWord_2219468) baseStart_2219468 baseEnd_2219468 := by
    simpa [prefixWord, tailWord_2219468, baseEnd_2219468] using wordTrace_append hprefix tailTrace_2219468
  have hstable : (prefixWord ++ tailWord_2219468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2219468).length < 2 ^ (prefixWord ++ tailWord_2219468).sum := by decide
  have hdescent : baseEnd_2219468 < baseStart_2219468 := by decide
  rcases family_descends (prefixWord ++ tailWord_2219468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2219470 : List Nat := [4, 1, 1, 1, 2, 1, 2, 1, 3, 1, 6]
def baseStart_2219470 : Nat := 118140960795 + 2219470 * 2 ^ 59
def prefixEnd_2219470 : Nat := 4983230072969 + 3 ^ 40 * 2219470 * 2
def baseEnd_2219470 : Nat := 1139654908234536547117849

theorem tailTrace_2219470 : CollatzResearch.WordTrace tailWord_2219470 prefixEnd_2219470 1139654908234536547117849 := by
  unfold tailWord_2219470
  simp only [CollatzResearch.WordTrace]
  refine ⟨10118840158655840017871983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 53967147512831146761983909 10118840158655840017871983)
  ·
    refine ⟨15178260237983760026807975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10118840158655840017871983 15178260237983760026807975)
    ·
      refine ⟨22767390356975640040211963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15178260237983760026807975 22767390356975640040211963)
      ·
        refine ⟨34151085535463460060317945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22767390356975640040211963 34151085535463460060317945)
        ·
          refine ⟨25613314151597595045238459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34151085535463460060317945 25613314151597595045238459)
          ·
            refine ⟨38419971227396392567857689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25613314151597595045238459 38419971227396392567857689)
            ·
              refine ⟨28814978420547294425893267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38419971227396392567857689 28814978420547294425893267)
              ·
                refine ⟨43222467630820941638839901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28814978420547294425893267 43222467630820941638839901)
                ·
                  refine ⟨16208425361557853114564963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 43222467630820941638839901 16208425361557853114564963)
                  ·
                    refine ⟨24312638042336779671847445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16208425361557853114564963 24312638042336779671847445)
                    ·
                      refine ⟨1139654908234536547117849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 24312638042336779671847445 1139654908234536547117849)
                      ·
                        rfl

theorem cell23_2219470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 1, 3, 1, 6].length) (baseStart_2219470 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2219470 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2219470 prefixEnd_2219470 := by exact prefixLift 2219470
  have htrace : WordTrace (prefixWord ++ tailWord_2219470) baseStart_2219470 baseEnd_2219470 := by
    simpa [prefixWord, tailWord_2219470, baseEnd_2219470] using wordTrace_append hprefix tailTrace_2219470
  have hstable : (prefixWord ++ tailWord_2219470).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2219470).length < 2 ^ (prefixWord ++ tailWord_2219470).sum := by decide
  have hdescent : baseEnd_2219470 < baseStart_2219470 := by decide
  rcases family_descends (prefixWord ++ tailWord_2219470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2219477 : List Nat := [1, 3, 2, 3, 1, 1, 1, 1, 5, 2, 3]
def baseStart_2219477 : Nat := 118140960795 + 2219477 * 2 ^ 59
def prefixEnd_2219477 : Nat := 4983230072969 + 3 ^ 40 * 2219477 * 2
def baseEnd_2219477 : Nat := 1139658502599118019730317

theorem tailTrace_2219477 : CollatzResearch.WordTrace tailWord_2219477 prefixEnd_2219477 1139658502599118019730317 := by
  unfold tailWord_2219477
  simp only [CollatzResearch.WordTrace]
  refine ⟨80950976580221360338480685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53967317720147573558987123 80950976580221360338480685)
  ·
    refine ⟨30356616217583010126930257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 80950976580221360338480685 30356616217583010126930257)
    ·
      refine ⟨22767462163187257595197693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30356616217583010126930257 22767462163187257595197693)
      ·
        refine ⟨8537798311195221598199135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22767462163187257595197693 8537798311195221598199135)
        ·
          refine ⟨12806697466792832397298703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8537798311195221598199135 12806697466792832397298703)
          ·
            refine ⟨19210046200189248595948055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12806697466792832397298703 19210046200189248595948055)
            ·
              refine ⟨28815069300283872893922083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19210046200189248595948055 28815069300283872893922083)
              ·
                refine ⟨43222603950425809340883125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28815069300283872893922083 43222603950425809340883125)
                ·
                  refine ⟨4052119120352419625707793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 43222603950425809340883125 4052119120352419625707793)
                  ·
                    refine ⟨3039089340264314719280845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4052119120352419625707793 3039089340264314719280845)
                    ·
                      refine ⟨1139658502599118019730317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3039089340264314719280845 1139658502599118019730317)
                      ·
                        rfl

theorem cell23_2219477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 1, 5, 2, 3].length) (baseStart_2219477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2219477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2219477 prefixEnd_2219477 := by exact prefixLift 2219477
  have htrace : WordTrace (prefixWord ++ tailWord_2219477) baseStart_2219477 baseEnd_2219477 := by
    simpa [prefixWord, tailWord_2219477, baseEnd_2219477] using wordTrace_append hprefix tailTrace_2219477
  have hstable : (prefixWord ++ tailWord_2219477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2219477).length < 2 ^ (prefixWord ++ tailWord_2219477).sum := by decide
  have hdescent : baseEnd_2219477 < baseStart_2219477 := by decide
  rcases family_descends (prefixWord ++ tailWord_2219477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2219480 : List Nat := [2, 1, 2, 2, 2, 1, 5, 8]
def baseStart_2219480 : Nat := 118140960795 + 2219480 * 2 ^ 59
def prefixEnd_2219480 : Nat := 4983230072969 + 3 ^ 40 * 2219480 * 2
def baseEnd_2219480 : Nat := 42209631223743759555289

theorem tailTrace_2219480 : CollatzResearch.WordTrace tailWord_2219480 prefixEnd_2219480 42209631223743759555289 := by
  unfold tailWord_2219480
  simp only [CollatzResearch.WordTrace]
  refine ⟨40475542999605245925419947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53967390666140327900559929 40475542999605245925419947)
  ·
    refine ⟨60713314499407868888129921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40475542999605245925419947 60713314499407868888129921)
    ·
      refine ⟨45534985874555901666097441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60713314499407868888129921 45534985874555901666097441)
      ·
        refine ⟨34151239405916926249573081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45534985874555901666097441 34151239405916926249573081)
        ·
          refine ⟨25613429554437694687179811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34151239405916926249573081 25613429554437694687179811)
          ·
            refine ⟨38420144331656542030769717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25613429554437694687179811 38420144331656542030769717)
            ·
              refine ⟨3601888531092800815384661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 38420144331656542030769717 3601888531092800815384661)
              ·
                refine ⟨42209631223743759555289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3601888531092800815384661 42209631223743759555289)
                ·
                  rfl

theorem cell23_2219480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 5, 8].length) (baseStart_2219480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2219480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2219480 prefixEnd_2219480 := by exact prefixLift 2219480
  have htrace : WordTrace (prefixWord ++ tailWord_2219480) baseStart_2219480 baseEnd_2219480 := by
    simpa [prefixWord, tailWord_2219480, baseEnd_2219480] using wordTrace_append hprefix tailTrace_2219480
  have hstable : (prefixWord ++ tailWord_2219480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2219480).length < 2 ^ (prefixWord ++ tailWord_2219480).sum := by decide
  have hdescent : baseEnd_2219480 < baseStart_2219480 := by decide
  rcases family_descends (prefixWord ++ tailWord_2219480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2219487 : List Nat := [1, 1, 2, 3, 3, 1, 4, 1, 1, 2, 4]
def baseStart_2219487 : Nat := 118140960795 + 2219487 * 2 ^ 59
def prefixEnd_2219487 : Nat := 4983230072969 + 3 ^ 40 * 2219487 * 2
def baseEnd_2219487 : Nat := 1139663637405662980605271

theorem tailTrace_2219487 : CollatzResearch.WordTrace tailWord_2219487 prefixEnd_2219487 1139663637405662980605271 := by
  unfold tailWord_2219487
  simp only [CollatzResearch.WordTrace]
  refine ⟨80951341310185132046344715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53967560873456754697563143 80951341310185132046344715)
  ·
    refine ⟨121427011965277698069517073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80951341310185132046344715 121427011965277698069517073)
    ·
      refine ⟨91070258973958273552137805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 121427011965277698069517073 91070258973958273552137805)
      ·
        refine ⟨34151347115234352582051677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 91070258973958273552137805 34151347115234352582051677)
        ·
          refine ⟨12806755168212882218269379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34151347115234352582051677 12806755168212882218269379)
          ·
            refine ⟨19210132752319323327404069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12806755168212882218269379 19210132752319323327404069)
            ·
              refine ⟨3601899891059873123888263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19210132752319323327404069 3601899891059873123888263)
              ·
                refine ⟨5402849836589809685832395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3601899891059873123888263 5402849836589809685832395)
                ·
                  refine ⟨8104274754884714528748593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5402849836589809685832395 8104274754884714528748593)
                  ·
                    refine ⟨6078206066163535896561445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8104274754884714528748593 6078206066163535896561445)
                    ·
                      refine ⟨1139663637405662980605271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6078206066163535896561445 1139663637405662980605271)
                      ·
                        rfl

theorem cell23_2219487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 4, 1, 1, 2, 4].length) (baseStart_2219487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2219487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2219487 prefixEnd_2219487 := by exact prefixLift 2219487
  have htrace : WordTrace (prefixWord ++ tailWord_2219487) baseStart_2219487 baseEnd_2219487 := by
    simpa [prefixWord, tailWord_2219487, baseEnd_2219487] using wordTrace_append hprefix tailTrace_2219487
  have hstable : (prefixWord ++ tailWord_2219487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2219487).length < 2 ^ (prefixWord ++ tailWord_2219487).sum := by decide
  have hdescent : baseEnd_2219487 < baseStart_2219487 := by decide
  rcases family_descends (prefixWord ++ tailWord_2219487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2219491 : List Nat := [1, 1, 1, 6, 2, 2, 1, 2, 3, 2, 2]
def baseStart_2219491 : Nat := 118140960795 + 2219491 * 2 ^ 59
def prefixEnd_2219491 : Nat := 4983230072969 + 3 ^ 40 * 2219491 * 2
def baseEnd_2219491 : Nat := 1139665691328280964955253

theorem tailTrace_2219491 : CollatzResearch.WordTrace tailWord_2219491 prefixEnd_2219491 1139665691328280964955253 := by
  unfold tailWord_2219491
  simp only [CollatzResearch.WordTrace]
  refine ⟨80951487202170640729490327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53967658134780427152993551 80951487202170640729490327)
  ·
    refine ⟨121427230803255961094235491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80951487202170640729490327 121427230803255961094235491)
    ·
      refine ⟨182140846204883941641353237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121427230803255961094235491 182140846204883941641353237)
      ·
        refine ⟨8537852165853934764438433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 182140846204883941641353237 8537852165853934764438433)
        ·
          refine ⟨6403389124390451073328825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8537852165853934764438433 6403389124390451073328825)
          ·
            refine ⟨4802541843292838304996619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6403389124390451073328825 4802541843292838304996619)
            ·
              refine ⟨7203812764939257457494929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4802541843292838304996619 7203812764939257457494929)
              ·
                refine ⟨5402859573704443093121197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7203812764939257457494929 5402859573704443093121197)
                ·
                  refine ⟨2026072340139166159920449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5402859573704443093121197 2026072340139166159920449)
                  ·
                    refine ⟨1519554255104374619940337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2026072340139166159920449 1519554255104374619940337)
                    ·
                      refine ⟨1139665691328280964955253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1519554255104374619940337 1139665691328280964955253)
                      ·
                        rfl

theorem cell23_2219491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 1, 2, 3, 2, 2].length) (baseStart_2219491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2219491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2219491 prefixEnd_2219491 := by exact prefixLift 2219491
  have htrace : WordTrace (prefixWord ++ tailWord_2219491) baseStart_2219491 baseEnd_2219491 := by
    simpa [prefixWord, tailWord_2219491, baseEnd_2219491] using wordTrace_append hprefix tailTrace_2219491
  have hstable : (prefixWord ++ tailWord_2219491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2219491).length < 2 ^ (prefixWord ++ tailWord_2219491).sum := by decide
  have hdescent : baseEnd_2219491 < baseStart_2219491 := by decide
  rcases family_descends (prefixWord ++ tailWord_2219491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2219634 : List Nat := [3, 2, 1, 2, 3, 1, 2, 2, 2, 5]
def baseStart_2219634 : Nat := 118140960795 + 2219634 * 2 ^ 59
def prefixEnd_2219634 : Nat := 4983230072969 + 3 ^ 40 * 2219634 * 2
def baseEnd_2219634 : Nat := 379913039687291301822365

theorem tailTrace_2219634 : CollatzResearch.WordTrace tailWord_2219634 prefixEnd_2219634 379913039687291301822365 := by
  unfold tailWord_2219634
  simp only [CollatzResearch.WordTrace]
  refine ⟨20239175710163144037986489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53971135227101717434630637 20239175710163144037986489)
  ·
    refine ⟨15179381782622358028489867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20239175710163144037986489 15179381782622358028489867)
    ·
      refine ⟨22769072673933537042734801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15179381782622358028489867 22769072673933537042734801)
      ·
        refine ⟨17076804505450152782051101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22769072673933537042734801 17076804505450152782051101)
        ·
          refine ⟨6403801689543807293269163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17076804505450152782051101 6403801689543807293269163)
          ·
            refine ⟨9605702534315710939903745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6403801689543807293269163 9605702534315710939903745)
            ·
              refine ⟨7204276900736783204927809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9605702534315710939903745 7204276900736783204927809)
              ·
                refine ⟨5403207675552587403695857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7204276900736783204927809 5403207675552587403695857)
                ·
                  refine ⟨4052405756664440552771893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5403207675552587403695857 4052405756664440552771893)
                  ·
                    refine ⟨379913039687291301822365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4052405756664440552771893 379913039687291301822365)
                    ·
                      rfl

theorem cell23_2219634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 2, 2, 2, 5].length) (baseStart_2219634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2219634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2219634 prefixEnd_2219634 := by exact prefixLift 2219634
  have htrace : WordTrace (prefixWord ++ tailWord_2219634) baseStart_2219634 baseEnd_2219634 := by
    simpa [prefixWord, tailWord_2219634, baseEnd_2219634] using wordTrace_append hprefix tailTrace_2219634
  have hstable : (prefixWord ++ tailWord_2219634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2219634).length < 2 ^ (prefixWord ++ tailWord_2219634).sum := by decide
  have hdescent : baseEnd_2219634 < baseStart_2219634 := by decide
  rcases family_descends (prefixWord ++ tailWord_2219634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2219638 : List Nat := [5, 1, 1, 2, 2, 1, 4, 2, 5]
def baseStart_2219638 : Nat := 118140960795 + 2219638 * 2 ^ 59
def prefixEnd_2219638 : Nat := 4983230072969 + 3 ^ 40 * 2219638 * 2
def baseEnd_2219638 : Nat := 126637908109387987757453

theorem tailTrace_2219638 : CollatzResearch.WordTrace tailWord_2219638 prefixEnd_2219638 126637908109387987757453 := by
  unfold tailWord_2219638
  simp only [CollatzResearch.WordTrace]
  refine ⟨5059803045789880302193223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 53971232488425389890061045 5059803045789880302193223)
  ·
    refine ⟨7589704568684820453289835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5059803045789880302193223 7589704568684820453289835)
    ·
      refine ⟨11384556853027230679934753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7589704568684820453289835 11384556853027230679934753)
      ·
        refine ⟨8538417639770423009951065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11384556853027230679934753 8538417639770423009951065)
        ·
          refine ⟨6403813229827817257463299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8538417639770423009951065 6403813229827817257463299)
          ·
            refine ⟨9605719844741725886194949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6403813229827817257463299 9605719844741725886194949)
            ·
              refine ⟨1801072470889073603661553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9605719844741725886194949 1801072470889073603661553)
              ·
                refine ⟨1350804353166805202746165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1801072470889073603661553 1350804353166805202746165)
                ·
                  refine ⟨126637908109387987757453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1350804353166805202746165 126637908109387987757453)
                  ·
                    rfl

theorem cell23_2219638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 4, 2, 5].length) (baseStart_2219638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2219638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2219638 prefixEnd_2219638 := by exact prefixLift 2219638
  have htrace : WordTrace (prefixWord ++ tailWord_2219638) baseStart_2219638 baseEnd_2219638 := by
    simpa [prefixWord, tailWord_2219638, baseEnd_2219638] using wordTrace_append hprefix tailTrace_2219638
  have hstable : (prefixWord ++ tailWord_2219638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2219638).length < 2 ^ (prefixWord ++ tailWord_2219638).sum := by decide
  have hdescent : baseEnd_2219638 < baseStart_2219638 := by decide
  rcases family_descends (prefixWord ++ tailWord_2219638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2219668 : List Nat := [2, 4, 2, 2, 2, 2, 1, 1, 2, 5]
def baseStart_2219668 : Nat := 118140960795 + 2219668 * 2 ^ 59
def prefixEnd_2219668 : Nat := 4983230072969 + 3 ^ 40 * 2219668 * 2
def baseEnd_2219668 : Nat := 379918859134708924147313

theorem tailTrace_2219668 : CollatzResearch.WordTrace tailWord_2219668 prefixEnd_2219668 379918859134708924147313 := by
  unfold tailWord_2219668
  simp only [CollatzResearch.WordTrace]
  refine ⟨40478971461264699979341829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53971961948352933305789105 40478971461264699979341829)
  ·
    refine ⟨7589807148987131246126593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 40478971461264699979341829 7589807148987131246126593)
    ·
      refine ⟨5692355361740348434594945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7589807148987131246126593 5692355361740348434594945)
      ·
        refine ⟨4269266521305261325946209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5692355361740348434594945 4269266521305261325946209)
        ·
          refine ⟨3201949890978945994459657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4269266521305261325946209 3201949890978945994459657)
          ·
            refine ⟨2401462418234209495844743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3201949890978945994459657 2401462418234209495844743)
            ·
              refine ⟨3602193627351314243767115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2401462418234209495844743 3602193627351314243767115)
              ·
                refine ⟨5403290441026971365650673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3602193627351314243767115 5403290441026971365650673)
                ·
                  refine ⟨4052467830770228524238005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5403290441026971365650673 4052467830770228524238005)
                  ·
                    refine ⟨379918859134708924147313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4052467830770228524238005 379918859134708924147313)
                    ·
                      rfl

theorem cell23_2219668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 2, 1, 1, 2, 5].length) (baseStart_2219668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2219668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2219668 prefixEnd_2219668 := by exact prefixLift 2219668
  have htrace : WordTrace (prefixWord ++ tailWord_2219668) baseStart_2219668 baseEnd_2219668 := by
    simpa [prefixWord, tailWord_2219668, baseEnd_2219668] using wordTrace_append hprefix tailTrace_2219668
  have hstable : (prefixWord ++ tailWord_2219668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2219668).length < 2 ^ (prefixWord ++ tailWord_2219668).sum := by decide
  have hdescent : baseEnd_2219668 < baseStart_2219668 := by decide
  rcases family_descends (prefixWord ++ tailWord_2219668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2219671 : List Nat := [1, 1, 3, 3, 2, 4, 1, 1, 2, 1, 4]
def baseStart_2219671 : Nat := 118140960795 + 2219671 * 2 ^ 59
def prefixEnd_2219671 : Nat := 4983230072969 + 3 ^ 40 * 2219671 * 2
def baseEnd_2219671 : Nat := 1139758117846090260704425

theorem tailTrace_2219671 : CollatzResearch.WordTrace tailWord_2219671 prefixEnd_2219671 1139758117846090260704425 := by
  unfold tailWord_2219671
  simp only [CollatzResearch.WordTrace]
  refine ⟨80958052341518531471042867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53972034894345687647361911 80958052341518531471042867)
  ·
    refine ⟨121437078512277797206564301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80958052341518531471042867 121437078512277797206564301)
    ·
      refine ⟨45538904442104173952461613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 121437078512277797206564301 45538904442104173952461613)
      ·
        refine ⟨17077089165789065232173105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45538904442104173952461613 17077089165789065232173105)
        ·
          refine ⟨12807816874341798924129829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17077089165789065232173105 12807816874341798924129829)
          ·
            refine ⟨2401465663939087298274343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12807816874341798924129829 2401465663939087298274343)
            ·
              refine ⟨3602198495908630947411515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2401465663939087298274343 3602198495908630947411515)
              ·
                refine ⟨5403297743862946421117273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3602198495908630947411515 5403297743862946421117273)
                ·
                  refine ⟨4052473307897209815837955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5403297743862946421117273 4052473307897209815837955)
                  ·
                    refine ⟨6078709961845814723756933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4052473307897209815837955 6078709961845814723756933)
                    ·
                      refine ⟨1139758117846090260704425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6078709961845814723756933 1139758117846090260704425)
                      ·
                        rfl

theorem cell23_2219671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 4, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 4, 1, 1, 2, 1, 4].length) (baseStart_2219671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2219671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2219671 prefixEnd_2219671 := by exact prefixLift 2219671
  have htrace : WordTrace (prefixWord ++ tailWord_2219671) baseStart_2219671 baseEnd_2219671 := by
    simpa [prefixWord, tailWord_2219671, baseEnd_2219671] using wordTrace_append hprefix tailTrace_2219671
  have hstable : (prefixWord ++ tailWord_2219671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2219671).length < 2 ^ (prefixWord ++ tailWord_2219671).sum := by decide
  have hdescent : baseEnd_2219671 < baseStart_2219671 := by decide
  rcases family_descends (prefixWord ++ tailWord_2219671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2219677 : List Nat := [1, 4, 2, 1, 1, 1, 1, 4, 8]
def baseStart_2219677 : Nat := 118140960795 + 2219677 * 2 ^ 59
def prefixEnd_2219677 : Nat := 4983230072969 + 3 ^ 40 * 2219677 * 2
def baseEnd_2219677 : Nat := 126640133192224137469933

theorem tailTrace_2219677 : CollatzResearch.WordTrace tailWord_2219677 prefixEnd_2219677 126640133192224137469933 := by
  unfold tailWord_2219677
  simp only [CollatzResearch.WordTrace]
  refine ⟨80958271179496794495761285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53972180786331196330507523 80958271179496794495761285)
  ·
    refine ⟨15179675846155648967955241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 80958271179496794495761285 15179675846155648967955241)
    ·
      refine ⟨11384756884616736725966431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15179675846155648967955241 11384756884616736725966431)
      ·
        refine ⟨17077135326925105088949647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11384756884616736725966431 17077135326925105088949647)
        ·
          refine ⟨25615702990387657633424471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17077135326925105088949647 25615702990387657633424471)
          ·
            refine ⟨38423554485581486450136707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25615702990387657633424471 38423554485581486450136707)
            ·
              refine ⟨57635331728372229675205061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38423554485581486450136707 57635331728372229675205061)
              ·
                refine ⟨10806624699069793064100949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 57635331728372229675205061 10806624699069793064100949)
                ·
                  refine ⟨126640133192224137469933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 10806624699069793064100949 126640133192224137469933)
                  ·
                    rfl

theorem cell23_2219677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 4, 8].length) (baseStart_2219677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2219677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2219677 prefixEnd_2219677 := by exact prefixLift 2219677
  have htrace : WordTrace (prefixWord ++ tailWord_2219677) baseStart_2219677 baseEnd_2219677 := by
    simpa [prefixWord, tailWord_2219677, baseEnd_2219677] using wordTrace_append hprefix tailTrace_2219677
  have hstable : (prefixWord ++ tailWord_2219677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2219677).length < 2 ^ (prefixWord ++ tailWord_2219677).sum := by decide
  have hdescent : baseEnd_2219677 < baseStart_2219677 := by decide
  rcases family_descends (prefixWord ++ tailWord_2219677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2219707 : List Nat := [1, 1, 1, 1, 1, 2, 3, 3, 5, 5]
def baseStart_2219707 : Nat := 118140960795 + 2219707 * 2 ^ 59
def prefixEnd_2219707 : Nat := 4983230072969 + 3 ^ 40 * 2219707 * 2
def baseEnd_2219707 : Nat := 379925534383217373284753

theorem tailTrace_2219707 : CollatzResearch.WordTrace tailWord_2219707 prefixEnd_2219707 379925534383217373284753 := by
  unfold tailWord_2219707
  simp only [CollatzResearch.WordTrace]
  refine ⟨80959365369388109619353375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53972910246258739746235583 80959365369388109619353375)
  ·
    refine ⟨121439048054082164429030063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80959365369388109619353375 121439048054082164429030063)
    ·
      refine ⟨182158572081123246643545095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121439048054082164429030063 182158572081123246643545095)
      ·
        refine ⟨273237858121684869965317643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 182158572081123246643545095 273237858121684869965317643)
        ·
          refine ⟨409856787182527304947976465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 273237858121684869965317643 409856787182527304947976465)
          ·
            refine ⟨307392590386895478710982349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 409856787182527304947976465 307392590386895478710982349)
            ·
              refine ⟨115272221395085804516618381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 307392590386895478710982349 115272221395085804516618381)
              ·
                refine ⟨43227083023157176693731893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 115272221395085804516618381 43227083023157176693731893)
                ·
                  refine ⟨4052539033420985315037365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 43227083023157176693731893 4052539033420985315037365)
                  ·
                    refine ⟨379925534383217373284753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4052539033420985315037365 379925534383217373284753)
                    ·
                      rfl

theorem cell23_2219707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 3, 5, 5].length) (baseStart_2219707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2219707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2219707 prefixEnd_2219707 := by exact prefixLift 2219707
  have htrace : WordTrace (prefixWord ++ tailWord_2219707) baseStart_2219707 baseEnd_2219707 := by
    simpa [prefixWord, tailWord_2219707, baseEnd_2219707] using wordTrace_append hprefix tailTrace_2219707
  have hstable : (prefixWord ++ tailWord_2219707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2219707).length < 2 ^ (prefixWord ++ tailWord_2219707).sum := by decide
  have hdescent : baseEnd_2219707 < baseStart_2219707 := by decide
  rcases family_descends (prefixWord ++ tailWord_2219707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2219727 : List Nat := [1, 1, 2, 1, 1, 3, 1, 2, 2, 5, 4]
def baseStart_2219727 : Nat := 118140960795 + 2219727 * 2 ^ 59
def prefixEnd_2219727 : Nat := 4983230072969 + 3 ^ 40 * 2219727 * 2
def baseEnd_2219727 : Nat := 1139786872762742041604167

theorem tailTrace_2219727 : CollatzResearch.WordTrace tailWord_2219727 prefixEnd_2219727 1139786872762742041604167 := by
  unfold tailWord_2219727
  simp only [CollatzResearch.WordTrace]
  refine ⟨80960094829315653035081435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53973396552877102023387623 80960094829315653035081435)
  ·
    refine ⟨121440142243973479552622153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80960094829315653035081435 121440142243973479552622153)
    ·
      refine ⟨91080106682980109664466615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 121440142243973479552622153 91080106682980109664466615)
      ·
        refine ⟨136620160024470164496699923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91080106682980109664466615 136620160024470164496699923)
        ·
          refine ⟨204930240036705246745049885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 136620160024470164496699923 204930240036705246745049885)
          ·
            refine ⟨76848840013764467529393707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 204930240036705246745049885 76848840013764467529393707)
            ·
              refine ⟨115273260020646701294090561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 76848840013764467529393707 115273260020646701294090561)
              ·
                refine ⟨86454945015485025970567921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 115273260020646701294090561 86454945015485025970567921)
                ·
                  refine ⟨64841208761613769477925941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 86454945015485025970567921 64841208761613769477925941)
                  ·
                    refine ⟨6078863321401290888555557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 64841208761613769477925941 6078863321401290888555557)
                    ·
                      refine ⟨1139786872762742041604167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6078863321401290888555557 1139786872762742041604167)
                      ·
                        rfl

theorem cell23_2219727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 2, 2, 5, 4].length) (baseStart_2219727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2219727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2219727 prefixEnd_2219727 := by exact prefixLift 2219727
  have htrace : WordTrace (prefixWord ++ tailWord_2219727) baseStart_2219727 baseEnd_2219727 := by
    simpa [prefixWord, tailWord_2219727, baseEnd_2219727] using wordTrace_append hprefix tailTrace_2219727
  have hstable : (prefixWord ++ tailWord_2219727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2219727).length < 2 ^ (prefixWord ++ tailWord_2219727).sum := by decide
  have hdescent : baseEnd_2219727 < baseStart_2219727 := by decide
  rcases family_descends (prefixWord ++ tailWord_2219727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2219767 : List Nat := [1, 1, 3, 1, 1, 1, 5, 10]
def baseStart_2219767 : Nat := 118140960795 + 2219767 * 2 ^ 59
def prefixEnd_2219767 : Nat := 4983230072969 + 3 ^ 40 * 2219767 * 2
def baseEnd_2219767 : Nat := 42215089332923032781629

theorem tailTrace_2219767 : CollatzResearch.WordTrace tailWord_2219767 prefixEnd_2219767 42215089332923032781629 := by
  unfold tailWord_2219767
  simp only [CollatzResearch.WordTrace]
  refine ⟨80961553749170739866537555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53974369166113826577691703 80961553749170739866537555)
  ·
    refine ⟨121442330623756109799806333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80961553749170739866537555 121442330623756109799806333)
    ·
      refine ⟨45540873983908541174927375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 121442330623756109799806333 45540873983908541174927375)
      ·
        refine ⟨68311310975862811762391063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45540873983908541174927375 68311310975862811762391063)
        ·
          refine ⟨102466966463794217643586595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68311310975862811762391063 102466966463794217643586595)
          ·
            refine ⟨153700449695691326465379893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 102466966463794217643586595 153700449695691326465379893)
            ·
              refine ⟨14409417158971061856129365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 153700449695691326465379893 14409417158971061856129365)
              ·
                refine ⟨42215089332923032781629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 14409417158971061856129365 42215089332923032781629)
                ·
                  rfl

theorem cell23_2219767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 5, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 5, 10].length) (baseStart_2219767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2219767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2219767 prefixEnd_2219767 := by exact prefixLift 2219767
  have htrace : WordTrace (prefixWord ++ tailWord_2219767) baseStart_2219767 baseEnd_2219767 := by
    simpa [prefixWord, tailWord_2219767, baseEnd_2219767] using wordTrace_append hprefix tailTrace_2219767
  have hstable : (prefixWord ++ tailWord_2219767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2219767).length < 2 ^ (prefixWord ++ tailWord_2219767).sum := by decide
  have hdescent : baseEnd_2219767 < baseStart_2219767 := by decide
  rcases family_descends (prefixWord ++ tailWord_2219767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2219811 : List Nat := [1, 1, 1, 4, 2, 1, 2, 3, 4, 1, 3]
def baseStart_2219811 : Nat := 118140960795 + 2219811 * 2 ^ 59
def prefixEnd_2219811 : Nat := 4983230072969 + 3 ^ 40 * 2219811 * 2
def baseEnd_2219811 : Nat := 1139830005137719712953781

theorem tailTrace_2219811 : CollatzResearch.WordTrace tailWord_2219811 prefixEnd_2219811 1139830005137719712953781 := by
  unfold tailWord_2219811
  simp only [CollatzResearch.WordTrace]
  refine ⟨80963158561011335381139287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53975439040674223587426191 80963158561011335381139287)
  ·
    refine ⟨121444737841517003071708931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80963158561011335381139287 121444737841517003071708931)
    ·
      refine ⟨182167106762275504607563397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121444737841517003071708931 182167106762275504607563397)
      ·
        refine ⟨34156332517926657113918137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 182167106762275504607563397 34156332517926657113918137)
        ·
          refine ⟨25617249388444992835438603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34156332517926657113918137 25617249388444992835438603)
          ·
            refine ⟨38425874082667489253157905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25617249388444992835438603 38425874082667489253157905)
            ·
              refine ⟨28819405562000616939868429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38425874082667489253157905 28819405562000616939868429)
              ·
                refine ⟨10807277085750231352450661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28819405562000616939868429 10807277085750231352450661)
                ·
                  refine ⟨2026364453578168378584499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10807277085750231352450661 2026364453578168378584499)
                  ·
                    refine ⟨3039546680367252567876749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2026364453578168378584499 3039546680367252567876749)
                    ·
                      refine ⟨1139830005137719712953781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3039546680367252567876749 1139830005137719712953781)
                      ·
                        rfl

theorem cell23_2219811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 3, 4, 1, 3].length) (baseStart_2219811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2219811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2219811 prefixEnd_2219811 := by exact prefixLift 2219811
  have htrace : WordTrace (prefixWord ++ tailWord_2219811) baseStart_2219811 baseEnd_2219811 := by
    simpa [prefixWord, tailWord_2219811, baseEnd_2219811] using wordTrace_append hprefix tailTrace_2219811
  have hstable : (prefixWord ++ tailWord_2219811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2219811).length < 2 ^ (prefixWord ++ tailWord_2219811).sum := by decide
  have hdescent : baseEnd_2219811 < baseStart_2219811 := by decide
  rcases family_descends (prefixWord ++ tailWord_2219811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2219812 : List Nat := [2, 3, 1, 3, 2, 2, 1, 4, 1, 2, 2]
def baseStart_2219812 : Nat := 118140960795 + 2219812 * 2 ^ 59
def prefixEnd_2219812 : Nat := 4983230072969 + 3 ^ 40 * 2219812 * 2
def baseEnd_2219812 : Nat := 1139830518618374209041277

theorem tailTrace_2219812 : CollatzResearch.WordTrace tailWord_2219812 prefixEnd_2219812 1139830518618374209041277 := by
  unfold tailWord_2219812
  simp only [CollatzResearch.WordTrace]
  refine ⟨40481597517003856275962845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53975463356005141701283793 40481597517003856275962845)
  ·
    refine ⟨15180599068876446103486067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40481597517003856275962845 15180599068876446103486067)
    ·
      refine ⟨22770898603314669155229101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15180599068876446103486067 22770898603314669155229101)
      ·
        refine ⟨8539086976243000933210913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22770898603314669155229101 8539086976243000933210913)
        ·
          refine ⟨6404315232182250699908185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8539086976243000933210913 6404315232182250699908185)
          ·
            refine ⟨4803236424136688024931139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6404315232182250699908185 4803236424136688024931139)
            ·
              refine ⟨7204854636205032037396709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4803236424136688024931139 7204854636205032037396709)
              ·
                refine ⟨1350910244288443507011883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7204854636205032037396709 1350910244288443507011883)
                ·
                  refine ⟨2026365366432665260517825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1350910244288443507011883 2026365366432665260517825)
                  ·
                    refine ⟨1519774024824498945388369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2026365366432665260517825 1519774024824498945388369)
                    ·
                      refine ⟨1139830518618374209041277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1519774024824498945388369 1139830518618374209041277)
                      ·
                        rfl

theorem cell23_2219812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 1, 4, 1, 2, 2].length) (baseStart_2219812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2219812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2219812 prefixEnd_2219812 := by exact prefixLift 2219812
  have htrace : WordTrace (prefixWord ++ tailWord_2219812) baseStart_2219812 baseEnd_2219812 := by
    simpa [prefixWord, tailWord_2219812, baseEnd_2219812] using wordTrace_append hprefix tailTrace_2219812
  have hstable : (prefixWord ++ tailWord_2219812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2219812).length < 2 ^ (prefixWord ++ tailWord_2219812).sum := by decide
  have hdescent : baseEnd_2219812 < baseStart_2219812 := by decide
  rcases family_descends (prefixWord ++ tailWord_2219812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2219828 : List Nat := [2, 5, 1, 1, 2, 1, 1, 3, 1, 3, 3]
def baseStart_2219828 : Nat := 118140960795 + 2219828 * 2 ^ 59
def prefixEnd_2219828 : Nat := 4983230072969 + 3 ^ 40 * 2219828 * 2
def baseEnd_2219828 : Nat := 1139838734308846146441203

theorem tailTrace_2219828 : CollatzResearch.WordTrace tailWord_2219828 prefixEnd_2219828 1139838734308846146441203 := by
  unfold tailWord_2219828
  simp only [CollatzResearch.WordTrace]
  refine ⟨40481889300974873642254069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53975852401299831523005425 40481889300974873642254069)
  ·
    refine ⟨3795177121966394403961319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 40481889300974873642254069 3795177121966394403961319)
    ·
      refine ⟨5692765682949591605941979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3795177121966394403961319 5692765682949591605941979)
      ·
        refine ⟨8539148524424387408912969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5692765682949591605941979 8539148524424387408912969)
        ·
          refine ⟨6404361393318290556684727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8539148524424387408912969 6404361393318290556684727)
          ·
            refine ⟨9606542089977435835027091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6404361393318290556684727 9606542089977435835027091)
            ·
              refine ⟨14409813134966153752540637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9606542089977435835027091 14409813134966153752540637)
              ·
                refine ⟨5403679925612307657202739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14409813134966153752540637 5403679925612307657202739)
                ·
                  refine ⟨8105519888418461485804109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5403679925612307657202739 8105519888418461485804109)
                  ·
                    refine ⟨3039569958156923057176541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8105519888418461485804109 3039569958156923057176541)
                    ·
                      refine ⟨1139838734308846146441203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3039569958156923057176541 1139838734308846146441203)
                      ·
                        rfl

theorem cell23_2219828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 1, 3, 1, 3, 3].length) (baseStart_2219828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2219828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2219828 prefixEnd_2219828 := by exact prefixLift 2219828
  have htrace : WordTrace (prefixWord ++ tailWord_2219828) baseStart_2219828 baseEnd_2219828 := by
    simpa [prefixWord, tailWord_2219828, baseEnd_2219828] using wordTrace_append hprefix tailTrace_2219828
  have hstable : (prefixWord ++ tailWord_2219828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2219828).length < 2 ^ (prefixWord ++ tailWord_2219828).sum := by decide
  have hdescent : baseEnd_2219828 < baseStart_2219828 := by decide
  rcases family_descends (prefixWord ++ tailWord_2219828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2219846 : List Nat := [6, 1, 1, 2, 1, 2, 2, 3, 1, 2, 2]
def baseStart_2219846 : Nat := 118140960795 + 2219846 * 2 ^ 59
def prefixEnd_2219846 : Nat := 4983230072969 + 3 ^ 40 * 2219846 * 2
def baseEnd_2219846 : Nat := 1139847976960627076016121

theorem tailTrace_2219846 : CollatzResearch.WordTrace tailWord_2219846 prefixEnd_2219846 1139847976960627076016121 := by
  unfold tailWord_2219846
  simp only [CollatzResearch.WordTrace]
  refine ⟨2530138597371391761208231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 53976290077256357572442261 2530138597371391761208231)
  ·
    refine ⟨3795207896057087641812347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2530138597371391761208231 3795207896057087641812347)
    ·
      refine ⟨5692811844085631462718521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3795207896057087641812347 5692811844085631462718521)
      ·
        refine ⟨4269608883064223597038891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5692811844085631462718521 4269608883064223597038891)
        ·
          refine ⟨6404413324596335395558337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4269608883064223597038891 6404413324596335395558337)
          ·
            refine ⟨4803309993447251546668753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6404413324596335395558337 4803309993447251546668753)
            ·
              refine ⟨3602482495085438660001565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4803309993447251546668753 3602482495085438660001565)
              ·
                refine ⟨1350930935657039497500587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3602482495085438660001565 1350930935657039497500587)
                ·
                  refine ⟨2026396403485559246250881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1350930935657039497500587 2026396403485559246250881)
                  ·
                    refine ⟨1519797302614169434688161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2026396403485559246250881 1519797302614169434688161)
                    ·
                      refine ⟨1139847976960627076016121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1519797302614169434688161 1139847976960627076016121)
                      ·
                        rfl

theorem cell23_2219846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 2, 3, 1, 2, 2].length) (baseStart_2219846 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2219846 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2219846 prefixEnd_2219846 := by exact prefixLift 2219846
  have htrace : WordTrace (prefixWord ++ tailWord_2219846) baseStart_2219846 baseEnd_2219846 := by
    simpa [prefixWord, tailWord_2219846, baseEnd_2219846] using wordTrace_append hprefix tailTrace_2219846
  have hstable : (prefixWord ++ tailWord_2219846).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2219846).length < 2 ^ (prefixWord ++ tailWord_2219846).sum := by decide
  have hdescent : baseEnd_2219846 < baseStart_2219846 := by decide
  rcases family_descends (prefixWord ++ tailWord_2219846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2219885 : List Nat := [1, 5, 1, 1, 1, 1, 2, 5, 2, 2, 2]
def baseStart_2219885 : Nat := 118140960795 + 2219885 * 2 ^ 59
def prefixEnd_2219885 : Nat := 4983230072969 + 3 ^ 40 * 2219885 * 2
def baseEnd_2219885 : Nat := 1139868002706152423428441

theorem tailTrace_2219885 : CollatzResearch.WordTrace tailWord_2219885 prefixEnd_2219885 1139868002706152423428441 := by
  unfold tailWord_2219885
  simp only [CollatzResearch.WordTrace]
  refine ⟨80965857562743246019333109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53977238375162164012888739 80965857562743246019333109)
  ·
    refine ⟨7590549146507179314312479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 80965857562743246019333109 7590549146507179314312479)
    ·
      refine ⟨11385823719760768971468719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7590549146507179314312479 11385823719760768971468719)
      ·
        refine ⟨17078735579641153457203079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11385823719760768971468719 17078735579641153457203079)
        ·
          refine ⟨25618103369461730185804619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17078735579641153457203079 25618103369461730185804619)
          ·
            refine ⟨38427155054192595278706929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25618103369461730185804619 38427155054192595278706929)
            ·
              refine ⟨28820366290644446459030197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38427155054192595278706929 28820366290644446459030197)
              ·
                refine ⟨2701909339747916855534081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 28820366290644446459030197 2701909339747916855534081)
                ·
                  refine ⟨2026432004810937641650561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2701909339747916855534081 2026432004810937641650561)
                  ·
                    refine ⟨1519824003608203231237921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2026432004810937641650561 1519824003608203231237921)
                    ·
                      refine ⟨1139868002706152423428441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1519824003608203231237921 1139868002706152423428441)
                      ·
                        rfl

theorem cell23_2219885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 5, 2, 2, 2].length) (baseStart_2219885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2219885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2219885 prefixEnd_2219885 := by exact prefixLift 2219885
  have htrace : WordTrace (prefixWord ++ tailWord_2219885) baseStart_2219885 baseEnd_2219885 := by
    simpa [prefixWord, tailWord_2219885, baseEnd_2219885] using wordTrace_append hprefix tailTrace_2219885
  have hstable : (prefixWord ++ tailWord_2219885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2219885).length < 2 ^ (prefixWord ++ tailWord_2219885).sum := by decide
  have hdescent : baseEnd_2219885 < baseStart_2219885 := by decide
  rcases family_descends (prefixWord ++ tailWord_2219885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2219902 : List Nat := [4, 2, 3, 1, 1, 1, 1, 2, 4, 2, 2]
def baseStart_2219902 : Nat := 118140960795 + 2219902 * 2 ^ 59
def prefixEnd_2219902 : Nat := 4983230072969 + 3 ^ 40 * 2219902 * 2
def baseEnd_2219902 : Nat := 1139876731877278856915863

theorem tailTrace_2219902 : CollatzResearch.WordTrace tailWord_2219902 prefixEnd_2219902 1139876731877278856915863 := by
  unfold tailWord_2219902
  simp only [CollatzResearch.WordTrace]
  refine ⟨10120809700460207240337745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 53977651735787771948467973 10120809700460207240337745)
  ·
    refine ⟨7590607275345155430253309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10120809700460207240337745 7590607275345155430253309)
    ·
      refine ⟨2846477728254433286344991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7590607275345155430253309 2846477728254433286344991)
      ·
        refine ⟨4269716592381649929517487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2846477728254433286344991 4269716592381649929517487)
        ·
          refine ⟨6404574888572474894276231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4269716592381649929517487 6404574888572474894276231)
          ·
            refine ⟨9606862332858712341414347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6404574888572474894276231 9606862332858712341414347)
            ·
              refine ⟨14410293499288068512121521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9606862332858712341414347 14410293499288068512121521)
              ·
                refine ⟨10807720124466051384091141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14410293499288068512121521 10807720124466051384091141)
                ·
                  refine ⟨2026447523337384634517089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10807720124466051384091141 2026447523337384634517089)
                  ·
                    refine ⟨1519835642503038475887817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2026447523337384634517089 1519835642503038475887817)
                    ·
                      refine ⟨1139876731877278856915863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1519835642503038475887817 1139876731877278856915863)
                      ·
                        rfl

theorem cell23_2219902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 1, 2, 4, 2, 2].length) (baseStart_2219902 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2219902 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2219902 prefixEnd_2219902 := by exact prefixLift 2219902
  have htrace : WordTrace (prefixWord ++ tailWord_2219902) baseStart_2219902 baseEnd_2219902 := by
    simpa [prefixWord, tailWord_2219902, baseEnd_2219902] using wordTrace_append hprefix tailTrace_2219902
  have hstable : (prefixWord ++ tailWord_2219902).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2219902).length < 2 ^ (prefixWord ++ tailWord_2219902).sum := by decide
  have hdescent : baseEnd_2219902 < baseStart_2219902 := by decide
  rcases family_descends (prefixWord ++ tailWord_2219902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2219904 : List Nat := [2, 1, 1, 2, 1, 2, 3, 3, 1, 7]
def baseStart_2219904 : Nat := 118140960795 + 2219904 * 2 ^ 59
def prefixEnd_2219904 : Nat := 4983230072969 + 3 ^ 40 * 2219904 * 2
def baseEnd_2219904 : Nat := 379959252946195949696951

theorem tailTrace_2219904 : CollatzResearch.WordTrace tailWord_2219904 prefixEnd_2219904 379959252946195949696951 := by
  unfold tailWord_2219904
  simp only [CollatzResearch.WordTrace]
  refine ⟨40483275274837206132137383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53977700366449608176183177 40483275274837206132137383)
  ·
    refine ⟨60724912912255809198206075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40483275274837206132137383 60724912912255809198206075)
    ·
      refine ⟨91087369368383713797309113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60724912912255809198206075 91087369368383713797309113)
      ·
        refine ⟨68315527026287785347981835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 91087369368383713797309113 68315527026287785347981835)
        ·
          refine ⟨102473290539431678021972753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68315527026287785347981835 102473290539431678021972753)
          ·
            refine ⟨76854967904573758516479565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 102473290539431678021972753 76854967904573758516479565)
            ·
              refine ⟨28820612964215159443679837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 76854967904573758516479565 28820612964215159443679837)
              ·
                refine ⟨10807729861580684791379939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28820612964215159443679837 10807729861580684791379939)
                ·
                  refine ⟨16211594792371027187069909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10807729861580684791379939 16211594792371027187069909)
                  ·
                    refine ⟨379959252946195949696951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 16211594792371027187069909 379959252946195949696951)
                    ·
                      rfl

theorem cell23_2219904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 3, 1, 7].length) (baseStart_2219904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2219904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2219904 prefixEnd_2219904 := by exact prefixLift 2219904
  have htrace : WordTrace (prefixWord ++ tailWord_2219904) baseStart_2219904 baseEnd_2219904 := by
    simpa [prefixWord, tailWord_2219904, baseEnd_2219904] using wordTrace_append hprefix tailTrace_2219904
  have hstable : (prefixWord ++ tailWord_2219904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2219904).length < 2 ^ (prefixWord ++ tailWord_2219904).sum := by decide
  have hdescent : baseEnd_2219904 < baseStart_2219904 := by decide
  rcases family_descends (prefixWord ++ tailWord_2219904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2219908 : List Nat := [2, 3, 2, 1, 1, 1, 5, 3, 5]
def baseStart_2219908 : Nat := 118140960795 + 2219908 * 2 ^ 59
def prefixEnd_2219908 : Nat := 4983230072969 + 3 ^ 40 * 2219908 * 2
def baseEnd_2219908 : Nat := 126653312529022870382315

theorem tailTrace_2219908 : CollatzResearch.WordTrace tailWord_2219908 prefixEnd_2219908 126653312529022870382315 := by
  unfold tailWord_2219908
  simp only [CollatzResearch.WordTrace]
  refine ⟨40483348220829960473710189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53977797627773280631613585 40483348220829960473710189)
  ·
    refine ⟨15181255582811235177641321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40483348220829960473710189 15181255582811235177641321)
    ·
      refine ⟨11385941687108426383230991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15181255582811235177641321 11385941687108426383230991)
      ·
        refine ⟨17078912530662639574846487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11385941687108426383230991 17078912530662639574846487)
        ·
          refine ⟨25618368795993959362269731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17078912530662639574846487 25618368795993959362269731)
          ·
            refine ⟨38427553193990939043404597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25618368795993959362269731 38427553193990939043404597)
            ·
              refine ⟨3602583111936650535319181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 38427553193990939043404597 3602583111936650535319181)
              ·
                refine ⟨1350968666976243950744693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3602583111936650535319181 1350968666976243950744693)
                ·
                  refine ⟨126653312529022870382315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1350968666976243950744693 126653312529022870382315)
                  ·
                    rfl

theorem cell23_2219908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 5, 3, 5].length) (baseStart_2219908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2219908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2219908 prefixEnd_2219908 := by exact prefixLift 2219908
  have htrace : WordTrace (prefixWord ++ tailWord_2219908) baseStart_2219908 baseEnd_2219908 := by
    simpa [prefixWord, tailWord_2219908, baseEnd_2219908] using wordTrace_append hprefix tailTrace_2219908
  have hstable : (prefixWord ++ tailWord_2219908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2219908).length < 2 ^ (prefixWord ++ tailWord_2219908).sum := by decide
  have hdescent : baseEnd_2219908 < baseStart_2219908 := by decide
  rcases family_descends (prefixWord ++ tailWord_2219908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2219951 : List Nat := [1, 1, 2, 1, 2, 2, 4, 1, 5, 4]
def baseStart_2219951 : Nat := 118140960795 + 2219951 * 2 ^ 59
def prefixEnd_2219951 : Nat := 4983230072969 + 3 ^ 40 * 2219951 * 2
def baseEnd_2219951 : Nat := 379967297476449721734379

theorem tailTrace_2219951 : CollatzResearch.WordTrace tailWord_2219951 prefixEnd_2219951 379967297476449721734379 := by
  unfold tailWord_2219951
  simp only [CollatzResearch.WordTrace]
  refine ⟨80968264780504139291235707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53978843187002759527490471 80968264780504139291235707)
  ·
    refine ⟨121452397170756208936853561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80968264780504139291235707 121452397170756208936853561)
    ·
      refine ⟨91089297878067156702640171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 121452397170756208936853561 91089297878067156702640171)
      ·
        refine ⟨136633946817100735053960257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91089297878067156702640171 136633946817100735053960257)
        ·
          refine ⟨102475460112825551290470193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 136633946817100735053960257 102475460112825551290470193)
          ·
            refine ⟨76856595084619163467852645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 102475460112825551290470193 76856595084619163467852645)
            ·
              refine ⟨14410611578366093150222371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 76856595084619163467852645 14410611578366093150222371)
              ·
                refine ⟨21615917367549139725333557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14410611578366093150222371 21615917367549139725333557)
                ·
                  refine ⟨2026492253207731849250021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 21615917367549139725333557 2026492253207731849250021)
                  ·
                    refine ⟨379967297476449721734379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2026492253207731849250021 379967297476449721734379)
                    ·
                      rfl

theorem cell23_2219951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 4, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 4, 1, 5, 4].length) (baseStart_2219951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2219951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2219951 prefixEnd_2219951 := by exact prefixLift 2219951
  have htrace : WordTrace (prefixWord ++ tailWord_2219951) baseStart_2219951 baseEnd_2219951 := by
    simpa [prefixWord, tailWord_2219951, baseEnd_2219951] using wordTrace_append hprefix tailTrace_2219951
  have hstable : (prefixWord ++ tailWord_2219951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2219951).length < 2 ^ (prefixWord ++ tailWord_2219951).sum := by decide
  have hdescent : baseEnd_2219951 < baseStart_2219951 := by decide
  rcases family_descends (prefixWord ++ tailWord_2219951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2219978 : List Nat := [3, 1, 2, 1, 2, 1, 4, 2, 2, 2, 3]
def baseStart_2219978 : Nat := 118140960795 + 2219978 * 2 ^ 59
def prefixEnd_2219978 : Nat := 4983230072969 + 3 ^ 40 * 2219978 * 2
def baseEnd_2219978 : Nat := 1139915756407020559565513

theorem tailTrace_2219978 : CollatzResearch.WordTrace tailWord_2219978 prefixEnd_2219978 1139915756407020559565513 := by
  unfold tailWord_2219978
  simp only [CollatzResearch.WordTrace]
  refine ⟨20242312387851580725617147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53979499700937548601645725 20242312387851580725617147)
  ·
    refine ⟨30363468581777371088425721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20242312387851580725617147 30363468581777371088425721)
    ·
      refine ⟨22772601436333028316319291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30363468581777371088425721 22772601436333028316319291)
      ·
        refine ⟨34158902154499542474478937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22772601436333028316319291 34158902154499542474478937)
        ·
          refine ⟨25619176615874656855859203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34158902154499542474478937 25619176615874656855859203)
          ·
            refine ⟨38428764923811985283788805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25619176615874656855859203 38428764923811985283788805)
            ·
              refine ⟨7205393423214747240710401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 38428764923811985283788805 7205393423214747240710401)
              ·
                refine ⟨5404045067411060430532801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7205393423214747240710401 5404045067411060430532801)
                ·
                  refine ⟨4053033800558295322899601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5404045067411060430532801 4053033800558295322899601)
                  ·
                    refine ⟨3039775350418721492174701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4053033800558295322899601 3039775350418721492174701)
                    ·
                      refine ⟨1139915756407020559565513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3039775350418721492174701 1139915756407020559565513)
                      ·
                        rfl

theorem cell23_2219978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 4, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 4, 2, 2, 2, 3].length) (baseStart_2219978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2219978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2219978 prefixEnd_2219978 := by exact prefixLift 2219978
  have htrace : WordTrace (prefixWord ++ tailWord_2219978) baseStart_2219978 baseEnd_2219978 := by
    simpa [prefixWord, tailWord_2219978, baseEnd_2219978] using wordTrace_append hprefix tailTrace_2219978
  have hstable : (prefixWord ++ tailWord_2219978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2219978).length < 2 ^ (prefixWord ++ tailWord_2219978).sum := by decide
  have hdescent : baseEnd_2219978 < baseStart_2219978 := by decide
  rcases family_descends (prefixWord ++ tailWord_2219978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2220002 : List Nat := [3, 3, 3, 1, 2, 1, 1, 2, 3, 4]
def baseStart_2220002 : Nat := 118140960795 + 2220002 * 2 ^ 59
def prefixEnd_2220002 : Nat := 4983230072969 + 3 ^ 40 * 2220002 * 2
def baseEnd_2220002 : Nat := 379976026647576155221801

theorem tailTrace_2220002 : CollatzResearch.WordTrace tailWord_2220002 prefixEnd_2220002 379976026647576155221801 := by
  unfold tailWord_2220002
  simp only [CollatzResearch.WordTrace]
  refine ⟨20242531225829843750335565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53980083268879583334228173 20242531225829843750335565)
  ·
    refine ⟨7590949209686191406375837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20242531225829843750335565 7590949209686191406375837)
    ·
      refine ⟨2846605953632321777390939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7590949209686191406375837 2846605953632321777390939)
      ·
        refine ⟨4269908930448482666086409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2846605953632321777390939 4269908930448482666086409)
        ·
          refine ⟨3202431697836361999564807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4269908930448482666086409 3202431697836361999564807)
          ·
            refine ⟨4803647546754542999347211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3202431697836361999564807 4803647546754542999347211)
            ·
              refine ⟨7205471320131814499020817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4803647546754542999347211 7205471320131814499020817)
              ·
                refine ⟨5404103490098860874265613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7205471320131814499020817 5404103490098860874265613)
                ·
                  refine ⟨2026538808787072827849605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5404103490098860874265613 2026538808787072827849605)
                  ·
                    refine ⟨379976026647576155221801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2026538808787072827849605 379976026647576155221801)
                    ·
                      rfl

theorem cell23_2220002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 1, 2, 3, 4].length) (baseStart_2220002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2220002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2220002 prefixEnd_2220002 := by exact prefixLift 2220002
  have htrace : WordTrace (prefixWord ++ tailWord_2220002) baseStart_2220002 baseEnd_2220002 := by
    simpa [prefixWord, tailWord_2220002, baseEnd_2220002] using wordTrace_append hprefix tailTrace_2220002
  have hstable : (prefixWord ++ tailWord_2220002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2220002).length < 2 ^ (prefixWord ++ tailWord_2220002).sum := by decide
  have hdescent : baseEnd_2220002 < baseStart_2220002 := by decide
  rcases family_descends (prefixWord ++ tailWord_2220002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2220028 : List Nat := [2, 2, 2, 1, 2, 2, 3, 3, 1, 5]
def baseStart_2220028 : Nat := 118140960795 + 2220028 * 2 ^ 59
def prefixEnd_2220028 : Nat := 4983230072969 + 3 ^ 40 * 2220028 * 2
def baseEnd_2220028 : Nat := 379980476813248454646761

theorem tailTrace_2220028 : CollatzResearch.WordTrace tailWord_2220028 prefixEnd_2220028 379980476813248454646761 := by
  unfold tailWord_2220028
  simp only [CollatzResearch.WordTrace]
  refine ⟨40485536600612590720894369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53980715467483454294525825 40485536600612590720894369)
  ·
    refine ⟨30364152450459443040670777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40485536600612590720894369 30364152450459443040670777)
    ·
      refine ⟨22773114337844582280503083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30364152450459443040670777 22773114337844582280503083)
      ·
        refine ⟨34159671506766873420754625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22773114337844582280503083 34159671506766873420754625)
        ·
          refine ⟨25619753630075155065565969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34159671506766873420754625 25619753630075155065565969)
          ·
            refine ⟨19214815222556366299174477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25619753630075155065565969 19214815222556366299174477)
            ·
              refine ⟨7205555708458637362190429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19214815222556366299174477 7205555708458637362190429)
              ·
                refine ⟨2702083390671989010821411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7205555708458637362190429 2702083390671989010821411)
                ·
                  refine ⟨4053125086007983516232117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2702083390671989010821411 4053125086007983516232117)
                  ·
                    refine ⟨379980476813248454646761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4053125086007983516232117 379980476813248454646761)
                    ·
                      rfl

theorem cell23_2220028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 3, 3, 1, 5].length) (baseStart_2220028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2220028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2220028 prefixEnd_2220028 := by exact prefixLift 2220028
  have htrace : WordTrace (prefixWord ++ tailWord_2220028) baseStart_2220028 baseEnd_2220028 := by
    simpa [prefixWord, tailWord_2220028, baseEnd_2220028] using wordTrace_append hprefix tailTrace_2220028
  have hstable : (prefixWord ++ tailWord_2220028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2220028).length < 2 ^ (prefixWord ++ tailWord_2220028).sum := by decide
  have hdescent : baseEnd_2220028 < baseStart_2220028 := by decide
  rcases family_descends (prefixWord ++ tailWord_2220028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2220042 : List Nat := [3, 1, 2, 2, 4, 1, 2, 1, 3, 1, 3]
def baseStart_2220042 : Nat := 118140960795 + 2220042 * 2 ^ 59
def prefixEnd_2220042 : Nat := 4983230072969 + 3 ^ 40 * 2220042 * 2
def baseEnd_2220042 : Nat := 1139948619168908309165219

theorem tailTrace_2220042 : CollatzResearch.WordTrace tailWord_2220042 prefixEnd_2220042 1139948619168908309165219 := by
  unfold tailWord_2220042
  simp only [CollatzResearch.WordTrace]
  refine ⟨20242895955793615458199595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53981055882116307888532253 20242895955793615458199595)
  ·
    refine ⟨30364343933690423187299393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20242895955793615458199595 30364343933690423187299393)
    ·
      refine ⟨22773257950267817390474545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30364343933690423187299393 22773257950267817390474545)
      ·
        refine ⟨17079943462700863042855909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22773257950267817390474545 17079943462700863042855909)
        ·
          refine ⟨3202489399256411820535483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17079943462700863042855909 3202489399256411820535483)
          ·
            refine ⟨4803734098884617730803225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3202489399256411820535483 4803734098884617730803225)
            ·
              refine ⟨3602800574163463298102419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4803734098884617730803225 3602800574163463298102419)
              ·
                refine ⟨5404200861245194947153629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3602800574163463298102419 5404200861245194947153629)
                ·
                  refine ⟨2026575322966948105182611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5404200861245194947153629 2026575322966948105182611)
                  ·
                    refine ⟨3039862984450422157773917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2026575322966948105182611 3039862984450422157773917)
                    ·
                      refine ⟨1139948619168908309165219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3039862984450422157773917 1139948619168908309165219)
                      ·
                        rfl

theorem cell23_2220042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 2, 1, 3, 1, 3].length) (baseStart_2220042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2220042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2220042 prefixEnd_2220042 := by exact prefixLift 2220042
  have htrace : WordTrace (prefixWord ++ tailWord_2220042) baseStart_2220042 baseEnd_2220042 := by
    simpa [prefixWord, tailWord_2220042, baseEnd_2220042] using wordTrace_append hprefix tailTrace_2220042
  have hstable : (prefixWord ++ tailWord_2220042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2220042).length < 2 ^ (prefixWord ++ tailWord_2220042).sum := by decide
  have hdescent : baseEnd_2220042 < baseStart_2220042 := by decide
  rcases family_descends (prefixWord ++ tailWord_2220042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2220051 : List Nat := [1, 1, 1, 2, 1, 4, 3, 1, 3, 1, 5]
def baseStart_2220051 : Nat := 118140960795 + 2220051 * 2 ^ 59
def prefixEnd_2220051 : Nat := 4983230072969 + 3 ^ 40 * 2220051 * 2
def baseEnd_2220051 : Nat := 1139953240494798773952677

theorem tailTrace_2220051 : CollatzResearch.WordTrace tailWord_2220051 prefixEnd_2220051 1139953240494798773952677 := by
  unfold tailWord_2220051
  simp only [CollatzResearch.WordTrace]
  refine ⟨80971912080141856369876007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53981274720094570913250671 80971912080141856369876007)
  ·
    refine ⟨121457868120212784554814011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80971912080141856369876007 121457868120212784554814011)
    ·
      refine ⟨182186802180319176832221017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121457868120212784554814011 182186802180319176832221017)
      ·
        refine ⟨136640101635239382624165763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 182186802180319176832221017 136640101635239382624165763)
        ·
          refine ⟨204960152452859073936248645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 136640101635239382624165763 204960152452859073936248645)
          ·
            refine ⟨38430028584911076363046621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 204960152452859073936248645 38430028584911076363046621)
            ·
              refine ⟨14411260719341653636142483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38430028584911076363046621 14411260719341653636142483)
              ·
                refine ⟨21616891079012480454213725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14411260719341653636142483 21616891079012480454213725)
                ·
                  refine ⟨8106334154629680170330147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21616891079012480454213725 8106334154629680170330147)
                  ·
                    refine ⟨12159501231944520255495221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8106334154629680170330147 12159501231944520255495221)
                    ·
                      refine ⟨1139953240494798773952677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12159501231944520255495221 1139953240494798773952677)
                      ·
                        rfl

theorem cell23_2220051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 3, 1, 3, 1, 5].length) (baseStart_2220051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2220051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2220051 prefixEnd_2220051 := by exact prefixLift 2220051
  have htrace : WordTrace (prefixWord ++ tailWord_2220051) baseStart_2220051 baseEnd_2220051 := by
    simpa [prefixWord, tailWord_2220051, baseEnd_2220051] using wordTrace_append hprefix tailTrace_2220051
  have hstable : (prefixWord ++ tailWord_2220051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2220051).length < 2 ^ (prefixWord ++ tailWord_2220051).sum := by decide
  have hdescent : baseEnd_2220051 < baseStart_2220051 := by decide
  rcases family_descends (prefixWord ++ tailWord_2220051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2220058 : List Nat := [3, 1, 1, 3, 1, 3, 3, 1, 1, 6]
def baseStart_2220058 : Nat := 118140960795 + 2220058 * 2 ^ 59
def prefixEnd_2220058 : Nat := 4983230072969 + 3 ^ 40 * 2220058 * 2
def baseEnd_2220058 : Nat := 379985611619793415521715

theorem tailTrace_2220058 : CollatzResearch.WordTrace tailWord_2220058 prefixEnd_2220058 379985611619793415521715 := by
  unfold tailWord_2220058
  simp only [CollatzResearch.WordTrace]
  refine ⟨20243041847779124141345207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53981444927410997710253885 20243041847779124141345207)
  ·
    refine ⟨30364562771668686212017811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20243041847779124141345207 30364562771668686212017811)
    ·
      refine ⟨45546844157503029318026717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30364562771668686212017811 45546844157503029318026717)
      ·
        refine ⟨17080066559063635994260019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45546844157503029318026717 17080066559063635994260019)
        ·
          refine ⟨25620099838595453991390029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17080066559063635994260019 25620099838595453991390029)
          ·
            refine ⟨9607537439473295246771261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25620099838595453991390029 9607537439473295246771261)
            ·
              refine ⟨3602826539802485717539223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9607537439473295246771261 3602826539802485717539223)
              ·
                refine ⟨5404239809703728576308835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3602826539802485717539223 5404239809703728576308835)
                ·
                  refine ⟨8106359714555592864463253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5404239809703728576308835 8106359714555592864463253)
                  ·
                    refine ⟨379985611619793415521715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8106359714555592864463253 379985611619793415521715)
                    ·
                      rfl

theorem cell23_2220058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 3, 1, 1, 6].length) (baseStart_2220058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2220058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2220058 prefixEnd_2220058 := by exact prefixLift 2220058
  have htrace : WordTrace (prefixWord ++ tailWord_2220058) baseStart_2220058 baseEnd_2220058 := by
    simpa [prefixWord, tailWord_2220058, baseEnd_2220058] using wordTrace_append hprefix tailTrace_2220058
  have hstable : (prefixWord ++ tailWord_2220058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2220058).length < 2 ^ (prefixWord ++ tailWord_2220058).sum := by decide
  have hdescent : baseEnd_2220058 < baseStart_2220058 := by decide
  rcases family_descends (prefixWord ++ tailWord_2220058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2220085 : List Nat := [1, 3, 3, 1, 1, 1, 4, 3, 1, 2, 3]
def baseStart_2220085 : Nat := 118140960795 + 2220085 * 2 ^ 59
def prefixEnd_2220085 : Nat := 4983230072969 + 3 ^ 40 * 2220085 * 2
def baseEnd_2220085 : Nat := 1139970698837051640927521

theorem tailTrace_2220085 : CollatzResearch.WordTrace tailWord_2220085 prefixEnd_2220085 1139970698837051640927521 := by
  unfold tailWord_2220085
  simp only [CollatzResearch.WordTrace]
  refine ⟨80973152162018680176613709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53982101441345786784409139 80973152162018680176613709)
  ·
    refine ⟨30364932060757005066230141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 80973152162018680176613709 30364932060757005066230141)
    ·
      refine ⟨11386849522783876899836303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30364932060757005066230141 11386849522783876899836303)
      ·
        refine ⟨17080274284175815349754455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11386849522783876899836303 17080274284175815349754455)
        ·
          refine ⟨25620411426263723024631683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17080274284175815349754455 25620411426263723024631683)
          ·
            refine ⟨38430617139395584536947525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25620411426263723024631683 38430617139395584536947525)
            ·
              refine ⟨7205740713636672100677661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 38430617139395584536947525 7205740713636672100677661)
              ·
                refine ⟨2702152767613752037754123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7205740713636672100677661 2702152767613752037754123)
                ·
                  refine ⟨4053229151420628056631185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2702152767613752037754123 4053229151420628056631185)
                  ·
                    refine ⟨3039921863565471042473389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4053229151420628056631185 3039921863565471042473389)
                    ·
                      refine ⟨1139970698837051640927521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3039921863565471042473389 1139970698837051640927521)
                      ·
                        rfl

theorem cell23_2220085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 4, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 4, 3, 1, 2, 3].length) (baseStart_2220085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2220085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2220085 prefixEnd_2220085 := by exact prefixLift 2220085
  have htrace : WordTrace (prefixWord ++ tailWord_2220085) baseStart_2220085 baseEnd_2220085 := by
    simpa [prefixWord, tailWord_2220085, baseEnd_2220085] using wordTrace_append hprefix tailTrace_2220085
  have hstable : (prefixWord ++ tailWord_2220085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2220085).length < 2 ^ (prefixWord ++ tailWord_2220085).sum := by decide
  have hdescent : baseEnd_2220085 < baseStart_2220085 := by decide
  rcases family_descends (prefixWord ++ tailWord_2220085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2220088 : List Nat := [2, 1, 2, 1, 6, 2, 9]
def baseStart_2220088 : Nat := 118140960795 + 2220088 * 2 ^ 59
def prefixEnd_2220088 : Nat := 4983230072969 + 3 ^ 40 * 2220088 * 2
def baseEnd_2220088 : Nat := 14073731349123643570247

theorem tailTrace_2220088 : CollatzResearch.WordTrace tailWord_2220088 prefixEnd_2220088 14073731349123643570247 := by
  unfold tailWord_2220088
  simp only [CollatzResearch.WordTrace]
  refine ⟨40486630790503905844486459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53982174387338541125981945 40486630790503905844486459)
  ·
    refine ⟨60729946185755858766729689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40486630790503905844486459 60729946185755858766729689)
    ·
      refine ⟨45547459639316894075047267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60729946185755858766729689 45547459639316894075047267)
      ·
        refine ⟨68321189458975341112570901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45547459639316894075047267 68321189458975341112570901)
        ·
          refine ⟨3202555755889469114651761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 68321189458975341112570901 3202555755889469114651761)
          ·
            refine ⟨2401916816917101835988821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3202555755889469114651761 2401916816917101835988821)
            ·
              refine ⟨14073731349123643570247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2401916816917101835988821 14073731349123643570247)
              ·
                rfl

theorem cell23_2220088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 2, 9].length) (baseStart_2220088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2220088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2220088 prefixEnd_2220088 := by exact prefixLift 2220088
  have htrace : WordTrace (prefixWord ++ tailWord_2220088) baseStart_2220088 baseEnd_2220088 := by
    simpa [prefixWord, tailWord_2220088, baseEnd_2220088] using wordTrace_append hprefix tailTrace_2220088
  have hstable : (prefixWord ++ tailWord_2220088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2220088).length < 2 ^ (prefixWord ++ tailWord_2220088).sum := by decide
  have hdescent : baseEnd_2220088 < baseStart_2220088 := by decide
  rcases family_descends (prefixWord ++ tailWord_2220088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2220101 : List Nat := [1, 3, 1, 1, 1, 3, 1, 3, 2, 7]
def baseStart_2220101 : Nat := 118140960795 + 2220101 * 2 ^ 59
def prefixEnd_2220101 : Nat := 4983230072969 + 3 ^ 40 * 2220101 * 2
def baseEnd_2220101 : Nat := 379992971509174526109149

theorem tailTrace_2220101 : CollatzResearch.WordTrace tailWord_2220101 prefixEnd_2220101 379992971509174526109149 := by
  unfold tailWord_2220101
  simp only [CollatzResearch.WordTrace]
  refine ⟨80973735729960714909196157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53982490486640476606130771 80973735729960714909196157)
  ·
    refine ⟨30365150898735268090948559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 80973735729960714909196157 30365150898735268090948559)
    ·
      refine ⟨45547726348102902136422839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30365150898735268090948559 45547726348102902136422839)
      ·
        refine ⟨68321589522154353204634259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45547726348102902136422839 68321589522154353204634259)
        ·
          refine ⟨102482384283231529806951389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68321589522154353204634259 102482384283231529806951389)
          ·
            refine ⟨38430894106211823677606771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 102482384283231529806951389 38430894106211823677606771)
            ·
              refine ⟨57646341159317735516410157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38430894106211823677606771 57646341159317735516410157)
              ·
                refine ⟨21617377934744150818653809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 57646341159317735516410157 21617377934744150818653809)
                ·
                  refine ⟨16213033451058113113990357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21617377934744150818653809 16213033451058113113990357)
                  ·
                    refine ⟨379992971509174526109149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 16213033451058113113990357 379992971509174526109149)
                    ·
                      rfl

theorem cell23_2220101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 3, 2, 7].length) (baseStart_2220101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2220101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2220101 prefixEnd_2220101 := by exact prefixLift 2220101
  have htrace : WordTrace (prefixWord ++ tailWord_2220101) baseStart_2220101 baseEnd_2220101 := by
    simpa [prefixWord, tailWord_2220101, baseEnd_2220101] using wordTrace_append hprefix tailTrace_2220101
  have hstable : (prefixWord ++ tailWord_2220101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2220101).length < 2 ^ (prefixWord ++ tailWord_2220101).sum := by decide
  have hdescent : baseEnd_2220101 < baseStart_2220101 := by decide
  rcases family_descends (prefixWord ++ tailWord_2220101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2220102 : List Nat := [6, 1, 1, 1, 1, 1, 2, 2, 3, 2, 3]
def baseStart_2220102 : Nat := 118140960795 + 2220102 * 2 ^ 59
def prefixEnd_2220102 : Nat := 4983230072969 + 3 ^ 40 * 2220102 * 2
def baseEnd_2220102 : Nat := 1139979428008178074414943

theorem tailTrace_2220102 : CollatzResearch.WordTrace tailWord_2220102 prefixEnd_2220102 1139979428008178074414943 := by
  unfold tailWord_2220102
  simp only [CollatzResearch.WordTrace]
  refine ⟨2530430381342409127499455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 53982514801971394719988373 2530430381342409127499455)
  ·
    refine ⟨3795645572013613691249183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2530430381342409127499455 3795645572013613691249183)
    ·
      refine ⟨5693468358020420536873775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3795645572013613691249183 5693468358020420536873775)
      ·
        refine ⟨8540202537030630805310663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5693468358020420536873775 8540202537030630805310663)
        ·
          refine ⟨12810303805545946207965995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8540202537030630805310663 12810303805545946207965995)
          ·
            refine ⟨19215455708318919311948993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12810303805545946207965995 19215455708318919311948993)
            ·
              refine ⟨14411591781239189483961745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19215455708318919311948993 14411591781239189483961745)
              ·
                refine ⟨10808693835929392112971309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14411591781239189483961745 10808693835929392112971309)
                ·
                  refine ⟨4053260188473522042364241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10808693835929392112971309 4053260188473522042364241)
                  ·
                    refine ⟨3039945141355141531773181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4053260188473522042364241 3039945141355141531773181)
                    ·
                      refine ⟨1139979428008178074414943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3039945141355141531773181 1139979428008178074414943)
                      ·
                        rfl

theorem cell23_2220102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 2, 2, 3, 2, 3].length) (baseStart_2220102 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2220102 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2220102 prefixEnd_2220102 := by exact prefixLift 2220102
  have htrace : WordTrace (prefixWord ++ tailWord_2220102) baseStart_2220102 baseEnd_2220102 := by
    simpa [prefixWord, tailWord_2220102, baseEnd_2220102] using wordTrace_append hprefix tailTrace_2220102
  have hstable : (prefixWord ++ tailWord_2220102).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2220102).length < 2 ^ (prefixWord ++ tailWord_2220102).sum := by decide
  have hdescent : baseEnd_2220102 < baseStart_2220102 := by decide
  rcases family_descends (prefixWord ++ tailWord_2220102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2220111 : List Nat := [1, 1, 2, 1, 1, 2, 2, 2, 4, 2, 5]
def baseStart_2220111 : Nat := 118140960795 + 2220111 * 2 ^ 59
def prefixEnd_2220111 : Nat := 4983230072969 + 3 ^ 40 * 2220111 * 2
def baseEnd_2220111 : Nat := 1139984049334068539202401

theorem tailTrace_2220111 : CollatzResearch.WordTrace tailWord_2220111 prefixEnd_2220111 1139984049334068539202401 := by
  unfold tailWord_2220111
  simp only [CollatzResearch.WordTrace]
  refine ⟨80974100459924486617060187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53982733639949657744706791 80974100459924486617060187)
  ·
    refine ⟨121461150689886729925590281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80974100459924486617060187 121461150689886729925590281)
    ·
      refine ⟨91095863017415047444192711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 121461150689886729925590281 91095863017415047444192711)
      ·
        refine ⟨136643794526122571166289067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91095863017415047444192711 136643794526122571166289067)
        ·
          refine ⟨204965691789183856749433601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 136643794526122571166289067 204965691789183856749433601)
          ·
            refine ⟨153724268841887892562075201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 204965691789183856749433601 153724268841887892562075201)
            ·
              refine ⟨115293201631415919421556401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 153724268841887892562075201 115293201631415919421556401)
              ·
                refine ⟨86469901223561939566167301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 115293201631415919421556401 86469901223561939566167301)
                ·
                  refine ⟨16213106479417863668656369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 86469901223561939566167301 16213106479417863668656369)
                  ·
                    refine ⟨12159829859563397751492277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16213106479417863668656369 12159829859563397751492277)
                    ·
                      refine ⟨1139984049334068539202401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12159829859563397751492277 1139984049334068539202401)
                      ·
                        rfl

theorem cell23_2220111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 2, 4, 2, 5].length) (baseStart_2220111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2220111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2220111 prefixEnd_2220111 := by exact prefixLift 2220111
  have htrace : WordTrace (prefixWord ++ tailWord_2220111) baseStart_2220111 baseEnd_2220111 := by
    simpa [prefixWord, tailWord_2220111, baseEnd_2220111] using wordTrace_append hprefix tailTrace_2220111
  have hstable : (prefixWord ++ tailWord_2220111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2220111).length < 2 ^ (prefixWord ++ tailWord_2220111).sum := by decide
  have hdescent : baseEnd_2220111 < baseStart_2220111 := by decide
  rcases family_descends (prefixWord ++ tailWord_2220111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2220218 : List Nat := [3, 1, 1, 1, 2, 2, 2, 3, 1, 2, 5]
def baseStart_2220218 : Nat := 118140960795 + 2220218 * 2 ^ 59
def prefixEnd_2220218 : Nat := 4983230072969 + 3 ^ 40 * 2220218 * 2
def baseEnd_2220218 : Nat := 1140038991764099620564409

theorem tailTrace_2220218 : CollatzResearch.WordTrace tailWord_2220218 prefixEnd_2220218 1140038991764099620564409 := by
  unfold tailWord_2220218
  simp only [CollatzResearch.WordTrace]
  refine ⟨20244500767634210972801327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53985335380357895927470205 20244500767634210972801327)
  ·
    refine ⟨30366751151451316459201991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20244500767634210972801327 30366751151451316459201991)
    ·
      refine ⟨45550126727176974688802987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30366751151451316459201991 45550126727176974688802987)
      ·
        refine ⟨68325190090765462033204481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45550126727176974688802987 68325190090765462033204481)
        ·
          refine ⟨51243892568074096524903361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 68325190090765462033204481 51243892568074096524903361)
          ·
            refine ⟨38432919426055572393677521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51243892568074096524903361 38432919426055572393677521)
            ·
              refine ⟨28824689569541679295258141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38432919426055572393677521 28824689569541679295258141)
              ·
                refine ⟨10809258588578129735721803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28824689569541679295258141 10809258588578129735721803)
                ·
                  refine ⟨16213887882867194603582705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10809258588578129735721803 16213887882867194603582705)
                  ·
                    refine ⟨12160415912150395952687029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16213887882867194603582705 12160415912150395952687029)
                    ·
                      refine ⟨1140038991764099620564409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12160415912150395952687029 1140038991764099620564409)
                      ·
                        rfl

theorem cell23_2220218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 3, 1, 2, 5].length) (baseStart_2220218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2220218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2220218 prefixEnd_2220218 := by exact prefixLift 2220218
  have htrace : WordTrace (prefixWord ++ tailWord_2220218) baseStart_2220218 baseEnd_2220218 := by
    simpa [prefixWord, tailWord_2220218, baseEnd_2220218] using wordTrace_append hprefix tailTrace_2220218
  have hstable : (prefixWord ++ tailWord_2220218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2220218).length < 2 ^ (prefixWord ++ tailWord_2220218).sum := by decide
  have hdescent : baseEnd_2220218 < baseStart_2220218 := by decide
  rcases family_descends (prefixWord ++ tailWord_2220218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2220246 : List Nat := [5, 2, 1, 2, 1, 3, 1, 3, 5]
def baseStart_2220246 : Nat := 118140960795 + 2220246 * 2 ^ 59
def prefixEnd_2220246 : Nat := 4983230072969 + 3 ^ 40 * 2220246 * 2
def baseEnd_2220246 : Nat := 126672596580269501223809

theorem tailTrace_2220246 : CollatzResearch.WordTrace tailWord_2220246 prefixEnd_2220246 126672596580269501223809 := by
  unfold tailWord_2220246
  simp only [CollatzResearch.WordTrace]
  refine ⟨5061189019652212792076537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 53986016209623603115483061 5061189019652212792076537)
  ·
    refine ⟨3795891764739159594057403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5061189019652212792076537 3795891764739159594057403)
    ·
      refine ⟨5693837647108739391086105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3795891764739159594057403 5693837647108739391086105)
      ·
        refine ⟨4270378235331554543314579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5693837647108739391086105 4270378235331554543314579)
        ·
          refine ⟨6405567352997331814971869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4270378235331554543314579 6405567352997331814971869)
          ·
            refine ⟨2402087757373999430614451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6405567352997331814971869 2402087757373999430614451)
            ·
              refine ⟨3603131636060999145921677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2402087757373999430614451 3603131636060999145921677)
              ·
                refine ⟨1351174363522874679720629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3603131636060999145921677 1351174363522874679720629)
                ·
                  refine ⟨126672596580269501223809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1351174363522874679720629 126672596580269501223809)
                  ·
                    rfl

theorem cell23_2220246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 3, 1, 3, 5].length) (baseStart_2220246 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2220246 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2220246 prefixEnd_2220246 := by exact prefixLift 2220246
  have htrace : WordTrace (prefixWord ++ tailWord_2220246) baseStart_2220246 baseEnd_2220246 := by
    simpa [prefixWord, tailWord_2220246, baseEnd_2220246] using wordTrace_append hprefix tailTrace_2220246
  have hstable : (prefixWord ++ tailWord_2220246).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2220246).length < 2 ^ (prefixWord ++ tailWord_2220246).sum := by decide
  have hdescent : baseEnd_2220246 < baseStart_2220246 := by decide
  rcases family_descends (prefixWord ++ tailWord_2220246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2220265 : List Nat := [1, 2, 1, 1, 1, 2, 2, 6, 2, 2, 3]
def baseStart_2220265 : Nat := 118140960795 + 2220265 * 2 ^ 59
def prefixEnd_2220265 : Nat := 4983230072969 + 3 ^ 40 * 2220265 * 2
def baseEnd_2220265 : Nat := 1140063125354860936676693

theorem tailTrace_2220265 : CollatzResearch.WordTrace tailWord_2220265 prefixEnd_2220265 1140063125354860936676693 := by
  unfold tailWord_2220265
  simp only [CollatzResearch.WordTrace]
  refine ⟨80979717301366570918166249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53986478200911047278777499 80979717301366570918166249)
  ·
    refine ⟨60734787976024928188624687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80979717301366570918166249 60734787976024928188624687)
    ·
      refine ⟨91102181964037392282937031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60734787976024928188624687 91102181964037392282937031)
      ·
        refine ⟨136653272946056088424405547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91102181964037392282937031 136653272946056088424405547)
        ·
          refine ⟨204979909419084132636608321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 136653272946056088424405547 204979909419084132636608321)
          ·
            refine ⟨153734932064313099477456241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 204979909419084132636608321 153734932064313099477456241)
            ·
              refine ⟨115301199048234824608092181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 153734932064313099477456241 115301199048234824608092181)
              ·
                refine ⟨5404743705386007403504321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 115301199048234824608092181 5404743705386007403504321)
                ·
                  refine ⟨4053557779039505552628241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5404743705386007403504321 4053557779039505552628241)
                  ·
                    refine ⟨3040168334279629164471181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4053557779039505552628241 3040168334279629164471181)
                    ·
                      refine ⟨1140063125354860936676693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3040168334279629164471181 1140063125354860936676693)
                      ·
                        rfl

theorem cell23_2220265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 6, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 6, 2, 2, 3].length) (baseStart_2220265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2220265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2220265 prefixEnd_2220265 := by exact prefixLift 2220265
  have htrace : WordTrace (prefixWord ++ tailWord_2220265) baseStart_2220265 baseEnd_2220265 := by
    simpa [prefixWord, tailWord_2220265, baseEnd_2220265] using wordTrace_append hprefix tailTrace_2220265
  have hstable : (prefixWord ++ tailWord_2220265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2220265).length < 2 ^ (prefixWord ++ tailWord_2220265).sum := by decide
  have hdescent : baseEnd_2220265 < baseStart_2220265 := by decide
  rcases family_descends (prefixWord ++ tailWord_2220265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2220268 : List Nat := [2, 2, 1, 1, 2, 3, 1, 3, 8]
def baseStart_2220268 : Nat := 118140960795 + 2220268 * 2 ^ 59
def prefixEnd_2220268 : Nat := 4983230072969 + 3 ^ 40 * 2220268 * 2
def baseEnd_2220268 : Nat := 126673851755202713882131

theorem tailTrace_2220268 : CollatzResearch.WordTrace tailWord_2220268 prefixEnd_2220268 126673851755202713882131 := by
  unfold tailWord_2220268
  simp only [CollatzResearch.WordTrace]
  refine ⟨40489913360177851215262729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53986551146903801620350305 40489913360177851215262729)
  ·
    refine ⟨30367435020133388411447047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40489913360177851215262729 30367435020133388411447047)
    ·
      refine ⟨45551152530200082617170571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30367435020133388411447047 45551152530200082617170571)
      ·
        refine ⟨68326728795300123925755857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45551152530200082617170571 68326728795300123925755857)
        ·
          refine ⟨51245046596475092944316893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 68326728795300123925755857 51245046596475092944316893)
          ·
            refine ⟨19216892473678159854118835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 51245046596475092944316893 19216892473678159854118835)
            ·
              refine ⟨28825338710517239781178253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19216892473678159854118835 28825338710517239781178253)
              ·
                refine ⟨10809502016443964917941845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28825338710517239781178253 10809502016443964917941845)
                ·
                  refine ⟨126673851755202713882131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 10809502016443964917941845 126673851755202713882131)
                  ·
                    rfl

theorem cell23_2220268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 8].length) (baseStart_2220268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2220268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2220268 prefixEnd_2220268 := by exact prefixLift 2220268
  have htrace : WordTrace (prefixWord ++ tailWord_2220268) baseStart_2220268 baseEnd_2220268 := by
    simpa [prefixWord, tailWord_2220268, baseEnd_2220268] using wordTrace_append hprefix tailTrace_2220268
  have hstable : (prefixWord ++ tailWord_2220268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2220268).length < 2 ^ (prefixWord ++ tailWord_2220268).sum := by decide
  have hdescent : baseEnd_2220268 < baseStart_2220268 := by decide
  rcases family_descends (prefixWord ++ tailWord_2220268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2220272 : List Nat := [2, 1, 1, 1, 3, 1, 1, 8, 1, 4]
def baseStart_2220272 : Nat := 118140960795 + 2220272 * 2 ^ 59
def prefixEnd_2220272 : Nat := 4983230072969 + 3 ^ 40 * 2220272 * 2
def baseEnd_2220272 : Nat := 380022239906480803096387

theorem tailTrace_2220272 : CollatzResearch.WordTrace tailWord_2220272 prefixEnd_2220272 380022239906480803096387 := by
  unfold tailWord_2220272
  simp only [CollatzResearch.WordTrace]
  refine ⟨40489986306170605556835535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53986648408227474075780713 40489986306170605556835535)
  ·
    refine ⟨60734979459255908335253303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40489986306170605556835535 60734979459255908335253303)
    ·
      refine ⟨91102469188883862502879955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60734979459255908335253303 91102469188883862502879955)
      ·
        refine ⟨136653703783325793754319933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91102469188883862502879955 136653703783325793754319933)
        ·
          refine ⟨51245138918747172657869975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 136653703783325793754319933 51245138918747172657869975)
          ·
            refine ⟨76867708378120758986804963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51245138918747172657869975 76867708378120758986804963)
            ·
              refine ⟨115301562567181138480207445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 76867708378120758986804963 115301562567181138480207445)
              ·
                refine ⟨1351190186334153966564931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 115301562567181138480207445 1351190186334153966564931)
                ·
                  refine ⟨2026785279501230949847397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1351190186334153966564931 2026785279501230949847397)
                  ·
                    refine ⟨380022239906480803096387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2026785279501230949847397 380022239906480803096387)
                    ·
                      rfl

theorem cell23_2220272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 8, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 8, 1, 4].length) (baseStart_2220272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2220272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2220272 prefixEnd_2220272 := by exact prefixLift 2220272
  have htrace : WordTrace (prefixWord ++ tailWord_2220272) baseStart_2220272 baseEnd_2220272 := by
    simpa [prefixWord, tailWord_2220272, baseEnd_2220272] using wordTrace_append hprefix tailTrace_2220272
  have hstable : (prefixWord ++ tailWord_2220272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2220272).length < 2 ^ (prefixWord ++ tailWord_2220272).sum := by decide
  have hdescent : baseEnd_2220272 < baseStart_2220272 := by decide
  rcases family_descends (prefixWord ++ tailWord_2220272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2220288 : List Nat := [2, 1, 1, 2, 1, 1, 4, 2, 1, 2, 6]
def baseStart_2220288 : Nat := 118140960795 + 2220288 * 2 ^ 59
def prefixEnd_2220288 : Nat := 4983230072969 + 3 ^ 40 * 2220288 * 2
def baseEnd_2220288 : Nat := 1140074935409914346689087

theorem tailTrace_2220288 : CollatzResearch.WordTrace tailWord_2220288 prefixEnd_2220288 1140074935409914346689087 := by
  unfold tailWord_2220288
  simp only [CollatzResearch.WordTrace]
  refine ⟨40490278090141622923126759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53987037453522163897502345 40490278090141622923126759)
  ·
    refine ⟨60735417135212434384690139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40490278090141622923126759 60735417135212434384690139)
    ·
      refine ⟨91103125702818651577035209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60735417135212434384690139 91103125702818651577035209)
      ·
        refine ⟨68327344277113988682776407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 91103125702818651577035209 68327344277113988682776407)
        ·
          refine ⟨102491016415670983024164611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68327344277113988682776407 102491016415670983024164611)
          ·
            refine ⟨153736524623506474536246917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 102491016415670983024164611 153736524623506474536246917)
            ·
              refine ⟨28825598366907463975546297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 153736524623506474536246917 28825598366907463975546297)
              ·
                refine ⟨21619198775180597981659723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28825598366907463975546297 21619198775180597981659723)
                ·
                  refine ⟨32428798162770896972489585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21619198775180597981659723 32428798162770896972489585)
                  ·
                    refine ⟨24321598622078172729367189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 32428798162770896972489585 24321598622078172729367189)
                    ·
                      refine ⟨1140074935409914346689087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 24321598622078172729367189 1140074935409914346689087)
                      ·
                        rfl

theorem cell23_2220288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 2, 1, 2, 6].length) (baseStart_2220288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2220288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2220288 prefixEnd_2220288 := by exact prefixLift 2220288
  have htrace : WordTrace (prefixWord ++ tailWord_2220288) baseStart_2220288 baseEnd_2220288 := by
    simpa [prefixWord, tailWord_2220288, baseEnd_2220288] using wordTrace_append hprefix tailTrace_2220288
  have hstable : (prefixWord ++ tailWord_2220288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2220288).length < 2 ^ (prefixWord ++ tailWord_2220288).sum := by decide
  have hdescent : baseEnd_2220288 < baseStart_2220288 := by decide
  rcases family_descends (prefixWord ++ tailWord_2220288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2220315 : List Nat := [1, 1, 1, 1, 1, 1, 6, 5, 1, 5]
def baseStart_2220315 : Nat := 118140960795 + 2220315 * 2 ^ 59
def prefixEnd_2220315 : Nat := 4983230072969 + 3 ^ 40 * 2220315 * 2
def baseEnd_2220315 : Nat := 380029599795861913683821

theorem tailTrace_2220315 : CollatzResearch.WordTrace tailWord_2220315 prefixEnd_2220315 380029599795861913683821 := by
  unfold tailWord_2220315
  simp only [CollatzResearch.WordTrace]
  refine ⟨80981540951185429457486399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53987693967456952971657599 80981540951185429457486399)
  ·
    refine ⟨121472311426778144186229599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80981540951185429457486399 121472311426778144186229599)
    ·
      refine ⟨182208467140167216279344399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121472311426778144186229599 182208467140167216279344399)
      ·
        refine ⟨273312700710250824419016599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 182208467140167216279344399 273312700710250824419016599)
        ·
          refine ⟨409969051065376236628524899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 273312700710250824419016599 409969051065376236628524899)
          ·
            refine ⟨614953576598064354942787349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 409969051065376236628524899 614953576598064354942787349)
            ·
              refine ⟨28825948903034266637943157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 614953576598064354942787349 28825948903034266637943157)
              ·
                refine ⟨2702432709659462497307171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 28825948903034266637943157 2702432709659462497307171)
                ·
                  refine ⟨4053649064489193745960757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2702432709659462497307171 4053649064489193745960757)
                  ·
                    refine ⟨380029599795861913683821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4053649064489193745960757 380029599795861913683821)
                    ·
                      rfl

theorem cell23_2220315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 5, 1, 5].length) (baseStart_2220315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2220315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2220315 prefixEnd_2220315 := by exact prefixLift 2220315
  have htrace : WordTrace (prefixWord ++ tailWord_2220315) baseStart_2220315 baseEnd_2220315 := by
    simpa [prefixWord, tailWord_2220315, baseEnd_2220315] using wordTrace_append hprefix tailTrace_2220315
  have hstable : (prefixWord ++ tailWord_2220315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2220315).length < 2 ^ (prefixWord ++ tailWord_2220315).sum := by decide
  have hdescent : baseEnd_2220315 < baseStart_2220315 := by decide
  rcases family_descends (prefixWord ++ tailWord_2220315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2220335 : List Nat := [1, 1, 2, 1, 2, 1, 5, 2, 3, 1, 4]
def baseStart_2220335 : Nat := 118140960795 + 2220335 * 2 ^ 59
def prefixEnd_2220335 : Nat := 4983230072969 + 3 ^ 40 * 2220335 * 2
def baseEnd_2220335 : Nat := 1140099069000675662801371

theorem tailTrace_2220335 : CollatzResearch.WordTrace tailWord_2220335 prefixEnd_2220335 1140099069000675662801371 := by
  unfold tailWord_2220335
  simp only [CollatzResearch.WordTrace]
  refine ⟨80982270411112972873214459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53988180274075315248809639 80982270411112972873214459)
  ·
    refine ⟨121473405616669459309821689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80982270411112972873214459 121473405616669459309821689)
    ·
      refine ⟨91105054212502094482366267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 121473405616669459309821689 91105054212502094482366267)
      ·
        refine ⟨136657581318753141723549401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91105054212502094482366267 136657581318753141723549401)
        ·
          refine ⟨102493185989064856292662051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 136657581318753141723549401 102493185989064856292662051)
          ·
            refine ⟨153739778983597284438993077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 102493185989064856292662051 153739778983597284438993077)
            ·
              refine ⟨14413104279712245416155601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 153739778983597284438993077 14413104279712245416155601)
              ·
                refine ⟨10809828209784184062116701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14413104279712245416155601 10809828209784184062116701)
                ·
                  refine ⟨4053685578669069023293763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10809828209784184062116701 4053685578669069023293763)
                  ·
                    refine ⟨6080528368003603534940645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4053685578669069023293763 6080528368003603534940645)
                    ·
                      refine ⟨1140099069000675662801371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6080528368003603534940645 1140099069000675662801371)
                      ·
                        rfl

theorem cell23_2220335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 5, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 5, 2, 3, 1, 4].length) (baseStart_2220335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2220335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2220335 prefixEnd_2220335 := by exact prefixLift 2220335
  have htrace : WordTrace (prefixWord ++ tailWord_2220335) baseStart_2220335 baseEnd_2220335 := by
    simpa [prefixWord, tailWord_2220335, baseEnd_2220335] using wordTrace_append hprefix tailTrace_2220335
  have hstable : (prefixWord ++ tailWord_2220335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2220335).length < 2 ^ (prefixWord ++ tailWord_2220335).sum := by decide
  have hdescent : baseEnd_2220335 < baseStart_2220335 := by decide
  rcases family_descends (prefixWord ++ tailWord_2220335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2220356 : List Nat := [2, 3, 4, 1, 2, 1, 1, 1, 1, 5, 2]
def baseStart_2220356 : Nat := 118140960795 + 2220356 * 2 ^ 59
def prefixEnd_2220356 : Nat := 4983230072969 + 3 ^ 40 * 2220356 * 2
def baseEnd_2220356 : Nat := 1140109852094420080638775

theorem tailTrace_2220356 : CollatzResearch.WordTrace tailWord_2220356 prefixEnd_2220356 1140109852094420080638775 := by
  unfold tailWord_2220356
  simp only [CollatzResearch.WordTrace]
  refine ⟨40491518172018446729864461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53988690896024595639819281 40491518172018446729864461)
  ·
    refine ⟨15184319314506917523699173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40491518172018446729864461 15184319314506917523699173)
    ·
      refine ⟨2847059871470047035693595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15184319314506917523699173 2847059871470047035693595)
      ·
        refine ⟨4270589807205070553540393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2847059871470047035693595 4270589807205070553540393)
        ·
          refine ⟨3202942355403802915155295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4270589807205070553540393 3202942355403802915155295)
          ·
            refine ⟨4804413533105704372732943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3202942355403802915155295 4804413533105704372732943)
            ·
              refine ⟨7206620299658556559099415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4804413533105704372732943 7206620299658556559099415)
              ·
                refine ⟨10809930449487834838649123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7206620299658556559099415 10809930449487834838649123)
                ·
                  refine ⟨16214895674231752257973685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10809930449487834838649123 16214895674231752257973685)
                  ·
                    refine ⟨1520146469459226774185033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 16214895674231752257973685 1520146469459226774185033)
                    ·
                      refine ⟨1140109852094420080638775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1520146469459226774185033 1140109852094420080638775)
                      ·
                        rfl

theorem cell23_2220356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 1, 1, 1, 5, 2].length) (baseStart_2220356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2220356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2220356 prefixEnd_2220356 := by exact prefixLift 2220356
  have htrace : WordTrace (prefixWord ++ tailWord_2220356) baseStart_2220356 baseEnd_2220356 := by
    simpa [prefixWord, tailWord_2220356, baseEnd_2220356] using wordTrace_append hprefix tailTrace_2220356
  have hstable : (prefixWord ++ tailWord_2220356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2220356).length < 2 ^ (prefixWord ++ tailWord_2220356).sum := by decide
  have hdescent : baseEnd_2220356 < baseStart_2220356 := by decide
  rcases family_descends (prefixWord ++ tailWord_2220356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2220369 : List Nat := [1, 2, 2, 1, 4, 2, 4, 1, 1, 1, 4]
def baseStart_2220369 : Nat := 118140960795 + 2220369 * 2 ^ 59
def prefixEnd_2220369 : Nat := 4983230072969 + 3 ^ 40 * 2220369 * 2
def baseEnd_2220369 : Nat := 1140116527342928529776215

theorem tailTrace_2220369 : CollatzResearch.WordTrace tailWord_2220369 prefixEnd_2220369 1140116527342928529776215 := by
  unfold tailWord_2220369
  simp only [CollatzResearch.WordTrace]
  refine ⟨80983510492989796679952161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53989006995326531119968107 80983510492989796679952161)
  ·
    refine ⟨60737632869742347509964121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80983510492989796679952161 60737632869742347509964121)
    ·
      refine ⟨45553224652306760632473091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60737632869742347509964121 45553224652306760632473091)
      ·
        refine ⟨68329836978460140948709637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45553224652306760632473091 68329836978460140948709637)
        ·
          refine ⟨12811844433461276427883057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 68329836978460140948709637 12811844433461276427883057)
          ·
            refine ⟨9608883325095957320912293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12811844433461276427883057 9608883325095957320912293)
            ·
              refine ⟨1801665623455491997671055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9608883325095957320912293 1801665623455491997671055)
              ·
                refine ⟨2702498435183237996506583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1801665623455491997671055 2702498435183237996506583)
                ·
                  refine ⟨4053747652774856994759875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2702498435183237996506583 4053747652774856994759875)
                  ·
                    refine ⟨6080621479162285492139813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4053747652774856994759875 6080621479162285492139813)
                    ·
                      refine ⟨1140116527342928529776215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6080621479162285492139813 1140116527342928529776215)
                      ·
                        rfl

theorem cell23_2220369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 4, 1, 1, 1, 4].length) (baseStart_2220369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2220369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2220369 prefixEnd_2220369 := by exact prefixLift 2220369
  have htrace : WordTrace (prefixWord ++ tailWord_2220369) baseStart_2220369 baseEnd_2220369 := by
    simpa [prefixWord, tailWord_2220369, baseEnd_2220369] using wordTrace_append hprefix tailTrace_2220369
  have hstable : (prefixWord ++ tailWord_2220369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2220369).length < 2 ^ (prefixWord ++ tailWord_2220369).sum := by decide
  have hdescent : baseEnd_2220369 < baseStart_2220369 := by decide
  rcases family_descends (prefixWord ++ tailWord_2220369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2220385 : List Nat := [1, 2, 3, 1, 1, 1, 1, 1, 2, 7, 3]
def baseStart_2220385 : Nat := 118140960795 + 2220385 * 2 ^ 59
def prefixEnd_2220385 : Nat := 4983230072969 + 3 ^ 40 * 2220385 * 2
def baseEnd_2220385 : Nat := 1140124743033400467176141

theorem tailTrace_2220385 : CollatzResearch.WordTrace tailWord_2220385 prefixEnd_2220385 1140124743033400467176141 := by
  unfold tailWord_2220385
  simp only [CollatzResearch.WordTrace]
  refine ⟨80984094060931831412534609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53989396040621220941689739 80984094060931831412534609)
  ·
    refine ⟨60738070545698873559400957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80984094060931831412534609 60738070545698873559400957)
    ·
      refine ⟨22776776454637077584775359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 60738070545698873559400957 22776776454637077584775359)
      ·
        refine ⟨34165164681955616377163039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22776776454637077584775359 34165164681955616377163039)
        ·
          refine ⟨51247747022933424565744559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34165164681955616377163039 51247747022933424565744559)
          ·
            refine ⟨76871620534400136848616839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51247747022933424565744559 76871620534400136848616839)
            ·
              refine ⟨115307430801600205272925259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 76871620534400136848616839 115307430801600205272925259)
              ·
                refine ⟨172961146202400307909387889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 115307430801600205272925259 172961146202400307909387889)
                ·
                  refine ⟨129720859651800230932040917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 172961146202400307909387889 129720859651800230932040917)
                  ·
                    refine ⟨3040332648089067912469709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 129720859651800230932040917 3040332648089067912469709)
                    ·
                      refine ⟨1140124743033400467176141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3040332648089067912469709 1140124743033400467176141)
                      ·
                        rfl

theorem cell23_2220385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 1, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 1, 2, 7, 3].length) (baseStart_2220385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2220385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2220385 prefixEnd_2220385 := by exact prefixLift 2220385
  have htrace : WordTrace (prefixWord ++ tailWord_2220385) baseStart_2220385 baseEnd_2220385 := by
    simpa [prefixWord, tailWord_2220385, baseEnd_2220385] using wordTrace_append hprefix tailTrace_2220385
  have hstable : (prefixWord ++ tailWord_2220385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2220385).length < 2 ^ (prefixWord ++ tailWord_2220385).sum := by decide
  have hdescent : baseEnd_2220385 < baseStart_2220385 := by decide
  rcases family_descends (prefixWord ++ tailWord_2220385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2220386 : List Nat := [3, 3, 2, 1, 1, 2, 1, 3, 3, 2, 2]
def baseStart_2220386 : Nat := 118140960795 + 2220386 * 2 ^ 59
def prefixEnd_2220386 : Nat := 4983230072969 + 3 ^ 40 * 2220386 * 2
def baseEnd_2220386 : Nat := 1140125256514054963263637

theorem tailTrace_2220386 : CollatzResearch.WordTrace tailWord_2220386 prefixEnd_2220386 1140125256514054963263637 := by
  unfold tailWord_2220386
  simp only [CollatzResearch.WordTrace]
  refine ⟨20246032633482052145830253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53989420355952139055547341 20246032633482052145830253)
  ·
    refine ⟨7592262237555769554686345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20246032633482052145830253 7592262237555769554686345)
    ·
      refine ⟨5694196678166827166014759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7592262237555769554686345 5694196678166827166014759)
      ·
        refine ⟨8541295017250240749022139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5694196678166827166014759 8541295017250240749022139)
        ·
          refine ⟨12811942525875361123533209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8541295017250240749022139 12811942525875361123533209)
          ·
            refine ⟨9608956894406520842649907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12811942525875361123533209 9608956894406520842649907)
            ·
              refine ⟨14413435341609781263974861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9608956894406520842649907 14413435341609781263974861)
              ·
                refine ⟨5405038253103667973990573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14413435341609781263974861 5405038253103667973990573)
                ·
                  refine ⟨2026889344913875490246465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5405038253103667973990573 2026889344913875490246465)
                  ·
                    refine ⟨1520167008685406617684849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2026889344913875490246465 1520167008685406617684849)
                    ·
                      refine ⟨1140125256514054963263637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1520167008685406617684849 1140125256514054963263637)
                      ·
                        rfl

theorem cell23_2220386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 1, 3, 3, 2, 2].length) (baseStart_2220386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2220386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2220386 prefixEnd_2220386 := by exact prefixLift 2220386
  have htrace : WordTrace (prefixWord ++ tailWord_2220386) baseStart_2220386 baseEnd_2220386 := by
    simpa [prefixWord, tailWord_2220386, baseEnd_2220386] using wordTrace_append hprefix tailTrace_2220386
  have hstable : (prefixWord ++ tailWord_2220386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2220386).length < 2 ^ (prefixWord ++ tailWord_2220386).sum := by decide
  have hdescent : baseEnd_2220386 < baseStart_2220386 := by decide
  rcases family_descends (prefixWord ++ tailWord_2220386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2220396 : List Nat := [2, 2, 1, 1, 6, 1, 3, 1, 2, 4]
def baseStart_2220396 : Nat := 118140960795 + 2220396 * 2 ^ 59
def prefixEnd_2220396 : Nat := 4983230072969 + 3 ^ 40 * 2220396 * 2
def baseEnd_2220396 : Nat := 380043463773533308046197

theorem tailTrace_2220396 : CollatzResearch.WordTrace tailWord_2220396 prefixEnd_2220396 380043463773533308046197 := by
  unfold tailWord_2220396
  simp only [CollatzResearch.WordTrace]
  refine ⟨40492247631945990145592521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53989663509261320194123361 40492247631945990145592521)
  ·
    refine ⟨30369185723959492609194391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40492247631945990145592521 30369185723959492609194391)
    ·
      refine ⟨45553778585939238913791587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30369185723959492609194391 45553778585939238913791587)
      ·
        refine ⟨68330667878908858370687381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45553778585939238913791587 68330667878908858370687381)
        ·
          refine ⟨3203000056823852736125971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 68330667878908858370687381 3203000056823852736125971)
          ·
            refine ⟨4804500085235779104188957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3203000056823852736125971 4804500085235779104188957)
            ·
              refine ⟨1801687531963417164070859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4804500085235779104188957 1801687531963417164070859)
              ·
                refine ⟨2702531297945125746106289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1801687531963417164070859 2702531297945125746106289)
                ·
                  refine ⟨2026898473458844309579717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2702531297945125746106289 2026898473458844309579717)
                  ·
                    refine ⟨380043463773533308046197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2026898473458844309579717 380043463773533308046197)
                    ·
                      rfl

theorem cell23_2220396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 2, 4].length) (baseStart_2220396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2220396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2220396 prefixEnd_2220396 := by exact prefixLift 2220396
  have htrace : WordTrace (prefixWord ++ tailWord_2220396) baseStart_2220396 baseEnd_2220396 := by
    simpa [prefixWord, tailWord_2220396, baseEnd_2220396] using wordTrace_append hprefix tailTrace_2220396
  have hstable : (prefixWord ++ tailWord_2220396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2220396).length < 2 ^ (prefixWord ++ tailWord_2220396).sum := by decide
  have hdescent : baseEnd_2220396 < baseStart_2220396 := by decide
  rcases family_descends (prefixWord ++ tailWord_2220396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2220476 : List Nat := [2, 2, 2, 4, 1, 2, 1, 2, 1, 4, 2]
def baseStart_2220476 : Nat := 118140960795 + 2220476 * 2 ^ 59
def prefixEnd_2220476 : Nat := 4983230072969 + 3 ^ 40 * 2220476 * 2
def baseEnd_2220476 : Nat := 1140171469772959611138223

theorem tailTrace_2220476 : CollatzResearch.WordTrace tailWord_2220476 prefixEnd_2220476 1140171469772959611138223 := by
  unfold tailWord_2220476
  simp only [CollatzResearch.WordTrace]
  refine ⟨40493706551801076977048641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53991608735734769302731521 40493706551801076977048641)
  ·
    refine ⟨30370279913850807732786481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40493706551801076977048641 30370279913850807732786481)
    ·
      refine ⟨22777709935388105799589861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30370279913850807732786481 22777709935388105799589861)
      ·
        refine ⟨4270820612885269837423099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22777709935388105799589861 4270820612885269837423099)
        ·
          refine ⟨6406230919327904756134649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4270820612885269837423099 6406230919327904756134649)
          ·
            refine ⟨4804673189495928567100987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6406230919327904756134649 4804673189495928567100987)
            ·
              refine ⟨7207009784243892850651481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4804673189495928567100987 7207009784243892850651481)
              ·
                refine ⟨5405257338182919637988611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7207009784243892850651481 5405257338182919637988611)
                ·
                  refine ⟨8107886007274379456982917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5405257338182919637988611 8107886007274379456982917)
                  ·
                    refine ⟨1520228626363946148184297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8107886007274379456982917 1520228626363946148184297)
                    ·
                      refine ⟨1140171469772959611138223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1520228626363946148184297 1140171469772959611138223)
                      ·
                        rfl

theorem cell23_2220476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 1, 2, 1, 4, 2].length) (baseStart_2220476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2220476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2220476 prefixEnd_2220476 := by exact prefixLift 2220476
  have htrace : WordTrace (prefixWord ++ tailWord_2220476) baseStart_2220476 baseEnd_2220476 := by
    simpa [prefixWord, tailWord_2220476, baseEnd_2220476] using wordTrace_append hprefix tailTrace_2220476
  have hstable : (prefixWord ++ tailWord_2220476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2220476).length < 2 ^ (prefixWord ++ tailWord_2220476).sum := by decide
  have hdescent : baseEnd_2220476 < baseStart_2220476 := by decide
  rcases family_descends (prefixWord ++ tailWord_2220476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2220495 : List Nat := [1, 1, 2, 1, 1, 4, 1, 2, 3, 7]
def baseStart_2220495 : Nat := 118140960795 + 2220495 * 2 ^ 59
def prefixEnd_2220495 : Nat := 4983230072969 + 3 ^ 40 * 2220495 * 2
def baseEnd_2220495 : Nat := 380060408635131678933545

theorem tailTrace_2220495 : CollatzResearch.WordTrace tailWord_2220495 prefixEnd_2220495 380060408635131678933545 := by
  unfold tailWord_2220495
  simp only [CollatzResearch.WordTrace]
  refine ⟨80988106090533320199038939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53992070727022213466025959 80988106090533320199038939)
  ·
    refine ⟨121482159135799980298558409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80988106090533320199038939 121482159135799980298558409)
    ·
      refine ⟨91111619351849985223918807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 121482159135799980298558409 91111619351849985223918807)
      ·
        refine ⟨136667429027774977835878211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91111619351849985223918807 136667429027774977835878211)
        ·
          refine ⟨205001143541662466753817317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 136667429027774977835878211 205001143541662466753817317)
          ·
            refine ⟨38437714414061712516340747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 205001143541662466753817317 38437714414061712516340747)
            ·
              refine ⟨57656571621092568774511121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38437714414061712516340747 57656571621092568774511121)
              ·
                refine ⟨43242428715819426580883341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 57656571621092568774511121 43242428715819426580883341)
                ·
                  refine ⟨16215910768432284967831253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 43242428715819426580883341 16215910768432284967831253)
                  ·
                    refine ⟨380060408635131678933545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 16215910768432284967831253 380060408635131678933545)
                    ·
                      rfl

theorem cell23_2220495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 2, 3, 7].length) (baseStart_2220495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2220495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2220495 prefixEnd_2220495 := by exact prefixLift 2220495
  have htrace : WordTrace (prefixWord ++ tailWord_2220495) baseStart_2220495 baseEnd_2220495 := by
    simpa [prefixWord, tailWord_2220495, baseEnd_2220495] using wordTrace_append hprefix tailTrace_2220495
  have hstable : (prefixWord ++ tailWord_2220495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2220495).length < 2 ^ (prefixWord ++ tailWord_2220495).sum := by decide
  have hdescent : baseEnd_2220495 < baseStart_2220495 := by decide
  rcases family_descends (prefixWord ++ tailWord_2220495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2220509 : List Nat := [1, 4, 3, 1, 1, 1, 3, 1, 2, 3, 3]
def baseStart_2220509 : Nat := 118140960795 + 2220509 * 2 ^ 59
def prefixEnd_2220509 : Nat := 4983230072969 + 3 ^ 40 * 2220509 * 2
def baseEnd_2220509 : Nat := 1140188414634557982025571

theorem tailTrace_2220509 : CollatzResearch.WordTrace tailWord_2220509 prefixEnd_2220509 1140188414634557982025571 := by
  unfold tailWord_2220509
  simp only [CollatzResearch.WordTrace]
  refine ⟨80988616712482600590048581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53992411141655067060032387 80988616712482600590048581)
  ·
    refine ⟨15185365633590487610634109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 80988616712482600590048581 15185365633590487610634109)
    ·
      refine ⟨5694512112596432853987791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15185365633590487610634109 5694512112596432853987791)
      ·
        refine ⟨8541768168894649280981687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5694512112596432853987791 8541768168894649280981687)
        ·
          refine ⟨12812652253341973921472531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8541768168894649280981687 12812652253341973921472531)
          ·
            refine ⟨19218978380012960882208797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12812652253341973921472531 19218978380012960882208797)
            ·
              refine ⟨7207116892504860330828299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19218978380012960882208797 7207116892504860330828299)
              ·
                refine ⟨10810675338757290496242449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7207116892504860330828299 10810675338757290496242449)
                ·
                  refine ⟨8108006504067967872181837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10810675338757290496242449 8108006504067967872181837)
                  ·
                    refine ⟨3040502439025487952068189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8108006504067967872181837 3040502439025487952068189)
                    ·
                      refine ⟨1140188414634557982025571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3040502439025487952068189 1140188414634557982025571)
                      ·
                        rfl

theorem cell23_2220509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 3, 1, 2, 3, 3].length) (baseStart_2220509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2220509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2220509 prefixEnd_2220509 := by exact prefixLift 2220509
  have htrace : WordTrace (prefixWord ++ tailWord_2220509) baseStart_2220509 baseEnd_2220509 := by
    simpa [prefixWord, tailWord_2220509, baseEnd_2220509] using wordTrace_append hprefix tailTrace_2220509
  have hstable : (prefixWord ++ tailWord_2220509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2220509).length < 2 ^ (prefixWord ++ tailWord_2220509).sum := by decide
  have hdescent : baseEnd_2220509 < baseStart_2220509 := by decide
  rcases family_descends (prefixWord ++ tailWord_2220509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2220519 : List Nat := [1, 1, 5, 2, 1, 1, 1, 2, 2, 5, 2]
def baseStart_2220519 : Nat := 118140960795 + 2220519 * 2 ^ 59
def prefixEnd_2220519 : Nat := 4983230072969 + 3 ^ 40 * 2220519 * 2
def baseEnd_2220519 : Nat := 1140193549441102942900525

theorem tailTrace_2220519 : CollatzResearch.WordTrace tailWord_2220519 prefixEnd_2220519 1140193549441102942900525 := by
  unfold tailWord_2220519
  simp only [CollatzResearch.WordTrace]
  refine ⟨80988981442446372297912611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53992654294964248198608407 80988981442446372297912611)
  ·
    refine ⟨121483472163669558446868917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80988981442446372297912611 121483472163669558446868917)
    ·
      refine ⟨11389075515344021104393961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 121483472163669558446868917 11389075515344021104393961)
      ·
        refine ⟨8541806636508015828295471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11389075515344021104393961 8541806636508015828295471)
        ·
          refine ⟨12812709954762023742443207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8541806636508015828295471 12812709954762023742443207)
          ·
            refine ⟨19219064932143035613664811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12812709954762023742443207 19219064932143035613664811)
            ·
              refine ⟨28828597398214553420497217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19219064932143035613664811 28828597398214553420497217)
              ·
                refine ⟨21621448048660915065372913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28828597398214553420497217 21621448048660915065372913)
                ·
                  refine ⟨16216086036495686299029685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21621448048660915065372913 16216086036495686299029685)
                  ·
                    refine ⟨1520258065921470590534033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 16216086036495686299029685 1520258065921470590534033)
                    ·
                      refine ⟨1140193549441102942900525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1520258065921470590534033 1140193549441102942900525)
                      ·
                        rfl

theorem cell23_2220519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 2, 2, 5, 2].length) (baseStart_2220519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2220519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2220519 prefixEnd_2220519 := by exact prefixLift 2220519
  have htrace : WordTrace (prefixWord ++ tailWord_2220519) baseStart_2220519 baseEnd_2220519 := by
    simpa [prefixWord, tailWord_2220519, baseEnd_2220519] using wordTrace_append hprefix tailTrace_2220519
  have hstable : (prefixWord ++ tailWord_2220519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2220519).length < 2 ^ (prefixWord ++ tailWord_2220519).sum := by decide
  have hdescent : baseEnd_2220519 < baseStart_2220519 := by decide
  rcases family_descends (prefixWord ++ tailWord_2220519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2220533 : List Nat := [1, 3, 5, 1, 2, 1, 2, 3, 5]
def baseStart_2220533 : Nat := 118140960795 + 2220533 * 2 ^ 59
def prefixEnd_2220533 : Nat := 4983230072969 + 3 ^ 40 * 2220533 * 2
def baseEnd_2220533 : Nat := 126688970907807320902829

theorem tailTrace_2220533 : CollatzResearch.WordTrace tailWord_2220533 prefixEnd_2220533 126688970907807320902829 := by
  unfold tailWord_2220533
  simp only [CollatzResearch.WordTrace]
  refine ⟨80989492064395652688922253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53992994709597101792614835 80989492064395652688922253)
  ·
    refine ⟨30371059524148369758345845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 80989492064395652688922253 30371059524148369758345845)
    ·
      refine ⟨2847286830388909664844923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 30371059524148369758345845 2847286830388909664844923)
      ·
        refine ⟨4270930245583364497267385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2847286830388909664844923 4270930245583364497267385)
        ·
          refine ⟨3203197684187523372950539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4270930245583364497267385 3203197684187523372950539)
          ·
            refine ⟨4804796526281285059425809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3203197684187523372950539 4804796526281285059425809)
            ·
              refine ⟨3603597394710963794569357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4804796526281285059425809 3603597394710963794569357)
              ·
                refine ⟨1351349023016611422963509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3603597394710963794569357 1351349023016611422963509)
                ·
                  refine ⟨126688970907807320902829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1351349023016611422963509 126688970907807320902829)
                  ·
                    rfl

theorem cell23_2220533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 2, 3, 5].length) (baseStart_2220533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2220533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2220533 prefixEnd_2220533 := by exact prefixLift 2220533
  have htrace : WordTrace (prefixWord ++ tailWord_2220533) baseStart_2220533 baseEnd_2220533 := by
    simpa [prefixWord, tailWord_2220533, baseEnd_2220533] using wordTrace_append hprefix tailTrace_2220533
  have hstable : (prefixWord ++ tailWord_2220533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2220533).length < 2 ^ (prefixWord ++ tailWord_2220533).sum := by decide
  have hdescent : baseEnd_2220533 < baseStart_2220533 := by decide
  rcases family_descends (prefixWord ++ tailWord_2220533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2220549 : List Nat := [1, 3, 1, 1, 2, 2, 3, 2, 2, 4, 2]
def baseStart_2220549 : Nat := 118140960795 + 2220549 * 2 ^ 59
def prefixEnd_2220549 : Nat := 4983230072969 + 3 ^ 40 * 2220549 * 2
def baseEnd_2220549 : Nat := 1140208953860737825525387

theorem tailTrace_2220549 : CollatzResearch.WordTrace tailWord_2220549 prefixEnd_2220549 1140208953860737825525387 := by
  unfold tailWord_2220549
  simp only [CollatzResearch.WordTrace]
  refine ⟨80990075632337687421504701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53993383754891791614336467 80990075632337687421504701)
  ·
    refine ⟨30371278362126632783064263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 80990075632337687421504701 30371278362126632783064263)
    ·
      refine ⟨45556917543189949174596395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30371278362126632783064263 45556917543189949174596395)
      ·
        refine ⟨68335376314784923761894593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45556917543189949174596395 68335376314784923761894593)
        ·
          refine ⟨51251532236088692821420945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 68335376314784923761894593 51251532236088692821420945)
          ·
            refine ⟨38438649177066519616065709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51251532236088692821420945 38438649177066519616065709)
            ·
              refine ⟨14414493441399944856024641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38438649177066519616065709 14414493441399944856024641)
              ·
                refine ⟨10810870081049958642018481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14414493441399944856024641 10810870081049958642018481)
                ·
                  refine ⟨8108152560787468981513861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10810870081049958642018481 8108152560787468981513861)
                  ·
                    refine ⟨1520278605147650434033849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8108152560787468981513861 1520278605147650434033849)
                    ·
                      refine ⟨1140208953860737825525387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1520278605147650434033849 1140208953860737825525387)
                      ·
                        rfl

theorem cell23_2220549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 3, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 3, 2, 2, 4, 2].length) (baseStart_2220549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2220549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2220549 prefixEnd_2220549 := by exact prefixLift 2220549
  have htrace : WordTrace (prefixWord ++ tailWord_2220549) baseStart_2220549 baseEnd_2220549 := by
    simpa [prefixWord, tailWord_2220549, baseEnd_2220549] using wordTrace_append hprefix tailTrace_2220549
  have hstable : (prefixWord ++ tailWord_2220549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2220549).length < 2 ^ (prefixWord ++ tailWord_2220549).sum := by decide
  have hdescent : baseEnd_2220549 < baseStart_2220549 := by decide
  rcases family_descends (prefixWord ++ tailWord_2220549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2220550 : List Nat := [6, 2, 1, 1, 1, 1, 2, 4, 5]
def baseStart_2220550 : Nat := 118140960795 + 2220550 * 2 ^ 59
def prefixEnd_2220550 : Nat := 4983230072969 + 3 ^ 40 * 2220550 * 2
def baseEnd_2220550 : Nat := 126689940815710257956987

theorem tailTrace_2220550 : CollatzResearch.WordTrace tailWord_2220550 prefixEnd_2220550 126689940815710257956987 := by
  unfold tailWord_2220550
  simp only [CollatzResearch.WordTrace]
  refine ⟨2530941003291689518509097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 53993408070222709728194069 2530941003291689518509097)
  ·
    refine ⟨1898205752468767138881823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2530941003291689518509097 1898205752468767138881823)
    ·
      refine ⟨2847308628703150708322735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1898205752468767138881823 2847308628703150708322735)
      ·
        refine ⟨4270962943054726062484103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2847308628703150708322735 4270962943054726062484103)
        ·
          refine ⟨6406444414582089093726155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4270962943054726062484103 6406444414582089093726155)
          ·
            refine ⟨9609666621873133640589233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6406444414582089093726155 9609666621873133640589233)
            ·
              refine ⟨7207249966404850230441925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9609666621873133640589233 7207249966404850230441925)
              ·
                refine ⟨1351359368700909418207861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7207249966404850230441925 1351359368700909418207861)
                ·
                  refine ⟨126689940815710257956987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1351359368700909418207861 126689940815710257956987)
                  ·
                    rfl

theorem cell23_2220550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 2, 4, 5].length) (baseStart_2220550 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2220550 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2220550 prefixEnd_2220550 := by exact prefixLift 2220550
  have htrace : WordTrace (prefixWord ++ tailWord_2220550) baseStart_2220550 baseEnd_2220550 := by
    simpa [prefixWord, tailWord_2220550, baseEnd_2220550] using wordTrace_append hprefix tailTrace_2220550
  have hstable : (prefixWord ++ tailWord_2220550).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2220550).length < 2 ^ (prefixWord ++ tailWord_2220550).sum := by decide
  have hdescent : baseEnd_2220550 < baseStart_2220550 := by decide
  rcases family_descends (prefixWord ++ tailWord_2220550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2220626 : List Nat := [3, 2, 2, 1, 2, 1, 1, 2, 4, 3, 2]
def baseStart_2220626 : Nat := 118140960795 + 2220626 * 2 ^ 59
def prefixEnd_2220626 : Nat := 4983230072969 + 3 ^ 40 * 2220626 * 2
def baseEnd_2220626 : Nat := 1140248491871134024262533

theorem tailTrace_2220626 : CollatzResearch.WordTrace tailWord_2220626 prefixEnd_2220626 1140248491871134024262533 := by
  unfold tailWord_2220626
  simp only [CollatzResearch.WordTrace]
  refine ⟨20248221013264682393014433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53995256035372486381371821 20248221013264682393014433)
  ·
    refine ⟨15186165759948511794760825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20248221013264682393014433 15186165759948511794760825)
    ·
      refine ⟨11389624319961383846070619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15186165759948511794760825 11389624319961383846070619)
      ·
        refine ⟨17084436479942075769105929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11389624319961383846070619 17084436479942075769105929)
        ·
          refine ⟨12813327359956556826829447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17084436479942075769105929 12813327359956556826829447)
          ·
            refine ⟨19219991039934835240244171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12813327359956556826829447 19219991039934835240244171)
            ·
              refine ⟨28829986559902252860366257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19219991039934835240244171 28829986559902252860366257)
              ·
                refine ⟨21622489919926689645274693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28829986559902252860366257 21622489919926689645274693)
                ·
                  refine ⟨4054216859986254308489005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21622489919926689645274693 4054216859986254308489005)
                  ·
                    refine ⟨1520331322494845365683377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4054216859986254308489005 1520331322494845365683377)
                    ·
                      refine ⟨1140248491871134024262533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1520331322494845365683377 1140248491871134024262533)
                      ·
                        rfl

theorem cell23_2220626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 2, 4, 3, 2].length) (baseStart_2220626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2220626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2220626 prefixEnd_2220626 := by exact prefixLift 2220626
  have htrace : WordTrace (prefixWord ++ tailWord_2220626) baseStart_2220626 baseEnd_2220626 := by
    simpa [prefixWord, tailWord_2220626, baseEnd_2220626] using wordTrace_append hprefix tailTrace_2220626
  have hstable : (prefixWord ++ tailWord_2220626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2220626).length < 2 ^ (prefixWord ++ tailWord_2220626).sum := by decide
  have hdescent : baseEnd_2220626 < baseStart_2220626 := by decide
  rcases family_descends (prefixWord ++ tailWord_2220626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2220636 : List Nat := [2, 2, 4, 1, 3, 1, 1, 1, 3, 5]
def baseStart_2220636 : Nat := 118140960795 + 2220636 * 2 ^ 59
def prefixEnd_2220636 : Nat := 4983230072969 + 3 ^ 40 * 2220636 * 2
def baseEnd_2220636 : Nat := 380084542225892995045829

theorem tailTrace_2220636 : CollatzResearch.WordTrace tailWord_2220636 prefixEnd_2220636 380084542225892995045829 := by
  unfold tailWord_2220636
  simp only [CollatzResearch.WordTrace]
  refine ⟨40496624391511250639960881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53995499188681667519947841 40496624391511250639960881)
  ·
    refine ⟨30372468293633437979970661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40496624391511250639960881 30372468293633437979970661)
    ·
      refine ⟨5694837805056269621244499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 30372468293633437979970661 5694837805056269621244499)
      ·
        refine ⟨8542256707584404431866749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5694837805056269621244499 8542256707584404431866749)
        ·
          refine ⟨3203346265344151661950031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8542256707584404431866749 3203346265344151661950031)
          ·
            refine ⟨4805019398016227492925047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3203346265344151661950031 4805019398016227492925047)
            ·
              refine ⟨7207529097024341239387571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4805019398016227492925047 7207529097024341239387571)
              ·
                refine ⟨10811293645536511859081357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7207529097024341239387571 10811293645536511859081357)
                ·
                  refine ⟨4054235117076191947155509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10811293645536511859081357 4054235117076191947155509)
                  ·
                    refine ⟨380084542225892995045829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4054235117076191947155509 380084542225892995045829)
                    ·
                      rfl

theorem cell23_2220636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 1, 1, 3, 5].length) (baseStart_2220636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2220636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2220636 prefixEnd_2220636 := by exact prefixLift 2220636
  have htrace : WordTrace (prefixWord ++ tailWord_2220636) baseStart_2220636 baseEnd_2220636 := by
    simpa [prefixWord, tailWord_2220636, baseEnd_2220636] using wordTrace_append hprefix tailTrace_2220636
  have hstable : (prefixWord ++ tailWord_2220636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2220636).length < 2 ^ (prefixWord ++ tailWord_2220636).sum := by decide
  have hdescent : baseEnd_2220636 < baseStart_2220636 := by decide
  rcases family_descends (prefixWord ++ tailWord_2220636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2220639 : List Nat := [1, 1, 2, 3, 1, 1, 1, 3, 2, 6, 2]
def baseStart_2220639 : Nat := 118140960795 + 2220639 * 2 ^ 59
def prefixEnd_2220639 : Nat := 4983230072969 + 3 ^ 40 * 2220639 * 2
def baseEnd_2220639 : Nat := 1140255167119642473399973

theorem tailTrace_2220639 : CollatzResearch.WordTrace tailWord_2220639 prefixEnd_2220639 1140255167119642473399973 := by
  unfold tailWord_2220639
  simp only [CollatzResearch.WordTrace]
  refine ⟨80993358202011632792280971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53995572134674421861520647 80993358202011632792280971)
  ·
    refine ⟨121490037303017449188421457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80993358202011632792280971 121490037303017449188421457)
    ·
      refine ⟨91117527977263086891316093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 121490037303017449188421457 91117527977263086891316093)
      ·
        refine ⟨34169072991473657584243535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 91117527977263086891316093 34169072991473657584243535)
        ·
          refine ⟨51253609487210486376365303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34169072991473657584243535 51253609487210486376365303)
          ·
            refine ⟨76880414230815729564547955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51253609487210486376365303 76880414230815729564547955)
            ·
              refine ⟨115320621346223594346821933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 76880414230815729564547955 115320621346223594346821933)
              ·
                refine ⟨43245233004833847880058225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 115320621346223594346821933 43245233004833847880058225)
                ·
                  refine ⟨32433924753625385910043669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 43245233004833847880058225 32433924753625385910043669)
                  ·
                    refine ⟨1520340222826189964533297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 32433924753625385910043669 1520340222826189964533297)
                    ·
                      refine ⟨1140255167119642473399973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1520340222826189964533297 1140255167119642473399973)
                      ·
                        rfl

theorem cell23_2220639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 3, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 3, 2, 6, 2].length) (baseStart_2220639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2220639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2220639 prefixEnd_2220639 := by exact prefixLift 2220639
  have htrace : WordTrace (prefixWord ++ tailWord_2220639) baseStart_2220639 baseEnd_2220639 := by
    simpa [prefixWord, tailWord_2220639, baseEnd_2220639] using wordTrace_append hprefix tailTrace_2220639
  have hstable : (prefixWord ++ tailWord_2220639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2220639).length < 2 ^ (prefixWord ++ tailWord_2220639).sum := by decide
  have hdescent : baseEnd_2220639 < baseStart_2220639 := by decide
  rcases family_descends (prefixWord ++ tailWord_2220639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2220653 : List Nat := [1, 5, 1, 1, 3, 2, 3, 1, 1, 5]
def baseStart_2220653 : Nat := 118140960795 + 2220653 * 2 ^ 59
def prefixEnd_2220653 : Nat := 4983230072969 + 3 ^ 40 * 2220653 * 2
def baseEnd_2220653 : Nat := 380087451949601806208303

theorem tailTrace_2220653 : CollatzResearch.WordTrace tailWord_2220653 prefixEnd_2220653 380087451949601806208303 := by
  unfold tailWord_2220653
  simp only [CollatzResearch.WordTrace]
  refine ⟨80993868823960913183290613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53995912549307275455527075 80993868823960913183290613)
  ·
    refine ⟨7593175202246335610933495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 80993868823960913183290613 7593175202246335610933495)
    ·
      refine ⟨11389762803369503416400243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7593175202246335610933495 11389762803369503416400243)
      ·
        refine ⟨17084644205054255124600365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11389762803369503416400243 17084644205054255124600365)
        ·
          refine ⟨6406741576895345671725137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17084644205054255124600365 6406741576895345671725137)
          ·
            refine ⟨4805056182671509253793853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6406741576895345671725137 4805056182671509253793853)
            ·
              refine ⟨1801896068501815970172695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4805056182671509253793853 1801896068501815970172695)
              ·
                refine ⟨2702844102752723955259043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1801896068501815970172695 2702844102752723955259043)
                ·
                  refine ⟨4054266154129085932888565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2702844102752723955259043 4054266154129085932888565)
                  ·
                    refine ⟨380087451949601806208303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4054266154129085932888565 380087451949601806208303)
                    ·
                      rfl

theorem cell23_2220653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 3, 1, 1, 5].length) (baseStart_2220653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2220653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2220653 prefixEnd_2220653 := by exact prefixLift 2220653
  have htrace : WordTrace (prefixWord ++ tailWord_2220653) baseStart_2220653 baseEnd_2220653 := by
    simpa [prefixWord, tailWord_2220653, baseEnd_2220653] using wordTrace_append hprefix tailTrace_2220653
  have hstable : (prefixWord ++ tailWord_2220653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2220653).length < 2 ^ (prefixWord ++ tailWord_2220653).sum := by decide
  have hdescent : baseEnd_2220653 < baseStart_2220653 := by decide
  rcases family_descends (prefixWord ++ tailWord_2220653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2220673 : List Nat := [1, 2, 4, 2, 1, 1, 2, 3, 3, 2, 2]
def baseStart_2220673 : Nat := 118140960795 + 2220673 * 2 ^ 59
def prefixEnd_2220673 : Nat := 4983230072969 + 3 ^ 40 * 2220673 * 2
def baseEnd_2220673 : Nat := 1140272625461895340374817

theorem tailTrace_2220673 : CollatzResearch.WordTrace tailWord_2220673 prefixEnd_2220673 1140272625461895340374817 := by
  unfold tailWord_2220673
  simp only [CollatzResearch.WordTrace]
  refine ⟨80994598283888456599018673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53996398855925637732679115 80994598283888456599018673)
  ·
    refine ⟨60745948712916342449264005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80994598283888456599018673 60745948712916342449264005)
    ·
      refine ⟨11389865383671814209237001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 60745948712916342449264005 11389865383671814209237001)
      ·
        refine ⟨8542399037753860656927751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11389865383671814209237001 8542399037753860656927751)
        ·
          refine ⟨12813598556630790985391627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8542399037753860656927751 12813598556630790985391627)
          ·
            refine ⟨19220397834946186478087441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12813598556630790985391627 19220397834946186478087441)
            ·
              refine ⟨14415298376209639858565581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19220397834946186478087441 14415298376209639858565581)
              ·
                refine ⟨5405736891078614946962093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14415298376209639858565581 5405736891078614946962093)
                ·
                  refine ⟨2027151334154480605110785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5405736891078614946962093 2027151334154480605110785)
                  ·
                    refine ⟨1520363500615860453833089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2027151334154480605110785 1520363500615860453833089)
                    ·
                      refine ⟨1140272625461895340374817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1520363500615860453833089 1140272625461895340374817)
                      ·
                        rfl

theorem cell23_2220673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 2, 3, 3, 2, 2].length) (baseStart_2220673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2220673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2220673 prefixEnd_2220673 := by exact prefixLift 2220673
  have htrace : WordTrace (prefixWord ++ tailWord_2220673) baseStart_2220673 baseEnd_2220673 := by
    simpa [prefixWord, tailWord_2220673, baseEnd_2220673] using wordTrace_append hprefix tailTrace_2220673
  have hstable : (prefixWord ++ tailWord_2220673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2220673).length < 2 ^ (prefixWord ++ tailWord_2220673).sum := by decide
  have hdescent : baseEnd_2220673 < baseStart_2220673 := by decide
  rcases family_descends (prefixWord ++ tailWord_2220673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2220676 : List Nat := [2, 3, 2, 1, 3, 1, 1, 2, 3, 2, 3]
def baseStart_2220676 : Nat := 118140960795 + 2220676 * 2 ^ 59
def prefixEnd_2220676 : Nat := 4983230072969 + 3 ^ 40 * 2220676 * 2
def baseEnd_2220676 : Nat := 1140274165903858828637303

theorem tailTrace_2220676 : CollatzResearch.WordTrace tailWord_2220676 prefixEnd_2220676 1140274165903858828637303 := by
  unfold tailWord_2220676
  simp only [CollatzResearch.WordTrace]
  refine ⟨40497353851438794055688941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53996471801918392074251921 40497353851438794055688941)
  ·
    refine ⟨15186507694289547770883353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40497353851438794055688941 15186507694289547770883353)
    ·
      refine ⟨11389880770717160828162515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15186507694289547770883353 11389880770717160828162515)
      ·
        refine ⟨17084821156075741242243773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11389880770717160828162515 17084821156075741242243773)
        ·
          refine ⟨6406807933528402965841415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17084821156075741242243773 6406807933528402965841415)
          ·
            refine ⟨9610211900292604448762123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6406807933528402965841415 9610211900292604448762123)
            ·
              refine ⟨14415317850438906673143185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9610211900292604448762123 14415317850438906673143185)
              ·
                refine ⟨10811488387829180004857389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14415317850438906673143185 10811488387829180004857389)
                ·
                  refine ⟨4054308145435942501821521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10811488387829180004857389 4054308145435942501821521)
                  ·
                    refine ⟨3040731109076956876366141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4054308145435942501821521 3040731109076956876366141)
                    ·
                      refine ⟨1140274165903858828637303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3040731109076956876366141 1140274165903858828637303)
                      ·
                        rfl

theorem cell23_2220676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 1, 2, 3, 2, 3].length) (baseStart_2220676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2220676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2220676 prefixEnd_2220676 := by exact prefixLift 2220676
  have htrace : WordTrace (prefixWord ++ tailWord_2220676) baseStart_2220676 baseEnd_2220676 := by
    simpa [prefixWord, tailWord_2220676, baseEnd_2220676] using wordTrace_append hprefix tailTrace_2220676
  have hstable : (prefixWord ++ tailWord_2220676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2220676).length < 2 ^ (prefixWord ++ tailWord_2220676).sum := by decide
  have hdescent : baseEnd_2220676 < baseStart_2220676 := by decide
  rcases family_descends (prefixWord ++ tailWord_2220676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2220686 : List Nat := [4, 1, 1, 3, 1, 1, 4, 1, 1, 2, 4]
def baseStart_2220686 : Nat := 118140960795 + 2220686 * 2 ^ 59
def prefixEnd_2220686 : Nat := 4983230072969 + 3 ^ 40 * 2220686 * 2
def baseEnd_2220686 : Nat := 1140279300710403789512257

theorem tailTrace_2220686 : CollatzResearch.WordTrace tailWord_2220686 prefixEnd_2220686 1140279300710403789512257 := by
  unfold tailWord_2220686
  simp only [CollatzResearch.WordTrace]
  refine ⟨10124384054105169977405239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 53996714955227573212827941 10124384054105169977405239)
  ·
    refine ⟨15186576081157754966107859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10124384054105169977405239 15186576081157754966107859)
    ·
      refine ⟨22779864121736632449161789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15186576081157754966107859 22779864121736632449161789)
      ·
        refine ⟨8542449045651237168435671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22779864121736632449161789 8542449045651237168435671)
        ·
          refine ⟨12813673568476855752653507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8542449045651237168435671 12813673568476855752653507)
          ·
            refine ⟨19220510352715283628980261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12813673568476855752653507 19220510352715283628980261)
            ·
              refine ⟨3603845691134115680433799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19220510352715283628980261 3603845691134115680433799)
              ·
                refine ⟨5405768536701173520650699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3603845691134115680433799 5405768536701173520650699)
                ·
                  refine ⟨8108652805051760280976049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5405768536701173520650699 8108652805051760280976049)
                  ·
                    refine ⟨6081489603788820210732037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8108652805051760280976049 6081489603788820210732037)
                    ·
                      refine ⟨1140279300710403789512257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6081489603788820210732037 1140279300710403789512257)
                      ·
                        rfl

theorem cell23_2220686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 4, 1, 1, 2, 4].length) (baseStart_2220686 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2220686 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2220686 prefixEnd_2220686 := by exact prefixLift 2220686
  have htrace : WordTrace (prefixWord ++ tailWord_2220686) baseStart_2220686 baseEnd_2220686 := by
    simpa [prefixWord, tailWord_2220686, baseEnd_2220686] using wordTrace_append hprefix tailTrace_2220686
  have hstable : (prefixWord ++ tailWord_2220686).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2220686).length < 2 ^ (prefixWord ++ tailWord_2220686).sum := by decide
  have hdescent : baseEnd_2220686 < baseStart_2220686 := by decide
  rcases family_descends (prefixWord ++ tailWord_2220686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2220690 : List Nat := [3, 2, 3, 1, 2, 2, 1, 2, 3, 2, 2]
def baseStart_2220690 : Nat := 118140960795 + 2220690 * 2 ^ 59
def prefixEnd_2220690 : Nat := 4983230072969 + 3 ^ 40 * 2220690 * 2
def baseEnd_2220690 : Nat := 1140281354633021773862239

theorem tailTrace_2220690 : CollatzResearch.WordTrace tailWord_2220690 prefixEnd_2220690 1140281354633021773862239 := by
  unfold tailWord_2220690
  simp only [CollatzResearch.WordTrace]
  refine ⟨20248804581206717125596881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53996812216551245668258349 20248804581206717125596881)
  ·
    refine ⟨15186603435905037844197661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20248804581206717125596881 15186603435905037844197661)
    ·
      refine ⟨5694976288464389191574123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15186603435905037844197661 5694976288464389191574123)
      ·
        refine ⟨8542464432696583787361185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5694976288464389191574123 8542464432696583787361185)
        ·
          refine ⟨6406848324522437840520889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8542464432696583787361185 6406848324522437840520889)
          ·
            refine ⟨4805136243391828380390667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6406848324522437840520889 4805136243391828380390667)
            ·
              refine ⟨7207704365087742570586001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4805136243391828380390667 7207704365087742570586001)
              ·
                refine ⟨5405778273815806927939501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7207704365087742570586001 5405778273815806927939501)
                ·
                  refine ⟨2027166852680927597977313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5405778273815806927939501 2027166852680927597977313)
                  ·
                    refine ⟨1520375139510695698482985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2027166852680927597977313 1520375139510695698482985)
                    ·
                      refine ⟨1140281354633021773862239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1520375139510695698482985 1140281354633021773862239)
                      ·
                        rfl

theorem cell23_2220690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 1, 2, 3, 2, 2].length) (baseStart_2220690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2220690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2220690 prefixEnd_2220690 := by exact prefixLift 2220690
  have htrace : WordTrace (prefixWord ++ tailWord_2220690) baseStart_2220690 baseEnd_2220690 := by
    simpa [prefixWord, tailWord_2220690, baseEnd_2220690] using wordTrace_append hprefix tailTrace_2220690
  have hstable : (prefixWord ++ tailWord_2220690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2220690).length < 2 ^ (prefixWord ++ tailWord_2220690).sum := by decide
  have hdescent : baseEnd_2220690 < baseStart_2220690 := by decide
  rcases family_descends (prefixWord ++ tailWord_2220690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2220723 : List Nat := [1, 1, 1, 2, 3, 4, 3, 2, 2, 1, 3]
def baseStart_2220723 : Nat := 118140960795 + 2220723 * 2 ^ 59
def prefixEnd_2220723 : Nat := 4983230072969 + 3 ^ 40 * 2220723 * 2
def baseEnd_2220723 : Nat := 1140298299494620144749587

theorem tailTrace_2220723 : CollatzResearch.WordTrace tailWord_2220723 prefixEnd_2220723 1140298299494620144749587 := by
  unfold tailWord_2220723
  simp only [CollatzResearch.WordTrace]
  refine ⟨80996421933707315138338823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53997614622471543425559215 80996421933707315138338823)
  ·
    refine ⟨121494632900560972707508235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80996421933707315138338823 121494632900560972707508235)
    ·
      refine ⟨182241949350841459061262353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121494632900560972707508235 182241949350841459061262353)
      ·
        refine ⟨136681462013131094295946765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 182241949350841459061262353 136681462013131094295946765)
        ·
          refine ⟨51255548254924160360980037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 136681462013131094295946765 51255548254924160360980037)
          ·
            refine ⟨9610415297798280067683757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 51255548254924160360980037 9610415297798280067683757)
            ·
              refine ⟨3603905736674355025381409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9610415297798280067683757 3603905736674355025381409)
              ·
                refine ⟨2702929302505766269036057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3603905736674355025381409 2702929302505766269036057)
                ·
                  refine ⟨2027196976879324701777043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2702929302505766269036057 2027196976879324701777043)
                  ·
                    refine ⟨3040795465318987052665565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2027196976879324701777043 3040795465318987052665565)
                    ·
                      refine ⟨1140298299494620144749587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3040795465318987052665565 1140298299494620144749587)
                      ·
                        rfl

theorem cell23_2220723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 3, 2, 2, 1, 3].length) (baseStart_2220723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2220723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2220723 prefixEnd_2220723 := by exact prefixLift 2220723
  have htrace : WordTrace (prefixWord ++ tailWord_2220723) baseStart_2220723 baseEnd_2220723 := by
    simpa [prefixWord, tailWord_2220723, baseEnd_2220723] using wordTrace_append hprefix tailTrace_2220723
  have hstable : (prefixWord ++ tailWord_2220723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2220723).length < 2 ^ (prefixWord ++ tailWord_2220723).sum := by decide
  have hdescent : baseEnd_2220723 < baseStart_2220723 := by decide
  rcases family_descends (prefixWord ++ tailWord_2220723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2220737 : List Nat := [1, 2, 6, 2, 2, 1, 1, 1, 1, 2, 4]
def baseStart_2220737 : Nat := 118140960795 + 2220737 * 2 ^ 59
def prefixEnd_2220737 : Nat := 4983230072969 + 3 ^ 40 * 2220737 * 2
def baseEnd_2220737 : Nat := 1140305488223783089974523

theorem tailTrace_2220737 : CollatzResearch.WordTrace tailWord_2220737 prefixEnd_2220737 1140305488223783089974523 := by
  unfold tailWord_2220737
  simp only [CollatzResearch.WordTrace]
  refine ⟨80996932555656595529348465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53997955037104397019565643 80996932555656595529348465)
  ·
    refine ⟨60747699416742446647011349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80996932555656595529348465 60747699416742446647011349)
    ·
      refine ⟨2847548410159802186578657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 60747699416742446647011349 2847548410159802186578657)
      ·
        refine ⟨2135661307619851639933993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2847548410159802186578657 2135661307619851639933993)
        ·
          refine ⟨1601745980714888729950495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2135661307619851639933993 1601745980714888729950495)
          ·
            refine ⟨2402618971072333094925743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1601745980714888729950495 2402618971072333094925743)
            ·
              refine ⟨3603928456608499642388615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2402618971072333094925743 3603928456608499642388615)
              ·
                refine ⟨5405892684912749463582923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3603928456608499642388615 5405892684912749463582923)
                ·
                  refine ⟨8108839027369124195374385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5405892684912749463582923 8108839027369124195374385)
                  ·
                    refine ⟨6081629270526843146530789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8108839027369124195374385 6081629270526843146530789)
                    ·
                      refine ⟨1140305488223783089974523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6081629270526843146530789 1140305488223783089974523)
                      ·
                        rfl

theorem cell23_2220737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 2, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 2, 1, 1, 1, 1, 2, 4].length) (baseStart_2220737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2220737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2220737 prefixEnd_2220737 := by exact prefixLift 2220737
  have htrace : WordTrace (prefixWord ++ tailWord_2220737) baseStart_2220737 baseEnd_2220737 := by
    simpa [prefixWord, tailWord_2220737, baseEnd_2220737] using wordTrace_append hprefix tailTrace_2220737
  have hstable : (prefixWord ++ tailWord_2220737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2220737).length < 2 ^ (prefixWord ++ tailWord_2220737).sum := by decide
  have hdescent : baseEnd_2220737 < baseStart_2220737 := by decide
  rcases family_descends (prefixWord ++ tailWord_2220737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2220750 : List Nat := [4, 1, 1, 1, 3, 3, 2, 2, 1, 3, 2]
def baseStart_2220750 : Nat := 118140960795 + 2220750 * 2 ^ 59
def prefixEnd_2220750 : Nat := 4983230072969 + 3 ^ 40 * 2220750 * 2
def baseEnd_2220750 : Nat := 1140312163472291539111963

theorem tailTrace_2220750 : CollatzResearch.WordTrace tailWord_2220750 prefixEnd_2220750 1140312163472291539111963 := by
  unfold tailWord_2220750
  simp only [CollatzResearch.WordTrace]
  refine ⟨10124675838076187343696463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 53998271136406332499714469 10124675838076187343696463)
  ·
    refine ⟨15187013757114281015544695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10124675838076187343696463 15187013757114281015544695)
    ·
      refine ⟨22780520635671421523317043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15187013757114281015544695 22780520635671421523317043)
      ·
        refine ⟨34170780953507132284975565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22780520635671421523317043 34170780953507132284975565)
        ·
          refine ⟨12814042857565174606865837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34170780953507132284975565 12814042857565174606865837)
          ·
            refine ⟨4805266071586940477574689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12814042857565174606865837 4805266071586940477574689)
            ·
              refine ⟨3603949553690205358181017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4805266071586940477574689 3603949553690205358181017)
              ·
                refine ⟨2702962165267654018635763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3603949553690205358181017 2702962165267654018635763)
                ·
                  refine ⟨4054443247901481027953645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2702962165267654018635763 4054443247901481027953645)
                  ·
                    refine ⟨1520416217963055385482617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4054443247901481027953645 1520416217963055385482617)
                    ·
                      refine ⟨1140312163472291539111963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1520416217963055385482617 1140312163472291539111963)
                      ·
                        rfl

theorem cell23_2220750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 2, 2, 1, 3, 2].length) (baseStart_2220750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2220750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2220750 prefixEnd_2220750 := by exact prefixLift 2220750
  have htrace : WordTrace (prefixWord ++ tailWord_2220750) baseStart_2220750 baseEnd_2220750 := by
    simpa [prefixWord, tailWord_2220750, baseEnd_2220750] using wordTrace_append hprefix tailTrace_2220750
  have hstable : (prefixWord ++ tailWord_2220750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2220750).length < 2 ^ (prefixWord ++ tailWord_2220750).sum := by decide
  have hdescent : baseEnd_2220750 < baseStart_2220750 := by decide
  rcases family_descends (prefixWord ++ tailWord_2220750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2220786 : List Nat := [3, 2, 1, 3, 1, 2, 3, 1, 7]
def baseStart_2220786 : Nat := 118140960795 + 2220786 * 2 ^ 59
def prefixEnd_2220786 : Nat := 4983230072969 + 3 ^ 40 * 2220786 * 2
def baseEnd_2220786 : Nat := 126703405419539266473533

theorem tailTrace_2220786 : CollatzResearch.WordTrace tailWord_2220786 prefixEnd_2220786 126703405419539266473533 := by
  unfold tailWord_2220786
  simp only [CollatzResearch.WordTrace]
  refine ⟨20249679933119769224470553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53999146488319384598588141 20249679933119769224470553)
  ·
    refine ⟨15187259949839826918352915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20249679933119769224470553 15187259949839826918352915)
    ·
      refine ⟨22780889924759740377529373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15187259949839826918352915 22780889924759740377529373)
      ·
        refine ⟨8542833721784902641573515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22780889924759740377529373 8542833721784902641573515)
        ·
          refine ⟨12814250582677353962360273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8542833721784902641573515 12814250582677353962360273)
          ·
            refine ⟨9610687937008015471770205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12814250582677353962360273 9610687937008015471770205)
            ·
              refine ⟨3604007976378005801913827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9610687937008015471770205 3604007976378005801913827)
              ·
                refine ⟨5406011964567008702870741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3604007976378005801913827 5406011964567008702870741)
                ·
                  refine ⟨126703405419539266473533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5406011964567008702870741 126703405419539266473533)
                  ·
                    rfl

theorem cell23_2220786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 3, 1, 7].length) (baseStart_2220786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2220786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2220786 prefixEnd_2220786 := by exact prefixLift 2220786
  have htrace : WordTrace (prefixWord ++ tailWord_2220786) baseStart_2220786 baseEnd_2220786 := by
    simpa [prefixWord, tailWord_2220786, baseEnd_2220786] using wordTrace_append hprefix tailTrace_2220786
  have hstable : (prefixWord ++ tailWord_2220786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2220786).length < 2 ^ (prefixWord ++ tailWord_2220786).sum := by decide
  have hdescent : baseEnd_2220786 < baseStart_2220786 := by decide
  rcases family_descends (prefixWord ++ tailWord_2220786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2220799 : List Nat := [1, 1, 2, 2, 1, 3, 1, 1, 6, 5]
def baseStart_2220799 : Nat := 118140960795 + 2220799 * 2 ^ 59
def prefixEnd_2220799 : Nat := 4983230072969 + 3 ^ 40 * 2220799 * 2
def baseEnd_2220799 : Nat := 380112441341453949133079

theorem tailTrace_2220799 : CollatzResearch.WordTrace tailWord_2220799 prefixEnd_2220799 380112441341453949133079 := by
  unfold tailWord_2220799
  simp only [CollatzResearch.WordTrace]
  refine ⟨80999193881431980118105451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53999462587621320078736967 80999193881431980118105451)
  ·
    refine ⟨121498790822147970177158177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80999193881431980118105451 121498790822147970177158177)
    ·
      refine ⟨91124093116610977632868633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 121498790822147970177158177 91124093116610977632868633)
      ·
        refine ⟨68343069837458233224651475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 91124093116610977632868633 68343069837458233224651475)
        ·
          refine ⟨102514604756187349836977213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68343069837458233224651475 102514604756187349836977213)
          ·
            refine ⟨38442976783570256188866455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 102514604756187349836977213 38442976783570256188866455)
            ·
              refine ⟨57664465175355384283299683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38442976783570256188866455 57664465175355384283299683)
              ·
                refine ⟨86496697763033076424949525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 57664465175355384283299683 86496697763033076424949525)
                ·
                  refine ⟨4054532707642175457419509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 86496697763033076424949525 4054532707642175457419509)
                  ·
                    refine ⟨380112441341453949133079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4054532707642175457419509 380112441341453949133079)
                    ·
                      rfl

theorem cell23_2220799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 1, 6, 5].length) (baseStart_2220799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2220799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2220799 prefixEnd_2220799 := by exact prefixLift 2220799
  have htrace : WordTrace (prefixWord ++ tailWord_2220799) baseStart_2220799 baseEnd_2220799 := by
    simpa [prefixWord, tailWord_2220799, baseEnd_2220799] using wordTrace_append hprefix tailTrace_2220799
  have hstable : (prefixWord ++ tailWord_2220799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2220799).length < 2 ^ (prefixWord ++ tailWord_2220799).sum := by decide
  have hdescent : baseEnd_2220799 < baseStart_2220799 := by decide
  rcases family_descends (prefixWord ++ tailWord_2220799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2220853 : List Nat := [1, 3, 3, 1, 3, 1, 1, 1, 1, 6, 2]
def baseStart_2220853 : Nat := 118140960795 + 2220853 * 2 ^ 59
def prefixEnd_2220853 : Nat := 4983230072969 + 3 ^ 40 * 2220853 * 2
def baseEnd_2220853 : Nat := 1140365051979704636123989

theorem tailTrace_2220853 : CollatzResearch.WordTrace tailWord_2220853 prefixEnd_2220853 1140365051979704636123989 := by
  unfold tailWord_2220853
  simp only [CollatzResearch.WordTrace]
  refine ⟨81001163423236347340571213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54000775615490898227047475 81001163423236347340571213)
  ·
    refine ⟨30375436283713630252714205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 81001163423236347340571213 30375436283713630252714205)
    ·
      refine ⟨11390788606392611344767827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30375436283713630252714205 11390788606392611344767827)
      ·
        refine ⟨17086182909588917017151741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11390788606392611344767827 17086182909588917017151741)
        ·
          refine ⟨6407318591095843881431903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17086182909588917017151741 6407318591095843881431903)
          ·
            refine ⟨9610977886643765822147855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6407318591095843881431903 9610977886643765822147855)
            ·
              refine ⟨14416466829965648733221783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9610977886643765822147855 14416466829965648733221783)
              ·
                refine ⟨21624700244948473099832675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14416466829965648733221783 21624700244948473099832675)
                ·
                  refine ⟨32437050367422709649749013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21624700244948473099832675 32437050367422709649749013)
                  ·
                    refine ⟨1520486735972939514831985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 32437050367422709649749013 1520486735972939514831985)
                    ·
                      refine ⟨1140365051979704636123989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1520486735972939514831985 1140365051979704636123989)
                      ·
                        rfl

theorem cell23_2220853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 1, 1, 1, 6, 2].length) (baseStart_2220853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2220853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2220853 prefixEnd_2220853 := by exact prefixLift 2220853
  have htrace : WordTrace (prefixWord ++ tailWord_2220853) baseStart_2220853 baseEnd_2220853 := by
    simpa [prefixWord, tailWord_2220853, baseEnd_2220853] using wordTrace_append hprefix tailTrace_2220853
  have hstable : (prefixWord ++ tailWord_2220853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2220853).length < 2 ^ (prefixWord ++ tailWord_2220853).sum := by decide
  have hdescent : baseEnd_2220853 < baseStart_2220853 := by decide
  rcases family_descends (prefixWord ++ tailWord_2220853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2220856 : List Nat := [2, 1, 2, 1, 3, 2, 2, 2, 1, 4, 3]
def baseStart_2220856 : Nat := 118140960795 + 2220856 * 2 ^ 59
def prefixEnd_2220856 : Nat := 4983230072969 + 3 ^ 40 * 2220856 * 2
def baseEnd_2220856 : Nat := 1140366592421668124386475

theorem tailTrace_2220856 : CollatzResearch.WordTrace tailWord_2220856 prefixEnd_2220856 1140366592421668124386475 := by
  unfold tailWord_2220856
  simp only [CollatzResearch.WordTrace]
  refine ⟨40500636421112739426465211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54000848561483652568620281 40500636421112739426465211)
  ·
    refine ⟨60750954631669109139697817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40500636421112739426465211 60750954631669109139697817)
    ·
      refine ⟨45563215973751831854773363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60750954631669109139697817 45563215973751831854773363)
      ·
        refine ⟨68344823960627747782160045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45563215973751831854773363 68344823960627747782160045)
        ·
          refine ⟨25629308985235405418310017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 68344823960627747782160045 25629308985235405418310017)
          ·
            refine ⟨19221981738926554063732513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25629308985235405418310017 19221981738926554063732513)
            ·
              refine ⟨14416486304194915547799385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19221981738926554063732513 14416486304194915547799385)
              ·
                refine ⟨10812364728146186660849539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14416486304194915547799385 10812364728146186660849539)
                ·
                  refine ⟨16218547092219279991274309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10812364728146186660849539 16218547092219279991274309)
                  ·
                    refine ⟨3040977579791114998363933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16218547092219279991274309 3040977579791114998363933)
                    ·
                      refine ⟨1140366592421668124386475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3040977579791114998363933 1140366592421668124386475)
                      ·
                        rfl

theorem cell23_2220856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 2, 2, 1, 4, 3].length) (baseStart_2220856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2220856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2220856 prefixEnd_2220856 := by exact prefixLift 2220856
  have htrace : WordTrace (prefixWord ++ tailWord_2220856) baseStart_2220856 baseEnd_2220856 := by
    simpa [prefixWord, tailWord_2220856, baseEnd_2220856] using wordTrace_append hprefix tailTrace_2220856
  have hstable : (prefixWord ++ tailWord_2220856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2220856).length < 2 ^ (prefixWord ++ tailWord_2220856).sum := by decide
  have hdescent : baseEnd_2220856 < baseStart_2220856 := by decide
  rcases family_descends (prefixWord ++ tailWord_2220856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2220863 : List Nat := [1, 1, 2, 2, 5, 2, 1, 2, 3, 4]
def baseStart_2220863 : Nat := 118140960795 + 2220863 * 2 ^ 59
def prefixEnd_2220863 : Nat := 4983230072969 + 3 ^ 40 * 2220863 * 2
def baseEnd_2220863 : Nat := 380123395595416532332981

theorem tailTrace_2220863 : CollatzResearch.WordTrace tailWord_2220863 prefixEnd_2220863 380123395595416532332981 := by
  unfold tailWord_2220863
  simp only [CollatzResearch.WordTrace]
  refine ⟨81001528153200119048435243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54001018768800079365623495 81001528153200119048435243)
  ·
    refine ⟨121502292229800178572652865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81001528153200119048435243 121502292229800178572652865)
    ·
      refine ⟨91126719172350133929489649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 121502292229800178572652865 91126719172350133929489649)
      ·
        refine ⟨68345039379262600447117237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 91126719172350133929489649 68345039379262600447117237)
        ·
          refine ⟨6407347441805868791917241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 68345039379262600447117237 6407347441805868791917241)
          ·
            refine ⟨4805510581354401593937931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6407347441805868791917241 4805510581354401593937931)
            ·
              refine ⟨7208265872031602390906897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4805510581354401593937931 7208265872031602390906897)
              ·
                refine ⟨5406199404023701793180173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7208265872031602390906897 5406199404023701793180173)
                ·
                  refine ⟨2027324776508888172442565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5406199404023701793180173 2027324776508888172442565)
                  ·
                    refine ⟨380123395595416532332981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2027324776508888172442565 380123395595416532332981)
                    ·
                      rfl

theorem cell23_2220863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 1, 2, 3, 4].length) (baseStart_2220863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2220863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2220863 prefixEnd_2220863 := by exact prefixLift 2220863
  have htrace : WordTrace (prefixWord ++ tailWord_2220863) baseStart_2220863 baseEnd_2220863 := by
    simpa [prefixWord, tailWord_2220863, baseEnd_2220863] using wordTrace_append hprefix tailTrace_2220863
  have hstable : (prefixWord ++ tailWord_2220863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2220863).length < 2 ^ (prefixWord ++ tailWord_2220863).sum := by decide
  have hdescent : baseEnd_2220863 < baseStart_2220863 := by decide
  rcases family_descends (prefixWord ++ tailWord_2220863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2220873 : List Nat := [1, 2, 1, 1, 2, 5, 3, 1, 2, 2, 3]
def baseStart_2220873 : Nat := 118140960795 + 2220873 * 2 ^ 59
def prefixEnd_2220873 : Nat := 4983230072969 + 3 ^ 40 * 2220873 * 2
def baseEnd_2220873 : Nat := 1140375321592794557873897

theorem tailTrace_2220873 : CollatzResearch.WordTrace tailWord_2220873 prefixEnd_2220873 1140375321592794557873897 := by
  unfold tailWord_2220873
  simp only [CollatzResearch.WordTrace]
  refine ⟨81001892883163890756299273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54001261922109260504199515 81001892883163890756299273)
  ·
    refine ⟨60751419662372918067224455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81001892883163890756299273 60751419662372918067224455)
    ·
      refine ⟨91127129493559377100836683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60751419662372918067224455 91127129493559377100836683)
      ·
        refine ⟨136690694240339065651255025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91127129493559377100836683 136690694240339065651255025)
        ·
          refine ⟨102518020680254299238441269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 136690694240339065651255025 102518020680254299238441269)
          ·
            refine ⟨9611064438773840553603869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 102518020680254299238441269 9611064438773840553603869)
            ·
              refine ⟨3604149164540190207601451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9611064438773840553603869 3604149164540190207601451)
              ·
                refine ⟨5406223746810285311402177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3604149164540190207601451 5406223746810285311402177)
                ·
                  refine ⟨4054667810107713983551633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5406223746810285311402177 4054667810107713983551633)
                  ·
                    refine ⟨3041000857580785487663725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4054667810107713983551633 3041000857580785487663725)
                    ·
                      refine ⟨1140375321592794557873897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3041000857580785487663725 1140375321592794557873897)
                      ·
                        rfl

theorem cell23_2220873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 3, 1, 2, 2, 3].length) (baseStart_2220873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2220873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2220873 prefixEnd_2220873 := by exact prefixLift 2220873
  have htrace : WordTrace (prefixWord ++ tailWord_2220873) baseStart_2220873 baseEnd_2220873 := by
    simpa [prefixWord, tailWord_2220873, baseEnd_2220873] using wordTrace_append hprefix tailTrace_2220873
  have hstable : (prefixWord ++ tailWord_2220873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2220873).length < 2 ^ (prefixWord ++ tailWord_2220873).sum := by decide
  have hdescent : baseEnd_2220873 < baseStart_2220873 := by decide
  rcases family_descends (prefixWord ++ tailWord_2220873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2220879 : List Nat := [1, 1, 2, 1, 1, 2, 1, 1, 5, 2, 6]
def baseStart_2220879 : Nat := 118140960795 + 2220879 * 2 ^ 59
def prefixEnd_2220879 : Nat := 4983230072969 + 3 ^ 40 * 2220879 * 2
def baseEnd_2220879 : Nat := 1140378402476721534398869

theorem tailTrace_2220879 : CollatzResearch.WordTrace tailWord_2220879 prefixEnd_2220879 1140378402476721534398869 := by
  unfold tailWord_2220879
  simp only [CollatzResearch.WordTrace]
  refine ⟨81002111721142153781017691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54001407814094769187345127 81002111721142153781017691)
  ·
    refine ⟨121503167581713230671526537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81002111721142153781017691 121503167581713230671526537)
    ·
      refine ⟨91127375686284923003644903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 121503167581713230671526537 91127375686284923003644903)
      ·
        refine ⟨136691063529427384505467355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91127375686284923003644903 136691063529427384505467355)
        ·
          refine ⟨205036595294141076758201033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 136691063529427384505467355 205036595294141076758201033)
          ·
            refine ⟨153777446470605807568650775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 205036595294141076758201033 153777446470605807568650775)
            ·
              refine ⟨230666169705908711352976163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 153777446470605807568650775 230666169705908711352976163)
              ·
                refine ⟨345999254558863067029464245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 230666169705908711352976163 345999254558863067029464245)
                ·
                  refine ⟨32437430114893412534012273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 345999254558863067029464245 32437430114893412534012273)
                  ·
                    refine ⟨24328072586170059400509205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 32437430114893412534012273 24328072586170059400509205)
                    ·
                      refine ⟨1140378402476721534398869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 24328072586170059400509205 1140378402476721534398869)
                      ·
                        rfl

theorem cell23_2220879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 1, 5, 2, 6].length) (baseStart_2220879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2220879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2220879 prefixEnd_2220879 := by exact prefixLift 2220879
  have htrace : WordTrace (prefixWord ++ tailWord_2220879) baseStart_2220879 baseEnd_2220879 := by
    simpa [prefixWord, tailWord_2220879, baseEnd_2220879] using wordTrace_append hprefix tailTrace_2220879
  have hstable : (prefixWord ++ tailWord_2220879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2220879).length < 2 ^ (prefixWord ++ tailWord_2220879).sum := by decide
  have hdescent : baseEnd_2220879 < baseStart_2220879 := by decide
  rcases family_descends (prefixWord ++ tailWord_2220879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2220913 : List Nat := [1, 2, 2, 2, 1, 4, 1, 2, 1, 5, 2]
def baseStart_2220913 : Nat := 118140960795 + 2220913 * 2 ^ 59
def prefixEnd_2220913 : Nat := 4983230072969 + 3 ^ 40 * 2220913 * 2
def baseEnd_2220913 : Nat := 1140395860818974401373713

theorem tailTrace_2220913 : CollatzResearch.WordTrace tailWord_2220913 prefixEnd_2220913 1140395860818974401373713 := by
  unfold tailWord_2220913
  simp only [CollatzResearch.WordTrace]
  refine ⟨81003351803018977587755393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54002234535345985058503595 81003351803018977587755393)
  ·
    refine ⟨60752513852264233190816545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81003351803018977587755393 60752513852264233190816545)
    ·
      refine ⟨45564385389198174893112409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60752513852264233190816545 45564385389198174893112409)
      ·
        refine ⟨34173289041898631169834307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45564385389198174893112409 34173289041898631169834307)
        ·
          refine ⟨51259933562847946754751461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34173289041898631169834307 51259933562847946754751461)
          ·
            refine ⟨9611237543033990016515899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 51259933562847946754751461 9611237543033990016515899)
            ·
              refine ⟨14416856314550985024773849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9611237543033990016515899 14416856314550985024773849)
              ·
                refine ⟨10812642235913238768580387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14416856314550985024773849 10812642235913238768580387)
                ·
                  refine ⟨16218963353869858152870581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10812642235913238768580387 16218963353869858152870581)
                  ·
                    refine ⟨1520527814425299201831617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 16218963353869858152870581 1520527814425299201831617)
                    ·
                      refine ⟨1140395860818974401373713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1520527814425299201831617 1140395860818974401373713)
                      ·
                        rfl

theorem cell23_2220913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 1, 2, 1, 5, 2].length) (baseStart_2220913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2220913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2220913 prefixEnd_2220913 := by exact prefixLift 2220913
  have htrace : WordTrace (prefixWord ++ tailWord_2220913) baseStart_2220913 baseEnd_2220913 := by
    simpa [prefixWord, tailWord_2220913, baseEnd_2220913] using wordTrace_append hprefix tailTrace_2220913
  have hstable : (prefixWord ++ tailWord_2220913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2220913).length < 2 ^ (prefixWord ++ tailWord_2220913).sum := by decide
  have hdescent : baseEnd_2220913 < baseStart_2220913 := by decide
  rcases family_descends (prefixWord ++ tailWord_2220913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2220937 : List Nat := [1, 2, 1, 1, 5, 2, 3, 3, 1, 1, 3]
def baseStart_2220937 : Nat := 118140960795 + 2220937 * 2 ^ 59
def prefixEnd_2220937 : Nat := 4983230072969 + 3 ^ 40 * 2220937 * 2
def baseEnd_2220937 : Nat := 1140408184354682307473603

theorem tailTrace_2220937 : CollatzResearch.WordTrace tailWord_2220937 prefixEnd_2220937 1140408184354682307473603 := by
  unfold tailWord_2220937
  simp only [CollatzResearch.WordTrace]
  refine ⟨81004227154932029686629065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54002818103288019791086043 81004227154932029686629065)
  ·
    refine ⟨60753170366199022264971799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81004227154932029686629065 60753170366199022264971799)
    ·
      refine ⟨91129755549298533397457699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60753170366199022264971799 91129755549298533397457699)
      ·
        refine ⟨136694633323947800096186549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91129755549298533397457699 136694633323947800096186549)
        ·
          refine ⟨12815121874120106259017489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 136694633323947800096186549 12815121874120106259017489)
          ·
            refine ⟨9611341405590079694263117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12815121874120106259017489 9611341405590079694263117)
            ·
              refine ⟨3604253027096279885348669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9611341405590079694263117 3604253027096279885348669)
              ·
                refine ⟨1351594885161104957005751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3604253027096279885348669 1351594885161104957005751)
                ·
                  refine ⟨2027392327741657435508627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1351594885161104957005751 2027392327741657435508627)
                  ·
                    refine ⟨3041088491612486153262941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2027392327741657435508627 3041088491612486153262941)
                    ·
                      refine ⟨1140408184354682307473603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3041088491612486153262941 1140408184354682307473603)
                      ·
                        rfl

theorem cell23_2220937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 3, 3, 1, 1, 3].length) (baseStart_2220937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2220937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2220937 prefixEnd_2220937 := by exact prefixLift 2220937
  have htrace : WordTrace (prefixWord ++ tailWord_2220937) baseStart_2220937 baseEnd_2220937 := by
    simpa [prefixWord, tailWord_2220937, baseEnd_2220937] using wordTrace_append hprefix tailTrace_2220937
  have hstable : (prefixWord ++ tailWord_2220937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2220937).length < 2 ^ (prefixWord ++ tailWord_2220937).sum := by decide
  have hdescent : baseEnd_2220937 < baseStart_2220937 := by decide
  rcases family_descends (prefixWord ++ tailWord_2220937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2220953 : List Nat := [1, 2, 1, 2, 1, 3, 1, 6, 2, 4]
def baseStart_2220953 : Nat := 118140960795 + 2220953 * 2 ^ 59
def prefixEnd_2220953 : Nat := 4983230072969 + 3 ^ 40 * 2220953 * 2
def baseEnd_2220953 : Nat := 380138800015051414957843

theorem tailTrace_2220953 : CollatzResearch.WordTrace tailWord_2220953 prefixEnd_2220953 380138800015051414957843 := by
  unfold tailWord_2220953
  simp only [CollatzResearch.WordTrace]
  refine ⟨81004810722874064419211513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54003207148582709612807675 81004810722874064419211513)
  ·
    refine ⟨60753608042155548314408635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81004810722874064419211513 60753608042155548314408635)
    ·
      refine ⟨91130412063233322471612953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60753608042155548314408635 91130412063233322471612953)
      ·
        refine ⟨68347809047424991853709715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 91130412063233322471612953 68347809047424991853709715)
        ·
          refine ⟨102521713571137487780564573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68347809047424991853709715 102521713571137487780564573)
          ·
            refine ⟨38445642589176557917711715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 102521713571137487780564573 38445642589176557917711715)
            ·
              refine ⟨57668463883764836876567573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38445642589176557917711715 57668463883764836876567573)
              ·
                refine ⟨2703209244551476728589105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 57668463883764836876567573 2703209244551476728589105)
                ·
                  refine ⟨2027406933413607546441829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2703209244551476728589105 2027406933413607546441829)
                  ·
                    refine ⟨380138800015051414957843, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2027406933413607546441829 380138800015051414957843)
                    ·
                      rfl

theorem cell23_2220953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 6, 2, 4].length) (baseStart_2220953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2220953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2220953 prefixEnd_2220953 := by exact prefixLift 2220953
  have htrace : WordTrace (prefixWord ++ tailWord_2220953) baseStart_2220953 baseEnd_2220953 := by
    simpa [prefixWord, tailWord_2220953, baseEnd_2220953] using wordTrace_append hprefix tailTrace_2220953
  have hstable : (prefixWord ++ tailWord_2220953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2220953).length < 2 ^ (prefixWord ++ tailWord_2220953).sum := by decide
  have hdescent : baseEnd_2220953 < baseStart_2220953 := by decide
  rcases family_descends (prefixWord ++ tailWord_2220953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2220954 : List Nat := [3, 1, 1, 4, 4, 1, 1, 1, 3, 1, 3]
def baseStart_2220954 : Nat := 118140960795 + 2220954 * 2 ^ 59
def prefixEnd_2220954 : Nat := 4983230072969 + 3 ^ 40 * 2220954 * 2
def baseEnd_2220954 : Nat := 1140416913525808740961025

theorem tailTrace_2220954 : CollatzResearch.WordTrace tailWord_2220954 prefixEnd_2220954 1140416913525808740961025 := by
  unfold tailWord_2220954
  simp only [CollatzResearch.WordTrace]
  refine ⟨20251211798967610397499479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54003231463913627726665277 20251211798967610397499479)
  ·
    refine ⟨30376817698451415596249219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20251211798967610397499479 30376817698451415596249219)
    ·
      refine ⟨45565226547677123394373829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30376817698451415596249219 45565226547677123394373829)
      ·
        refine ⟨8543479977689460636445093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 45565226547677123394373829 8543479977689460636445093)
        ·
          refine ⟨1601902495816773869333455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8543479977689460636445093 1601902495816773869333455)
          ·
            refine ⟨2402853743725160804000183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1601902495816773869333455 2402853743725160804000183)
            ·
              refine ⟨3604280615587741206000275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2402853743725160804000183 3604280615587741206000275)
              ·
                refine ⟨5406420923381611809000413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3604280615587741206000275 5406420923381611809000413)
                ·
                  refine ⟨2027407846268104428375155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5406420923381611809000413 2027407846268104428375155)
                  ·
                    refine ⟨3041111769402156642562733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2027407846268104428375155 3041111769402156642562733)
                    ·
                      refine ⟨1140416913525808740961025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3041111769402156642562733 1140416913525808740961025)
                      ·
                        rfl

theorem cell23_2220954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 4, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 4, 1, 1, 1, 3, 1, 3].length) (baseStart_2220954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2220954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2220954 prefixEnd_2220954 := by exact prefixLift 2220954
  have htrace : WordTrace (prefixWord ++ tailWord_2220954) baseStart_2220954 baseEnd_2220954 := by
    simpa [prefixWord, tailWord_2220954, baseEnd_2220954] using wordTrace_append hprefix tailTrace_2220954
  have hstable : (prefixWord ++ tailWord_2220954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2220954).length < 2 ^ (prefixWord ++ tailWord_2220954).sum := by decide
  have hdescent : baseEnd_2220954 < baseStart_2220954 := by decide
  rcases family_descends (prefixWord ++ tailWord_2220954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2220977 : List Nat := [1, 2, 2, 4, 3, 2, 1, 2, 1, 1, 4]
def baseStart_2220977 : Nat := 118140960795 + 2220977 * 2 ^ 59
def prefixEnd_2220977 : Nat := 4983230072969 + 3 ^ 40 * 2220977 * 2
def baseEnd_2220977 : Nat := 1140428723580862150973419

theorem tailTrace_2220977 : CollatzResearch.WordTrace tailWord_2220977 prefixEnd_2220977 1140428723580862150973419 := by
  unfold tailWord_2220977
  simp only [CollatzResearch.WordTrace]
  refine ⟨81005686074787116518085185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54003790716524744345390123 81005686074787116518085185)
  ·
    refine ⟨60754264556090337388563889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81005686074787116518085185 60754264556090337388563889)
    ·
      refine ⟨45565698417067753041422917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60754264556090337388563889 45565698417067753041422917)
      ·
        refine ⟨8543568453200203695266797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 45565698417067753041422917 8543568453200203695266797)
        ·
          refine ⟨3203838169950076385725049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8543568453200203695266797 3203838169950076385725049)
          ·
            refine ⟨2402878627462557289293787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3203838169950076385725049 2402878627462557289293787)
            ·
              refine ⟨3604317941193835933940681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2402878627462557289293787 3604317941193835933940681)
              ·
                refine ⟨2703238455895376950455511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3604317941193835933940681 2703238455895376950455511)
                ·
                  refine ⟨4054857683843065425683267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2703238455895376950455511 4054857683843065425683267)
                  ·
                    refine ⟨6082286525764598138524901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4054857683843065425683267 6082286525764598138524901)
                    ·
                      refine ⟨1140428723580862150973419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6082286525764598138524901 1140428723580862150973419)
                      ·
                        rfl

theorem cell23_2220977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 2, 1, 2, 1, 1, 4].length) (baseStart_2220977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2220977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2220977 prefixEnd_2220977 := by exact prefixLift 2220977
  have htrace : WordTrace (prefixWord ++ tailWord_2220977) baseStart_2220977 baseEnd_2220977 := by
    simpa [prefixWord, tailWord_2220977, baseEnd_2220977] using wordTrace_append hprefix tailTrace_2220977
  have hstable : (prefixWord ++ tailWord_2220977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2220977).length < 2 ^ (prefixWord ++ tailWord_2220977).sum := by decide
  have hdescent : baseEnd_2220977 < baseStart_2220977 := by decide
  rcases family_descends (prefixWord ++ tailWord_2220977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2221063 : List Nat := [1, 1, 4, 3, 1, 1, 1, 1, 4, 2, 4]
def baseStart_2221063 : Nat := 118140960795 + 2221063 * 2 ^ 59
def prefixEnd_2221063 : Nat := 4983230072969 + 3 ^ 40 * 2221063 * 2
def baseEnd_2221063 : Nat := 1140472882917148814498023

theorem tailTrace_2221063 : CollatzResearch.WordTrace tailWord_2221063 prefixEnd_2221063 1140472882917148814498023 := by
  unfold tailWord_2221063
  simp only [CollatzResearch.WordTrace]
  refine ⟨81008822752475553205715843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54005881834983702137143895 81008822752475553205715843)
  ·
    refine ⟨121513234128713329808573765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81008822752475553205715843 121513234128713329808573765)
    ·
      refine ⟨22783731399133749339107581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 121513234128713329808573765 22783731399133749339107581)
      ·
        refine ⟨8543899274675156002165343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22783731399133749339107581 8543899274675156002165343)
        ·
          refine ⟨12815848912012734003248015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8543899274675156002165343 12815848912012734003248015)
          ·
            refine ⟨19223773368019101004872023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12815848912012734003248015 19223773368019101004872023)
            ·
              refine ⟨28835660052028651507308035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19223773368019101004872023 28835660052028651507308035)
              ·
                refine ⟨43253490078042977260962053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28835660052028651507308035 43253490078042977260962053)
                ·
                  refine ⟨8110029389633058236430385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 43253490078042977260962053 8110029389633058236430385)
                  ·
                    refine ⟨6082522042224793677322789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8110029389633058236430385 6082522042224793677322789)
                    ·
                      refine ⟨1140472882917148814498023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6082522042224793677322789 1140472882917148814498023)
                      ·
                        rfl

theorem cell23_2221063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 1, 4, 2, 4].length) (baseStart_2221063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2221063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2221063 prefixEnd_2221063 := by exact prefixLift 2221063
  have htrace : WordTrace (prefixWord ++ tailWord_2221063) baseStart_2221063 baseEnd_2221063 := by
    simpa [prefixWord, tailWord_2221063, baseEnd_2221063] using wordTrace_append hprefix tailTrace_2221063
  have hstable : (prefixWord ++ tailWord_2221063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2221063).length < 2 ^ (prefixWord ++ tailWord_2221063).sum := by decide
  have hdescent : baseEnd_2221063 < baseStart_2221063 := by decide
  rcases family_descends (prefixWord ++ tailWord_2221063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2221067 : List Nat := [1, 1, 1, 1, 6, 3, 1, 1, 4, 2, 2]
def baseStart_2221067 : Nat := 118140960795 + 2221067 * 2 ^ 59
def prefixEnd_2221067 : Nat := 4983230072969 + 3 ^ 40 * 2221067 * 2
def baseEnd_2221067 : Nat := 1140474936839766798848005

theorem tailTrace_2221067 : CollatzResearch.WordTrace tailWord_2221067 prefixEnd_2221067 1140474936839766798848005 := by
  unfold tailWord_2221067
  simp only [CollatzResearch.WordTrace]
  refine ⟨81008968644461061888861455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54005979096307374592574303 81008968644461061888861455)
  ·
    refine ⟨121513452966691592833292183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81008968644461061888861455 121513452966691592833292183)
    ·
      refine ⟨182270179450037389249938275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121513452966691592833292183 182270179450037389249938275)
      ·
        refine ⟨273405269175056083874907413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 182270179450037389249938275 273405269175056083874907413)
        ·
          refine ⟨12815871992580753931636285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 273405269175056083874907413 12815871992580753931636285)
          ·
            refine ⟨4805951997217782724363607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12815871992580753931636285 4805951997217782724363607)
            ·
              refine ⟨7208927995826674086545411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4805951997217782724363607 7208927995826674086545411)
              ·
                refine ⟨10813391993740011129818117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7208927995826674086545411 10813391993740011129818117)
                ·
                  refine ⟨2027510998826252086840897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10813391993740011129818117 2027510998826252086840897)
                  ·
                    refine ⟨1520633249119689065130673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2027510998826252086840897 1520633249119689065130673)
                    ·
                      refine ⟨1140474936839766798848005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1520633249119689065130673 1140474936839766798848005)
                      ·
                        rfl

theorem cell23_2221067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 1, 1, 4, 2, 2].length) (baseStart_2221067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2221067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2221067 prefixEnd_2221067 := by exact prefixLift 2221067
  have htrace : WordTrace (prefixWord ++ tailWord_2221067) baseStart_2221067 baseEnd_2221067 := by
    simpa [prefixWord, tailWord_2221067, baseEnd_2221067] using wordTrace_append hprefix tailTrace_2221067
  have hstable : (prefixWord ++ tailWord_2221067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2221067).length < 2 ^ (prefixWord ++ tailWord_2221067).sum := by decide
  have hdescent : baseEnd_2221067 < baseStart_2221067 := by decide
  rcases family_descends (prefixWord ++ tailWord_2221067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2221084 : List Nat := [2, 2, 3, 1, 4, 2, 1, 1, 1, 4, 2]
def baseStart_2221084 : Nat := 118140960795 + 2221084 * 2 ^ 59
def prefixEnd_2221084 : Nat := 4983230072969 + 3 ^ 40 * 2221084 * 2
def baseEnd_2221084 : Nat := 1140483666010893232335427

theorem tailTrace_2221084 : CollatzResearch.WordTrace tailWord_2221084 prefixEnd_2221084 1140483666010893232335427 := by
  unfold tailWord_2221084
  simp only [CollatzResearch.WordTrace]
  refine ⟨40504794342699736896115153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54006392456932982528153537 40504794342699736896115153)
  ·
    refine ⟨30378595757024802672086365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40504794342699736896115153 30378595757024802672086365)
    ·
      refine ⟨11391973408884301002032387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30378595757024802672086365 11391973408884301002032387)
      ·
        refine ⟨17087960113326451503048581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11391973408884301002032387 17087960113326451503048581)
        ·
          refine ⟨3203992521248709656821609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17087960113326451503048581 3203992521248709656821609)
          ·
            refine ⟨2402994390936532242616207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3203992521248709656821609 2402994390936532242616207)
            ·
              refine ⟨3604491586404798363924311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2402994390936532242616207 3604491586404798363924311)
              ·
                refine ⟨5406737379607197545886467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3604491586404798363924311 5406737379607197545886467)
                ·
                  refine ⟨8110106069410796318829701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5406737379607197545886467 8110106069410796318829701)
                  ·
                    refine ⟨1520644888014524309780569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8110106069410796318829701 1520644888014524309780569)
                    ·
                      refine ⟨1140483666010893232335427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1520644888014524309780569 1140483666010893232335427)
                      ·
                        rfl

theorem cell23_2221084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 2, 1, 1, 1, 4, 2].length) (baseStart_2221084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2221084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2221084 prefixEnd_2221084 := by exact prefixLift 2221084
  have htrace : WordTrace (prefixWord ++ tailWord_2221084) baseStart_2221084 baseEnd_2221084 := by
    simpa [prefixWord, tailWord_2221084, baseEnd_2221084] using wordTrace_append hprefix tailTrace_2221084
  have hstable : (prefixWord ++ tailWord_2221084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2221084).length < 2 ^ (prefixWord ++ tailWord_2221084).sum := by decide
  have hdescent : baseEnd_2221084 < baseStart_2221084 := by decide
  rcases family_descends (prefixWord ++ tailWord_2221084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2221153 : List Nat := [1, 2, 3, 1, 1, 2, 2, 1, 2, 4, 4]
def baseStart_2221153 : Nat := 118140960795 + 2221153 * 2 ^ 59
def prefixEnd_2221153 : Nat := 4983230072969 + 3 ^ 40 * 2221153 * 2
def baseEnd_2221153 : Nat := 1140519096176053462372609

theorem tailTrace_2221153 : CollatzResearch.WordTrace tailWord_2221153 prefixEnd_2221153 1140519096176053462372609 := by
  unfold tailWord_2221153
  simp only [CollatzResearch.WordTrace]
  refine ⟨81012105322149498576492113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54008070214766332384328075 81012105322149498576492113)
  ·
    refine ⟨60759078991612123932369085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81012105322149498576492113 60759078991612123932369085)
    ·
      refine ⟨22784654621854546474638407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 60759078991612123932369085 22784654621854546474638407)
      ·
        refine ⟨34176981932781819711957611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22784654621854546474638407 34176981932781819711957611)
        ·
          refine ⟨51265472899172729567936417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34176981932781819711957611 51265472899172729567936417)
          ·
            refine ⟨38449104674379547175952313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51265472899172729567936417 38449104674379547175952313)
            ·
              refine ⟨28836828505784660381964235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38449104674379547175952313 28836828505784660381964235)
              ·
                refine ⟨43255242758676990572946353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28836828505784660381964235 43255242758676990572946353)
                ·
                  refine ⟨32441432069007742929709765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 43255242758676990572946353 32441432069007742929709765)
                  ·
                    refine ⟨6082768512938951799320581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 32441432069007742929709765 6082768512938951799320581)
                    ·
                      refine ⟨1140519096176053462372609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6082768512938951799320581 1140519096176053462372609)
                      ·
                        rfl

theorem cell23_2221153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 1, 2, 4, 4].length) (baseStart_2221153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2221153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2221153 prefixEnd_2221153 := by exact prefixLift 2221153
  have htrace : WordTrace (prefixWord ++ tailWord_2221153) baseStart_2221153 baseEnd_2221153 := by
    simpa [prefixWord, tailWord_2221153, baseEnd_2221153] using wordTrace_append hprefix tailTrace_2221153
  have hstable : (prefixWord ++ tailWord_2221153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2221153).length < 2 ^ (prefixWord ++ tailWord_2221153).sum := by decide
  have hdescent : baseEnd_2221153 < baseStart_2221153 := by decide
  rcases family_descends (prefixWord ++ tailWord_2221153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2221167 : List Nat := [1, 1, 2, 1, 3, 3, 2, 5, 1, 4]
def baseStart_2221167 : Nat := 118140960795 + 2221167 * 2 ^ 59
def prefixEnd_2221167 : Nat := 4983230072969 + 3 ^ 40 * 2221167 * 2
def baseEnd_2221167 : Nat := 380175428301738802532515

theorem tailTrace_2221167 : CollatzResearch.WordTrace tailWord_2221167 prefixEnd_2221167 380175428301738802532515 := by
  unfold tailWord_2221167
  simp only [CollatzResearch.WordTrace]
  refine ⟨81012615944098778967501755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54008410629399185978334503 81012615944098778967501755)
  ·
    refine ⟨121518923916148168451252633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81012615944098778967501755 121518923916148168451252633)
    ·
      refine ⟨91139192937111126338439475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 121518923916148168451252633 91139192937111126338439475)
      ·
        refine ⟨136708789405666689507659213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91139192937111126338439475 136708789405666689507659213)
        ·
          refine ⟨51265796027125008565372205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 136708789405666689507659213 51265796027125008565372205)
          ·
            refine ⟨19224673510171878212014577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 51265796027125008565372205 19224673510171878212014577)
            ·
              refine ⟨14418505132628908659010933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19224673510171878212014577 14418505132628908659010933)
              ·
                refine ⟨1351734856183960186782275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 14418505132628908659010933 1351734856183960186782275)
                ·
                  refine ⟨2027602284275940280173413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1351734856183960186782275 2027602284275940280173413)
                  ·
                    refine ⟨380175428301738802532515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2027602284275940280173413 380175428301738802532515)
                    ·
                      rfl

theorem cell23_2221167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 2, 5, 1, 4].length) (baseStart_2221167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2221167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2221167 prefixEnd_2221167 := by exact prefixLift 2221167
  have htrace : WordTrace (prefixWord ++ tailWord_2221167) baseStart_2221167 baseEnd_2221167 := by
    simpa [prefixWord, tailWord_2221167, baseEnd_2221167] using wordTrace_append hprefix tailTrace_2221167
  have hstable : (prefixWord ++ tailWord_2221167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2221167).length < 2 ^ (prefixWord ++ tailWord_2221167).sum := by decide
  have hdescent : baseEnd_2221167 < baseStart_2221167 := by decide
  rcases family_descends (prefixWord ++ tailWord_2221167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2221180 : List Nat := [2, 2, 2, 1, 1, 3, 4, 2, 6]
def baseStart_2221180 : Nat := 118140960795 + 2221180 * 2 ^ 59
def prefixEnd_2221180 : Nat := 4983230072969 + 3 ^ 40 * 2221180 * 2
def baseEnd_2221180 : Nat := 126725884461524984081665

theorem tailTrace_2221180 : CollatzResearch.WordTrace tailWord_2221180 prefixEnd_2221180 126725884461524984081665 := by
  unfold tailWord_2221180
  simp only [CollatzResearch.WordTrace]
  refine ⟨40506545046525841093862497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54008726728701121458483329 40506545046525841093862497)
  ·
    refine ⟨30379908784894380820396873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40506545046525841093862497 30379908784894380820396873)
    ·
      refine ⟨22784931588670785615297655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30379908784894380820396873 22784931588670785615297655)
      ·
        refine ⟨34177397383006178422946483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22784931588670785615297655 34177397383006178422946483)
        ·
          refine ⟨51266096074509267634419725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34177397383006178422946483 51266096074509267634419725)
          ·
            refine ⟨19224786027940975362907397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 51266096074509267634419725 19224786027940975362907397)
            ·
              refine ⟨3604647380238932880545137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19224786027940975362907397 3604647380238932880545137)
              ·
                refine ⟨2703485535179199660408853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3604647380238932880545137 2703485535179199660408853)
                ·
                  refine ⟨126725884461524984081665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2703485535179199660408853 126725884461524984081665)
                  ·
                    rfl

theorem cell23_2221180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 4, 2, 6].length) (baseStart_2221180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2221180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2221180 prefixEnd_2221180 := by exact prefixLift 2221180
  have htrace : WordTrace (prefixWord ++ tailWord_2221180) baseStart_2221180 baseEnd_2221180 := by
    simpa [prefixWord, tailWord_2221180, baseEnd_2221180] using wordTrace_append hprefix tailTrace_2221180
  have hstable : (prefixWord ++ tailWord_2221180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2221180).length < 2 ^ (prefixWord ++ tailWord_2221180).sum := by decide
  have hdescent : baseEnd_2221180 < baseStart_2221180 := by decide
  rcases family_descends (prefixWord ++ tailWord_2221180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2221184 : List Nat := [2, 1, 1, 2, 1, 3, 6, 2, 1, 4]
def baseStart_2221184 : Nat := 118140960795 + 2221184 * 2 ^ 59
def prefixEnd_2221184 : Nat := 4983230072969 + 3 ^ 40 * 2221184 * 2
def baseEnd_2221184 : Nat := 380178338025447613694989

theorem tailTrace_2221184 : CollatzResearch.WordTrace tailWord_2221184 prefixEnd_2221184 380178338025447613694989 := by
  unfold tailWord_2221184
  simp only [CollatzResearch.WordTrace]
  refine ⟨40506617992518595435435303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54008823990024793913913737 40506617992518595435435303)
  ·
    refine ⟨60759926988777893153152955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40506617992518595435435303 60759926988777893153152955)
    ·
      refine ⟨91139890483166839729729433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60759926988777893153152955 91139890483166839729729433)
      ·
        refine ⟨68354917862375129797297075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 91139890483166839729729433 68354917862375129797297075)
        ·
          refine ⟨102532376793562694695945613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68354917862375129797297075 102532376793562694695945613)
          ·
            refine ⟨38449641297586010510979605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 102532376793562694695945613 38449641297586010510979605)
            ·
              refine ⟨1802326935824344242702169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 38449641297586010510979605 1802326935824344242702169)
              ·
                refine ⟨1351745201868258182026627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1802326935824344242702169 1351745201868258182026627)
                ·
                  refine ⟨2027617802802387273039941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1351745201868258182026627 2027617802802387273039941)
                  ·
                    refine ⟨380178338025447613694989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2027617802802387273039941 380178338025447613694989)
                    ·
                      rfl

theorem cell23_2221184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 6, 2, 1, 4].length) (baseStart_2221184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2221184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2221184 prefixEnd_2221184 := by exact prefixLift 2221184
  have htrace : WordTrace (prefixWord ++ tailWord_2221184) baseStart_2221184 baseEnd_2221184 := by
    simpa [prefixWord, tailWord_2221184, baseEnd_2221184] using wordTrace_append hprefix tailTrace_2221184
  have hstable : (prefixWord ++ tailWord_2221184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2221184).length < 2 ^ (prefixWord ++ tailWord_2221184).sum := by decide
  have hdescent : baseEnd_2221184 < baseStart_2221184 := by decide
  rcases family_descends (prefixWord ++ tailWord_2221184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2221207 : List Nat := [1, 1, 3, 3, 3, 1, 1, 1, 5, 1, 3]
def baseStart_2221207 : Nat := 118140960795 + 2221207 * 2 ^ 59
def prefixEnd_2221207 : Nat := 4983230072969 + 3 ^ 40 * 2221207 * 2
def baseEnd_2221207 : Nat := 1140546824131396251097361

theorem tailTrace_2221207 : CollatzResearch.WordTrace tailWord_2221207 prefixEnd_2221207 1140546824131396251097361 := by
  unfold tailWord_2221207
  simp only [CollatzResearch.WordTrace]
  refine ⟨81014074863953865798957875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54009383242635910532638583 81014074863953865798957875)
  ·
    refine ⟨121521112295930798698436813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81014074863953865798957875 121521112295930798698436813)
    ·
      refine ⟨45570417110974049511913805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 121521112295930798698436813 45570417110974049511913805)
      ·
        refine ⟨17088906416615268566967677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45570417110974049511913805 17088906416615268566967677)
        ·
          refine ⟨6408339906230725712612879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17088906416615268566967677 6408339906230725712612879)
          ·
            refine ⟨9612509859346088568919319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6408339906230725712612879 9612509859346088568919319)
            ·
              refine ⟨14418764789019132853378979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9612509859346088568919319 14418764789019132853378979)
              ·
                refine ⟨21628147183528699280068469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14418764789019132853378979 21628147183528699280068469)
                ·
                  refine ⟨2027638798455815557506419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 21628147183528699280068469 2027638798455815557506419)
                  ·
                    refine ⟨3041458197683723336259629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2027638798455815557506419 3041458197683723336259629)
                    ·
                      refine ⟨1140546824131396251097361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3041458197683723336259629 1140546824131396251097361)
                      ·
                        rfl

theorem cell23_2221207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 1, 1, 5, 1, 3].length) (baseStart_2221207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2221207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2221207 prefixEnd_2221207 := by exact prefixLift 2221207
  have htrace : WordTrace (prefixWord ++ tailWord_2221207) baseStart_2221207 baseEnd_2221207 := by
    simpa [prefixWord, tailWord_2221207, baseEnd_2221207] using wordTrace_append hprefix tailTrace_2221207
  have hstable : (prefixWord ++ tailWord_2221207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2221207).length < 2 ^ (prefixWord ++ tailWord_2221207).sum := by decide
  have hdescent : baseEnd_2221207 < baseStart_2221207 := by decide
  rcases family_descends (prefixWord ++ tailWord_2221207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2221217 : List Nat := [1, 2, 3, 3, 1, 1, 3, 1, 1, 5, 2]
def baseStart_2221217 : Nat := 118140960795 + 2221217 * 2 ^ 59
def prefixEnd_2221217 : Nat := 4983230072969 + 3 ^ 40 * 2221217 * 2
def baseEnd_2221217 : Nat := 1140551958937941211972315

theorem tailTrace_2221217 : CollatzResearch.WordTrace tailWord_2221217 prefixEnd_2221217 1140551958937941211972315 := by
  unfold tailWord_2221217
  simp only [CollatzResearch.WordTrace]
  refine ⟨81014439593917637506821905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54009626395945091671214603 81014439593917637506821905)
  ·
    refine ⟨60760829695438228130116429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81014439593917637506821905 60760829695438228130116429)
    ·
      refine ⟨22785311135789335548793661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 60760829695438228130116429 22785311135789335548793661)
      ·
        refine ⟨8544491675921000830797623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22785311135789335548793661 8544491675921000830797623)
        ·
          refine ⟨12816737513881501246196435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8544491675921000830797623 12816737513881501246196435)
          ·
            refine ⟨19225106270822251869294653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12816737513881501246196435 19225106270822251869294653)
            ·
              refine ⟨7209414851558344450985495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19225106270822251869294653 7209414851558344450985495)
              ·
                refine ⟨10814122277337516676478243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7209414851558344450985495 10814122277337516676478243)
                ·
                  refine ⟨16221183416006275014717365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10814122277337516676478243 16221183416006275014717365)
                  ·
                    refine ⟨1520735945250588282629753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 16221183416006275014717365 1520735945250588282629753)
                    ·
                      refine ⟨1140551958937941211972315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1520735945250588282629753 1140551958937941211972315)
                      ·
                        rfl

theorem cell23_2221217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 3, 1, 1, 5, 2].length) (baseStart_2221217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2221217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2221217 prefixEnd_2221217 := by exact prefixLift 2221217
  have htrace : WordTrace (prefixWord ++ tailWord_2221217) baseStart_2221217 baseEnd_2221217 := by
    simpa [prefixWord, tailWord_2221217, baseEnd_2221217] using wordTrace_append hprefix tailTrace_2221217
  have hstable : (prefixWord ++ tailWord_2221217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2221217).length < 2 ^ (prefixWord ++ tailWord_2221217).sum := by decide
  have hdescent : baseEnd_2221217 < baseStart_2221217 := by decide
  rcases family_descends (prefixWord ++ tailWord_2221217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2221253 : List Nat := [1, 3, 1, 1, 1, 1, 3, 12]
def baseStart_2221253 : Nat := 118140960795 + 2221253 * 2 ^ 59
def prefixEnd_2221253 : Nat := 4983230072969 + 3 ^ 40 * 2221253 * 2
def baseEnd_2221253 : Nat := 42243349786722335967487

theorem tailTrace_2221253 : CollatzResearch.WordTrace tailWord_2221253 prefixEnd_2221253 42243349786722335967487 := by
  unfold tailWord_2221253
  simp only [CollatzResearch.WordTrace]
  refine ⟨81015752621787215655132413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54010501747858143770088275 81015752621787215655132413)
  ·
    refine ⟨30380907233170205870674655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 81015752621787215655132413 30380907233170205870674655)
    ·
      refine ⟨45571360849755308806011983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30380907233170205870674655 45571360849755308806011983)
      ·
        refine ⟨68357041274632963209017975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45571360849755308806011983 68357041274632963209017975)
        ·
          refine ⟨102535561911949444813526963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68357041274632963209017975 102535561911949444813526963)
          ·
            refine ⟨153803342867924167220290445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 102535561911949444813526963 153803342867924167220290445)
            ·
              refine ⟨57676253575471562707608917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 153803342867924167220290445 57676253575471562707608917)
              ·
                refine ⟨42243349786722335967487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 57676253575471562707608917 42243349786722335967487)
                ·
                  rfl

theorem cell23_2221253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 12].length) (baseStart_2221253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2221253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2221253 prefixEnd_2221253 := by exact prefixLift 2221253
  have htrace : WordTrace (prefixWord ++ tailWord_2221253) baseStart_2221253 baseEnd_2221253 := by
    simpa [prefixWord, tailWord_2221253, baseEnd_2221253] using wordTrace_append hprefix tailTrace_2221253
  have hstable : (prefixWord ++ tailWord_2221253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2221253).length < 2 ^ (prefixWord ++ tailWord_2221253).sum := by decide
  have hdescent : baseEnd_2221253 < baseStart_2221253 := by decide
  rcases family_descends (prefixWord ++ tailWord_2221253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2221287 : List Nat := [1, 1, 5, 3, 2, 2, 9]
def baseStart_2221287 : Nat := 118140960795 + 2221287 * 2 ^ 59
def prefixEnd_2221287 : Nat := 4983230072969 + 3 ^ 40 * 2221287 * 2
def baseEnd_2221287 : Nat := 14081332130663653556753

theorem tailTrace_2221287 : CollatzResearch.WordTrace tailWord_2221287 prefixEnd_2221287 14081332130663653556753 := by
  unfold tailWord_2221287
  simp only [CollatzResearch.WordTrace]
  refine ⟨81016992703664039461870115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54011328469109359641246743 81016992703664039461870115)
  ·
    refine ⟨121525489055496059192805173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81016992703664039461870115 121525489055496059192805173)
    ·
      refine ⟨11393014598952755549325485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 121525489055496059192805173 11393014598952755549325485)
      ·
        refine ⟨4272380474607283330997057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11393014598952755549325485 4272380474607283330997057)
        ·
          refine ⟨3204285355955462498247793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4272380474607283330997057 3204285355955462498247793)
          ·
            refine ⟨2403214016966596873685845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3204285355955462498247793 2403214016966596873685845)
            ·
              refine ⟨14081332130663653556753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2403214016966596873685845 14081332130663653556753)
              ·
                rfl

theorem cell23_2221287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 2, 9].length) (baseStart_2221287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2221287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2221287 prefixEnd_2221287 := by exact prefixLift 2221287
  have htrace : WordTrace (prefixWord ++ tailWord_2221287) baseStart_2221287 baseEnd_2221287 := by
    simpa [prefixWord, tailWord_2221287, baseEnd_2221287] using wordTrace_append hprefix tailTrace_2221287
  have hstable : (prefixWord ++ tailWord_2221287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2221287).length < 2 ^ (prefixWord ++ tailWord_2221287).sum := by decide
  have hdescent : baseEnd_2221287 < baseStart_2221287 := by decide
  rcases family_descends (prefixWord ++ tailWord_2221287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2221298 : List Nat := [3, 2, 1, 3, 3, 2, 1, 1, 3, 2, 2]
def baseStart_2221298 : Nat := 118140960795 + 2221298 * 2 ^ 59
def prefixEnd_2221298 : Nat := 4983230072969 + 3 ^ 40 * 2221298 * 2
def baseEnd_2221298 : Nat := 1140593550870955395059443

theorem tailTrace_2221298 : CollatzResearch.WordTrace tailWord_2221298 prefixEnd_2221298 1140593550870955395059443 := by
  unfold tailWord_2221298
  simp only [CollatzResearch.WordTrace]
  refine ⟨20254348476656047085130137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54011595937749458893680365 20254348476656047085130137)
  ·
    refine ⟨15190761357492035313847603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20254348476656047085130137 15190761357492035313847603)
    ·
      refine ⟨22786142036238052970771405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15190761357492035313847603 22786142036238052970771405)
      ·
        refine ⟨8544803263589269864039277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22786142036238052970771405 8544803263589269864039277)
        ·
          refine ⟨3204301223845976199014729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8544803263589269864039277 3204301223845976199014729)
          ·
            refine ⟨2403225917884482149261047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3204301223845976199014729 2403225917884482149261047)
            ·
              refine ⟨3604838876826723223891571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2403225917884482149261047 3604838876826723223891571)
              ·
                refine ⟨5407258315240084835837357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3604838876826723223891571 5407258315240084835837357)
                ·
                  refine ⟨2027721868215031813439009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5407258315240084835837357 2027721868215031813439009)
                  ·
                    refine ⟨1520791401161273860079257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2027721868215031813439009 1520791401161273860079257)
                    ·
                      refine ⟨1140593550870955395059443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1520791401161273860079257 1140593550870955395059443)
                      ·
                        rfl

theorem cell23_2221298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 2, 1, 1, 3, 2, 2].length) (baseStart_2221298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2221298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2221298 prefixEnd_2221298 := by exact prefixLift 2221298
  have htrace : WordTrace (prefixWord ++ tailWord_2221298) baseStart_2221298 baseEnd_2221298 := by
    simpa [prefixWord, tailWord_2221298, baseEnd_2221298] using wordTrace_append hprefix tailTrace_2221298
  have hstable : (prefixWord ++ tailWord_2221298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2221298).length < 2 ^ (prefixWord ++ tailWord_2221298).sum := by decide
  have hdescent : baseEnd_2221298 < baseStart_2221298 := by decide
  rcases family_descends (prefixWord ++ tailWord_2221298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2221308 : List Nat := [2, 2, 2, 1, 6, 1, 2, 1, 2, 4]
def baseStart_2221308 : Nat := 118140960795 + 2221308 * 2 ^ 59
def prefixEnd_2221308 : Nat := 4983230072969 + 3 ^ 40 * 2221308 * 2
def baseEnd_2221308 : Nat := 380199561892500118644799

theorem tailTrace_2221308 : CollatzResearch.WordTrace tailWord_2221308 prefixEnd_2221308 380199561892500118644799 := by
  unfold tailWord_2221308
  simp only [CollatzResearch.WordTrace]
  refine ⟨40508879318293980024192289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54011839091058640032256385 40508879318293980024192289)
  ·
    refine ⟨30381659488720485018144217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40508879318293980024192289 30381659488720485018144217)
    ·
      refine ⟨22786244616540363763608163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30381659488720485018144217 22786244616540363763608163)
      ·
        refine ⟨34179366924810545645412245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22786244616540363763608163 34179366924810545645412245)
        ·
          refine ⟨1602157824600494327128699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 34179366924810545645412245 1602157824600494327128699)
          ·
            refine ⟨2403236736900741490693049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1602157824600494327128699 2403236736900741490693049)
            ·
              refine ⟨1802427552675556118019787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2403236736900741490693049 1802427552675556118019787)
              ·
                refine ⟨2703641329013334177029681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1802427552675556118019787 2703641329013334177029681)
                ·
                  refine ⟨2027730996760000632772261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2703641329013334177029681 2027730996760000632772261)
                  ·
                    refine ⟨380199561892500118644799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2027730996760000632772261 380199561892500118644799)
                    ·
                      rfl

theorem cell23_2221308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 6, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 6, 1, 2, 1, 2, 4].length) (baseStart_2221308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2221308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2221308 prefixEnd_2221308 := by exact prefixLift 2221308
  have htrace : WordTrace (prefixWord ++ tailWord_2221308) baseStart_2221308 baseEnd_2221308 := by
    simpa [prefixWord, tailWord_2221308, baseEnd_2221308] using wordTrace_append hprefix tailTrace_2221308
  have hstable : (prefixWord ++ tailWord_2221308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2221308).length < 2 ^ (prefixWord ++ tailWord_2221308).sum := by decide
  have hdescent : baseEnd_2221308 < baseStart_2221308 := by decide
  rcases family_descends (prefixWord ++ tailWord_2221308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2221324 : List Nat := [2, 2, 1, 2, 2, 4, 1, 1, 3, 3, 2]
def baseStart_2221324 : Nat := 118140960795 + 2221324 * 2 ^ 59
def prefixEnd_2221324 : Nat := 4983230072969 + 3 ^ 40 * 2221324 * 2
def baseEnd_2221324 : Nat := 1140606901367972293334323

theorem tailTrace_2221324 : CollatzResearch.WordTrace tailWord_2221324 prefixEnd_2221324 1140606901367972293334323 := by
  unfold tailWord_2221324
  simp only [CollatzResearch.WordTrace]
  refine ⟨40509171102264997390483513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54012228136353329853978017 40509171102264997390483513)
  ·
    refine ⟨30381878326698748042862635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40509171102264997390483513 30381878326698748042862635)
    ·
      refine ⟨45572817490048122064293953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30381878326698748042862635 45572817490048122064293953)
      ·
        refine ⟨34179613117536091548220465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45572817490048122064293953 34179613117536091548220465)
        ·
          refine ⟨25634709838152068661165349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34179613117536091548220465 25634709838152068661165349)
          ·
            refine ⟨4806508094653512873968503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25634709838152068661165349 4806508094653512873968503)
            ·
              refine ⟨7209762141980269310952755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4806508094653512873968503 7209762141980269310952755)
              ·
                refine ⟨10814643212970403966429133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7209762141980269310952755 10814643212970403966429133)
                ·
                  refine ⟨4055491204863901487410925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10814643212970403966429133 4055491204863901487410925)
                  ·
                    refine ⟨1520809201823963057779097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4055491204863901487410925 1520809201823963057779097)
                    ·
                      refine ⟨1140606901367972293334323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1520809201823963057779097 1140606901367972293334323)
                      ·
                        rfl

theorem cell23_2221324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 1, 1, 3, 3, 2].length) (baseStart_2221324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2221324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2221324 prefixEnd_2221324 := by exact prefixLift 2221324
  have htrace : WordTrace (prefixWord ++ tailWord_2221324) baseStart_2221324 baseEnd_2221324 := by
    simpa [prefixWord, tailWord_2221324, baseEnd_2221324] using wordTrace_append hprefix tailTrace_2221324
  have hstable : (prefixWord ++ tailWord_2221324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2221324).length < 2 ^ (prefixWord ++ tailWord_2221324).sum := by decide
  have hdescent : baseEnd_2221324 < baseStart_2221324 := by decide
  rcases family_descends (prefixWord ++ tailWord_2221324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2221360 : List Nat := [2, 1, 1, 1, 2, 2, 4, 3, 7]
def baseStart_2221360 : Nat := 118140960795 + 2221360 * 2 ^ 59
def prefixEnd_2221360 : Nat := 4983230072969 + 3 ^ 40 * 2221360 * 2
def baseEnd_2221360 : Nat := 126736154074614905831573

theorem tailTrace_2221360 : CollatzResearch.WordTrace tailWord_2221360 prefixEnd_2221360 126736154074614905831573 := by
  unfold tailWord_2221360
  simp only [CollatzResearch.WordTrace]
  refine ⟨40509827616199786464638767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54013103488266381952851689 40509827616199786464638767)
  ·
    refine ⟨60764741424299679696958151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40509827616199786464638767 60764741424299679696958151)
    ·
      refine ⟨91147112136449519545437227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60764741424299679696958151 91147112136449519545437227)
      ·
        refine ⟨136720668204674279318155841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91147112136449519545437227 136720668204674279318155841)
        ·
          refine ⟨102540501153505709488616881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 136720668204674279318155841 102540501153505709488616881)
          ·
            refine ⟨76905375865129282116462661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 102540501153505709488616881 76905375865129282116462661)
            ·
              refine ⟨14419757974711740396836749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 76905375865129282116462661 14419757974711740396836749)
              ·
                refine ⟨5407409240516902648813781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14419757974711740396836749 5407409240516902648813781)
                ·
                  refine ⟨126736154074614905831573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5407409240516902648813781 126736154074614905831573)
                  ·
                    rfl

theorem cell23_2221360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 4, 3, 7].length) (baseStart_2221360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2221360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2221360 prefixEnd_2221360 := by exact prefixLift 2221360
  have htrace : WordTrace (prefixWord ++ tailWord_2221360) baseStart_2221360 baseEnd_2221360 := by
    simpa [prefixWord, tailWord_2221360, baseEnd_2221360] using wordTrace_append hprefix tailTrace_2221360
  have hstable : (prefixWord ++ tailWord_2221360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2221360).length < 2 ^ (prefixWord ++ tailWord_2221360).sum := by decide
  have hdescent : baseEnd_2221360 < baseStart_2221360 := by decide
  rcases family_descends (prefixWord ++ tailWord_2221360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2221377 : List Nat := [1, 2, 5, 2, 1, 1, 1, 1, 9]
def baseStart_2221377 : Nat := 118140960795 + 2221377 * 2 ^ 59
def prefixEnd_2221377 : Nat := 4983230072969 + 3 ^ 40 * 2221377 * 2
def baseEnd_2221377 : Nat := 126737123982517842885731

theorem tailTrace_2221377 : CollatzResearch.WordTrace tailWord_2221377 prefixEnd_2221377 126737123982517842885731 := by
  unfold tailWord_2221377
  simp only [CollatzResearch.WordTrace]
  refine ⟨81020275273337984832646385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54013516848891989888430923 81020275273337984832646385)
  ·
    refine ⟨60765206455003488624484789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81020275273337984832646385 60765206455003488624484789)
    ·
      refine ⟨5696738105156577058545449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 60765206455003488624484789 5696738105156577058545449)
      ·
        refine ⟨4272553578867432793909087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5696738105156577058545449 4272553578867432793909087)
        ·
          refine ⟨6408830368301149190863631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4272553578867432793909087 6408830368301149190863631)
          ·
            refine ⟨9613245552451723786295447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6408830368301149190863631 9613245552451723786295447)
            ·
              refine ⟨14419868328677585679443171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9613245552451723786295447 14419868328677585679443171)
              ·
                refine ⟨21629802493016378519164757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14419868328677585679443171 21629802493016378519164757)
                ·
                  refine ⟨126737123982517842885731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 21629802493016378519164757 126737123982517842885731)
                  ·
                    rfl

theorem cell23_2221377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 1, 1, 9].length) (baseStart_2221377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2221377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2221377 prefixEnd_2221377 := by exact prefixLift 2221377
  have htrace : WordTrace (prefixWord ++ tailWord_2221377) baseStart_2221377 baseEnd_2221377 := by
    simpa [prefixWord, tailWord_2221377, baseEnd_2221377] using wordTrace_append hprefix tailTrace_2221377
  have hstable : (prefixWord ++ tailWord_2221377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2221377).length < 2 ^ (prefixWord ++ tailWord_2221377).sum := by decide
  have hdescent : baseEnd_2221377 < baseStart_2221377 := by decide
  rcases family_descends (prefixWord ++ tailWord_2221377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2221422 : List Nat := [4, 1, 2, 4, 1, 1, 3, 1, 2, 2, 2]
def baseStart_2221422 : Nat := 118140960795 + 2221422 * 2 ^ 59
def prefixEnd_2221422 : Nat := 4983230072969 + 3 ^ 40 * 2221422 * 2
def baseEnd_2221422 : Nat := 1140657222472112909908873

theorem tailTrace_2221422 : CollatzResearch.WordTrace tailWord_2221422 prefixEnd_2221422 1140657222472112909908873 := by
  unfold tailWord_2221422
  simp only [CollatzResearch.WordTrace]
  refine ⟨10127739569771869689754315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 54014611038783305012023013 10127739569771869689754315)
  ·
    refine ⟨15191609354657804534631473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10127739569771869689754315 15191609354657804534631473)
    ·
      refine ⟨11393707015993353400973605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15191609354657804534631473 11393707015993353400973605)
      ·
        refine ⟨2136320065498753762682551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11393707015993353400973605 2136320065498753762682551)
        ·
          refine ⟨3204480098248130644023827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2136320065498753762682551 3204480098248130644023827)
          ·
            refine ⟨4806720147372195966035741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3204480098248130644023827 4806720147372195966035741)
            ·
              refine ⟨1802520055264573487263403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4806720147372195966035741 1802520055264573487263403)
              ·
                refine ⟨2703780082896860230895105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1802520055264573487263403 2703780082896860230895105)
                ·
                  refine ⟨2027835062172645173171329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2703780082896860230895105 2027835062172645173171329)
                  ·
                    refine ⟨1520876296629483879878497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2027835062172645173171329 1520876296629483879878497)
                    ·
                      refine ⟨1140657222472112909908873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1520876296629483879878497 1140657222472112909908873)
                      ·
                        rfl

theorem cell23_2221422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 3, 1, 2, 2, 2].length) (baseStart_2221422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2221422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2221422 prefixEnd_2221422 := by exact prefixLift 2221422
  have htrace : WordTrace (prefixWord ++ tailWord_2221422) baseStart_2221422 baseEnd_2221422 := by
    simpa [prefixWord, tailWord_2221422, baseEnd_2221422] using wordTrace_append hprefix tailTrace_2221422
  have hstable : (prefixWord ++ tailWord_2221422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2221422).length < 2 ^ (prefixWord ++ tailWord_2221422).sum := by decide
  have hdescent : baseEnd_2221422 < baseStart_2221422 := by decide
  rcases family_descends (prefixWord ++ tailWord_2221422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2221471 : List Nat := [1, 1, 2, 5, 1, 4, 1, 1, 3, 4]
def baseStart_2221471 : Nat := 118140960795 + 2221471 * 2 ^ 59
def prefixEnd_2221471 : Nat := 4983230072969 + 3 ^ 40 * 2221471 * 2
def baseEnd_2221471 : Nat := 380227461008061072732049

theorem tailTrace_2221471 : CollatzResearch.WordTrace tailWord_2221471 prefixEnd_2221471 380227461008061072732049 := by
  unfold tailWord_2221471
  simp only [CollatzResearch.WordTrace]
  refine ⟨81023703734997438886568267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54015802489998292591045511 81023703734997438886568267)
  ·
    refine ⟨121535555602496158329852401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81023703734997438886568267 121535555602496158329852401)
    ·
      refine ⟨91151666701872118747389301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 121535555602496158329852401 91151666701872118747389301)
      ·
        refine ⟨8545468753300511132567747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 91151666701872118747389301 8545468753300511132567747)
        ·
          refine ⟨12818203129950766698851621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8545468753300511132567747 12818203129950766698851621)
          ·
            refine ⟨2403413086865768756034679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12818203129950766698851621 2403413086865768756034679)
            ·
              refine ⟨3605119630298653134052019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2403413086865768756034679 3605119630298653134052019)
              ·
                refine ⟨5407679445447979701078029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3605119630298653134052019 5407679445447979701078029)
                ·
                  refine ⟨2027879792042992387904261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5407679445447979701078029 2027879792042992387904261)
                  ·
                    refine ⟨380227461008061072732049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2027879792042992387904261 380227461008061072732049)
                    ·
                      rfl

theorem cell23_2221471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 4, 1, 1, 3, 4].length) (baseStart_2221471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2221471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2221471 prefixEnd_2221471 := by exact prefixLift 2221471
  have htrace : WordTrace (prefixWord ++ tailWord_2221471) baseStart_2221471 baseEnd_2221471 := by
    simpa [prefixWord, tailWord_2221471, baseEnd_2221471] using wordTrace_append hprefix tailTrace_2221471
  have hstable : (prefixWord ++ tailWord_2221471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2221471).length < 2 ^ (prefixWord ++ tailWord_2221471).sum := by decide
  have hdescent : baseEnd_2221471 < baseStart_2221471 := by decide
  rcases family_descends (prefixWord ++ tailWord_2221471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2221477 : List Nat := [1, 3, 1, 2, 1, 1, 2, 2, 2, 5, 3]
def baseStart_2221477 : Nat := 118140960795 + 2221477 * 2 ^ 59
def prefixEnd_2221477 : Nat := 4983230072969 + 3 ^ 40 * 2221477 * 2
def baseEnd_2221477 : Nat := 1140685463908110194721119

theorem tailTrace_2221477 : CollatzResearch.WordTrace tailWord_2221477 prefixEnd_2221477 1140685463908110194721119 := by
  unfold tailWord_2221477
  simp only [CollatzResearch.WordTrace]
  refine ⟨81023922572975701911286685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54015948381983801274191123 81023922572975701911286685)
  ·
    refine ⟨30383970964865888216732507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 81023922572975701911286685 30383970964865888216732507)
    ·
      refine ⟨45575956447298832325098761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30383970964865888216732507 45575956447298832325098761)
      ·
        refine ⟨34181967335474124243824071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45575956447298832325098761 34181967335474124243824071)
        ·
          refine ⟨51272951003211186365736107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34181967335474124243824071 51272951003211186365736107)
          ·
            refine ⟨76909426504816779548604161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51272951003211186365736107 76909426504816779548604161)
            ·
              refine ⟨57682069878612584661453121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 76909426504816779548604161 57682069878612584661453121)
              ·
                refine ⟨43261552408959438496089841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 57682069878612584661453121 43261552408959438496089841)
                ·
                  refine ⟨32446164306719578872067381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 43261552408959438496089841 32446164306719578872067381)
                  ·
                    refine ⟨3041827903754960519256317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 32446164306719578872067381 3041827903754960519256317)
                    ·
                      refine ⟨1140685463908110194721119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3041827903754960519256317 1140685463908110194721119)
                      ·
                        rfl

theorem cell23_2221477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 2, 2, 5, 3].length) (baseStart_2221477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2221477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2221477 prefixEnd_2221477 := by exact prefixLift 2221477
  have htrace : WordTrace (prefixWord ++ tailWord_2221477) baseStart_2221477 baseEnd_2221477 := by
    simpa [prefixWord, tailWord_2221477, baseEnd_2221477] using wordTrace_append hprefix tailTrace_2221477
  have hstable : (prefixWord ++ tailWord_2221477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2221477).length < 2 ^ (prefixWord ++ tailWord_2221477).sum := by decide
  have hdescent : baseEnd_2221477 < baseStart_2221477 := by decide
  rcases family_descends (prefixWord ++ tailWord_2221477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2221484 : List Nat := [2, 2, 1, 1, 1, 1, 8, 1, 6]
def baseStart_2221484 : Nat := 118140960795 + 2221484 * 2 ^ 59
def prefixEnd_2221484 : Nat := 4983230072969 + 3 ^ 40 * 2221484 * 2
def baseEnd_2221484 : Nat := 126743228696965740814843

theorem tailTrace_2221484 : CollatzResearch.WordTrace tailWord_2221484 prefixEnd_2221484 126743228696965740814843 := by
  unfold tailWord_2221484
  simp only [CollatzResearch.WordTrace]
  refine ⟨40512088941975171053395753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54016118589300228071194337 40512088941975171053395753)
  ·
    refine ⟨30384066706481378290046815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40512088941975171053395753 30384066706481378290046815)
    ·
      refine ⟨45576100059722067435070223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30384066706481378290046815 45576100059722067435070223)
      ·
        refine ⟨68364150089583101152605335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45576100059722067435070223 68364150089583101152605335)
        ·
          refine ⟨102546225134374651728908003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68364150089583101152605335 102546225134374651728908003)
          ·
            refine ⟨153819337701561977593362005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 102546225134374651728908003 153819337701561977593362005)
            ·
              refine ⟨1802570363690179424922211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 153819337701561977593362005 1802570363690179424922211)
              ·
                refine ⟨2703855545535269137383317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1802570363690179424922211 2703855545535269137383317)
                ·
                  refine ⟨126743228696965740814843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2703855545535269137383317 126743228696965740814843)
                  ·
                    rfl

theorem cell23_2221484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 6].length) (baseStart_2221484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2221484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2221484 prefixEnd_2221484 := by exact prefixLift 2221484
  have htrace : WordTrace (prefixWord ++ tailWord_2221484) baseStart_2221484 baseEnd_2221484 := by
    simpa [prefixWord, tailWord_2221484, baseEnd_2221484] using wordTrace_append hprefix tailTrace_2221484
  have hstable : (prefixWord ++ tailWord_2221484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2221484).length < 2 ^ (prefixWord ++ tailWord_2221484).sum := by decide
  have hdescent : baseEnd_2221484 < baseStart_2221484 := by decide
  rcases family_descends (prefixWord ++ tailWord_2221484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2221504 : List Nat := [2, 1, 1, 2, 3, 1, 2, 3, 1, 5, 2]
def baseStart_2221504 : Nat := 118140960795 + 2221504 * 2 ^ 59
def prefixEnd_2221504 : Nat := 4983230072969 + 3 ^ 40 * 2221504 * 2
def baseEnd_2221504 : Nat := 1140699327885781589083495

theorem tailTrace_2221504 : CollatzResearch.WordTrace tailWord_2221504 prefixEnd_2221504 1140699327885781589083495 := by
  unfold tailWord_2221504
  simp only [CollatzResearch.WordTrace]
  refine ⟨40512453671938942761259783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54016604895918590348346377 40512453671938942761259783)
  ·
    refine ⟨60768680507908414141889675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40512453671938942761259783 60768680507908414141889675)
    ·
      refine ⟨91153020761862621212834513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60768680507908414141889675 91153020761862621212834513)
      ·
        refine ⟨68364765571396965909625885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 91153020761862621212834513 68364765571396965909625885)
        ·
          refine ⟨25636787089273862216109707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 68364765571396965909625885 25636787089273862216109707)
          ·
            refine ⟨38455180633910793324164561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25636787089273862216109707 38455180633910793324164561)
            ·
              refine ⟨28841385475433094993123421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38455180633910793324164561 28841385475433094993123421)
              ·
                refine ⟨10815519553287410622421283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28841385475433094993123421 10815519553287410622421283)
                ·
                  refine ⟨16223279329931115933631925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10815519553287410622421283 16223279329931115933631925)
                  ·
                    refine ⟨1520932437181042118777993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 16223279329931115933631925 1520932437181042118777993)
                    ·
                      refine ⟨1140699327885781589083495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1520932437181042118777993 1140699327885781589083495)
                      ·
                        rfl

theorem cell23_2221504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 3, 1, 5, 2].length) (baseStart_2221504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2221504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2221504 prefixEnd_2221504 := by exact prefixLift 2221504
  have htrace : WordTrace (prefixWord ++ tailWord_2221504) baseStart_2221504 baseEnd_2221504 := by
    simpa [prefixWord, tailWord_2221504, baseEnd_2221504] using wordTrace_append hprefix tailTrace_2221504
  have hstable : (prefixWord ++ tailWord_2221504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2221504).length < 2 ^ (prefixWord ++ tailWord_2221504).sum := by decide
  have hdescent : baseEnd_2221504 < baseStart_2221504 := by decide
  rcases family_descends (prefixWord ++ tailWord_2221504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2221544 : List Nat := [2, 1, 4, 1, 1, 2, 4, 1, 1, 6]
def baseStart_2221544 : Nat := 118140960795 + 2221544 * 2 ^ 59
def prefixEnd_2221544 : Nat := 4983230072969 + 3 ^ 40 * 2221544 * 2
def baseEnd_2221544 : Nat := 380239955703987144194437

theorem tailTrace_2221544 : CollatzResearch.WordTrace tailWord_2221544 prefixEnd_2221544 380239955703987144194437 := by
  unfold tailWord_2221544
  simp only [CollatzResearch.WordTrace]
  refine ⟨40513183131866486176987843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54017577509155314902650457 40513183131866486176987843)
  ·
    refine ⟨60769774697799729265481765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40513183131866486176987843 60769774697799729265481765)
    ·
      refine ⟨11394332755837449237277831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 60769774697799729265481765 11394332755837449237277831)
      ·
        refine ⟨17091499133756173855916747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11394332755837449237277831 17091499133756173855916747)
        ·
          refine ⟨25637248700634260783875121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17091499133756173855916747 25637248700634260783875121)
          ·
            refine ⟨19227936525475695587906341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25637248700634260783875121 19227936525475695587906341)
            ·
              refine ⟨3605238098526692922732439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19227936525475695587906341 3605238098526692922732439)
              ·
                refine ⟨5407857147790039384098659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3605238098526692922732439 5407857147790039384098659)
                ·
                  refine ⟨8111785721685059076147989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5407857147790039384098659 8111785721685059076147989)
                  ·
                    refine ⟨380239955703987144194437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8111785721685059076147989 380239955703987144194437)
                    ·
                      rfl

theorem cell23_2221544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 4, 1, 1, 6].length) (baseStart_2221544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2221544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2221544 prefixEnd_2221544 := by exact prefixLift 2221544
  have htrace : WordTrace (prefixWord ++ tailWord_2221544) baseStart_2221544 baseEnd_2221544 := by
    simpa [prefixWord, tailWord_2221544, baseEnd_2221544] using wordTrace_append hprefix tailTrace_2221544
  have hstable : (prefixWord ++ tailWord_2221544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2221544).length < 2 ^ (prefixWord ++ tailWord_2221544).sum := by decide
  have hdescent : baseEnd_2221544 < baseStart_2221544 := by decide
  rcases family_descends (prefixWord ++ tailWord_2221544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2221551 : List Nat := [1, 1, 2, 1, 4, 1, 3, 1, 5, 2, 2]
def baseStart_2221551 : Nat := 118140960795 + 2221551 * 2 ^ 59
def prefixEnd_2221551 : Nat := 4983230072969 + 3 ^ 40 * 2221551 * 2
def baseEnd_2221551 : Nat := 1140723461476542905195779

theorem tailTrace_2221551 : CollatzResearch.WordTrace tailWord_2221551 prefixEnd_2221551 1140723461476542905195779 := by
  unfold tailWord_2221551
  simp only [CollatzResearch.WordTrace]
  refine ⟨81026621574707612549480507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54017747716471741699653671 81026621574707612549480507)
  ·
    refine ⟨121539932362061418824220761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81026621574707612549480507 121539932362061418824220761)
    ·
      refine ⟨91154949271546064118165571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 121539932362061418824220761 91154949271546064118165571)
      ·
        refine ⟨136732423907319096177248357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91154949271546064118165571 136732423907319096177248357)
        ·
          refine ⟨25637329482622330533234067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 136732423907319096177248357 25637329482622330533234067)
          ·
            refine ⟨38455994223933495799851101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25637329482622330533234067 38455994223933495799851101)
            ·
              refine ⟨14420997833975060924944163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38455994223933495799851101 14420997833975060924944163)
              ·
                refine ⟨21631496750962591387416245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14420997833975060924944163 21631496750962591387416245)
                ·
                  refine ⟨2027952820402742942570273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 21631496750962591387416245 2027952820402742942570273)
                  ·
                    refine ⟨1520964615302057206927705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2027952820402742942570273 1520964615302057206927705)
                    ·
                      refine ⟨1140723461476542905195779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1520964615302057206927705 1140723461476542905195779)
                      ·
                        rfl

theorem cell23_2221551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 3, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 3, 1, 5, 2, 2].length) (baseStart_2221551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2221551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2221551 prefixEnd_2221551 := by exact prefixLift 2221551
  have htrace : WordTrace (prefixWord ++ tailWord_2221551) baseStart_2221551 baseEnd_2221551 := by
    simpa [prefixWord, tailWord_2221551, baseEnd_2221551] using wordTrace_append hprefix tailTrace_2221551
  have hstable : (prefixWord ++ tailWord_2221551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2221551).length < 2 ^ (prefixWord ++ tailWord_2221551).sum := by decide
  have hdescent : baseEnd_2221551 < baseStart_2221551 := by decide
  rcases family_descends (prefixWord ++ tailWord_2221551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2221564 : List Nat := [2, 2, 2, 1, 2, 1, 4, 2, 1, 2, 4]
def baseStart_2221564 : Nat := 118140960795 + 2221564 * 2 ^ 59
def prefixEnd_2221564 : Nat := 4983230072969 + 3 ^ 40 * 2221564 * 2
def baseEnd_2221564 : Nat := 1140730136725051354333219

theorem tailTrace_2221564 : CollatzResearch.WordTrace tailWord_2221564 prefixEnd_2221564 1140730136725051354333219 := by
  unfold tailWord_2221564
  simp only [CollatzResearch.WordTrace]
  refine ⟨40513547861830257884851873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54018063815773677179802497 40513547861830257884851873)
  ·
    refine ⟨30385160896372693413638905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40513547861830257884851873 30385160896372693413638905)
    ·
      refine ⟨22788870672279520060229179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30385160896372693413638905 22788870672279520060229179)
      ·
        refine ⟨34183306008419280090343769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22788870672279520060229179 34183306008419280090343769)
        ·
          refine ⟨25637479506314460067757827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34183306008419280090343769 25637479506314460067757827)
          ·
            refine ⟨38456219259471690101636741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25637479506314460067757827 38456219259471690101636741)
            ·
              refine ⟨7210541111150941894056889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 38456219259471690101636741 7210541111150941894056889)
              ·
                refine ⟨5407905833363206420542667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7210541111150941894056889 5407905833363206420542667)
                ·
                  refine ⟨8111858750044809630814001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5407905833363206420542667 8111858750044809630814001)
                  ·
                    refine ⟨6083894062533607223110501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8111858750044809630814001 6083894062533607223110501)
                    ·
                      refine ⟨1140730136725051354333219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6083894062533607223110501 1140730136725051354333219)
                      ·
                        rfl

theorem cell23_2221564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 4, 2, 1, 2, 4].length) (baseStart_2221564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2221564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2221564 prefixEnd_2221564 := by exact prefixLift 2221564
  have htrace : WordTrace (prefixWord ++ tailWord_2221564) baseStart_2221564 baseEnd_2221564 := by
    simpa [prefixWord, tailWord_2221564, baseEnd_2221564] using wordTrace_append hprefix tailTrace_2221564
  have hstable : (prefixWord ++ tailWord_2221564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2221564).length < 2 ^ (prefixWord ++ tailWord_2221564).sum := by decide
  have hdescent : baseEnd_2221564 < baseStart_2221564 := by decide
  rcases family_descends (prefixWord ++ tailWord_2221564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2221578 : List Nat := [3, 1, 2, 2, 2, 4, 1, 2, 2, 4]
def baseStart_2221578 : Nat := 118140960795 + 2221578 * 2 ^ 59
def prefixEnd_2221578 : Nat := 4983230072969 + 3 ^ 40 * 2221578 * 2
def baseEnd_2221578 : Nat := 380245775151404766519385

theorem tailTrace_2221578 : CollatzResearch.WordTrace tailWord_2221578 prefixEnd_2221578 380245775151404766519385 := by
  unfold tailWord_2221578
  simp only [CollatzResearch.WordTrace]
  refine ⟨20256901586402449040178347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54018404230406530773808925 20256901586402449040178347)
  ·
    refine ⟨30385352379603673560267521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20256901586402449040178347 30385352379603673560267521)
    ·
      refine ⟨22789014284702755170200641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30385352379603673560267521 22789014284702755170200641)
      ·
        refine ⟨17091760713527066377650481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22789014284702755170200641 17091760713527066377650481)
        ·
          refine ⟨12818820535145299783237861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17091760713527066377650481 12818820535145299783237861)
          ·
            refine ⟨2403528850339743709357099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12818820535145299783237861 2403528850339743709357099)
            ·
              refine ⟨3605293275509615564035649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2403528850339743709357099 3605293275509615564035649)
              ·
                refine ⟨2703969956632211673026737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3605293275509615564035649 2703969956632211673026737)
                ·
                  refine ⟨2027977467474158754770053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2703969956632211673026737 2027977467474158754770053)
                  ·
                    refine ⟨380245775151404766519385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2027977467474158754770053 380245775151404766519385)
                    ·
                      rfl

theorem cell23_2221578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 4, 1, 2, 2, 4].length) (baseStart_2221578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2221578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2221578 prefixEnd_2221578 := by exact prefixLift 2221578
  have htrace : WordTrace (prefixWord ++ tailWord_2221578) baseStart_2221578 baseEnd_2221578 := by
    simpa [prefixWord, tailWord_2221578, baseEnd_2221578] using wordTrace_append hprefix tailTrace_2221578
  have hstable : (prefixWord ++ tailWord_2221578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2221578).length < 2 ^ (prefixWord ++ tailWord_2221578).sum := by decide
  have hdescent : baseEnd_2221578 < baseStart_2221578 := by decide
  rcases family_descends (prefixWord ++ tailWord_2221578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2221588 : List Nat := [2, 4, 3, 1, 2, 1, 1, 2, 1, 1, 5]
def baseStart_2221588 : Nat := 118140960795 + 2221588 * 2 ^ 59
def prefixEnd_2221588 : Nat := 4983230072969 + 3 ^ 40 * 2221588 * 2
def baseEnd_2221588 : Nat := 1140742460260759260433109

theorem tailTrace_2221588 : CollatzResearch.WordTrace tailWord_2221588 prefixEnd_2221588 1140742460260759260433109 := by
  unfold tailWord_2221588
  simp only [CollatzResearch.WordTrace]
  refine ⟨40513985537786783934288709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54018647383715711912384945 40513985537786783934288709)
  ·
    refine ⟨7596372288335021987679133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 40513985537786783934288709 7596372288335021987679133)
    ·
      refine ⟨2848639608125633245379675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7596372288335021987679133 2848639608125633245379675)
      ·
        refine ⟨4272959412188449868069513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2848639608125633245379675 4272959412188449868069513)
        ·
          refine ⟨3204719559141337401052135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4272959412188449868069513 3204719559141337401052135)
          ·
            refine ⟨4807079338712006101578203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3204719559141337401052135 4807079338712006101578203)
            ·
              refine ⟨7210619008068009152367305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4807079338712006101578203 7210619008068009152367305)
              ·
                refine ⟨5407964256051006864275479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7210619008068009152367305 5407964256051006864275479)
                ·
                  refine ⟨8111946384076510296413219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5407964256051006864275479 8111946384076510296413219)
                  ·
                    refine ⟨12167919576114765444619829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8111946384076510296413219 12167919576114765444619829)
                    ·
                      refine ⟨1140742460260759260433109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12167919576114765444619829 1140742460260759260433109)
                      ·
                        rfl

theorem cell23_2221588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 1, 2, 1, 1, 5].length) (baseStart_2221588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2221588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2221588 prefixEnd_2221588 := by exact prefixLift 2221588
  have htrace : WordTrace (prefixWord ++ tailWord_2221588) baseStart_2221588 baseEnd_2221588 := by
    simpa [prefixWord, tailWord_2221588, baseEnd_2221588] using wordTrace_append hprefix tailTrace_2221588
  have hstable : (prefixWord ++ tailWord_2221588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2221588).length < 2 ^ (prefixWord ++ tailWord_2221588).sum := by decide
  have hdescent : baseEnd_2221588 < baseStart_2221588 := by decide
  rcases family_descends (prefixWord ++ tailWord_2221588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2221601 : List Nat := [1, 2, 3, 2, 2, 2, 3, 1, 1, 3, 3]
def baseStart_2221601 : Nat := 118140960795 + 2221601 * 2 ^ 59
def prefixEnd_2221601 : Nat := 4983230072969 + 3 ^ 40 * 2221601 * 2
def baseEnd_2221601 : Nat := 1140749135509267709570549

theorem tailTrace_2221601 : CollatzResearch.WordTrace tailWord_2221601 prefixEnd_2221601 1140749135509267709570549 := by
  unfold tailWord_2221601
  simp only [CollatzResearch.WordTrace]
  refine ⟨81028445224526471088800657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54018963483017647392533771 81028445224526471088800657)
  ·
    refine ⟨60771333918394853316600493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81028445224526471088800657 60771333918394853316600493)
    ·
      refine ⟨22789250219398069993725185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 60771333918394853316600493 22789250219398069993725185)
      ·
        refine ⟨17091937664548552495293889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22789250219398069993725185 17091937664548552495293889)
        ·
          refine ⟨12818953248411414371470417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17091937664548552495293889 12818953248411414371470417)
          ·
            refine ⟨9614214936308560778602813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12818953248411414371470417 9614214936308560778602813)
            ·
              refine ⟨3605330601115710291976055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9614214936308560778602813 3605330601115710291976055)
              ·
                refine ⟨5407995901673565437964083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3605330601115710291976055 5407995901673565437964083)
                ·
                  refine ⟨8111993852510348156946125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5407995901673565437964083 8111993852510348156946125)
                  ·
                    refine ⟨3041997694691380558854797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8111993852510348156946125 3041997694691380558854797)
                    ·
                      refine ⟨1140749135509267709570549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3041997694691380558854797 1140749135509267709570549)
                      ·
                        rfl

theorem cell23_2221601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 3, 1, 1, 3, 3].length) (baseStart_2221601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2221601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2221601 prefixEnd_2221601 := by exact prefixLift 2221601
  have htrace : WordTrace (prefixWord ++ tailWord_2221601) baseStart_2221601 baseEnd_2221601 := by
    simpa [prefixWord, tailWord_2221601, baseEnd_2221601] using wordTrace_append hprefix tailTrace_2221601
  have hstable : (prefixWord ++ tailWord_2221601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2221601).length < 2 ^ (prefixWord ++ tailWord_2221601).sum := by decide
  have hdescent : baseEnd_2221601 < baseStart_2221601 := by decide
  rcases family_descends (prefixWord ++ tailWord_2221601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2221608 : List Nat := [2, 1, 5, 2, 2, 2, 2, 7]
def baseStart_2221608 : Nat := 118140960795 + 2221608 * 2 ^ 59
def prefixEnd_2221608 : Nat := 4983230072969 + 3 ^ 40 * 2221608 * 2
def baseEnd_2221608 : Nat := 42250101106438858599371

theorem tailTrace_2221608 : CollatzResearch.WordTrace tailWord_2221608 prefixEnd_2221608 42250101106438858599371 := by
  unfold tailWord_2221608
  simp only [CollatzResearch.WordTrace]
  refine ⟨40514350267750555642152739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54019133690334074189536985 40514350267750555642152739)
  ·
    refine ⟨60771525401625833463229109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40514350267750555642152739 60771525401625833463229109)
    ·
      refine ⟨5697330506402421887177729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 60771525401625833463229109 5697330506402421887177729)
      ·
        refine ⟨4272997879801816415383297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5697330506402421887177729 4272997879801816415383297)
        ·
          refine ⟨3204748409851362311537473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4272997879801816415383297 3204748409851362311537473)
          ·
            refine ⟨2403561307388521733653105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3204748409851362311537473 2403561307388521733653105)
            ·
              refine ⟨1802670980541391300239829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2403561307388521733653105 1802670980541391300239829)
              ·
                refine ⟨42250101106438858599371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1802670980541391300239829 42250101106438858599371)
                ·
                  rfl

theorem cell23_2221608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 2, 2, 7].length) (baseStart_2221608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2221608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2221608 prefixEnd_2221608 := by exact prefixLift 2221608
  have htrace : WordTrace (prefixWord ++ tailWord_2221608) baseStart_2221608 baseEnd_2221608 := by
    simpa [prefixWord, tailWord_2221608, baseEnd_2221608] using wordTrace_append hprefix tailTrace_2221608
  have hstable : (prefixWord ++ tailWord_2221608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2221608).length < 2 ^ (prefixWord ++ tailWord_2221608).sum := by decide
  have hdescent : baseEnd_2221608 < baseStart_2221608 := by decide
  rcases family_descends (prefixWord ++ tailWord_2221608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2221701 : List Nat := [1, 3, 1, 1, 4, 1, 1, 1, 1, 7, 2]
def baseStart_2221701 : Nat := 118140960795 + 2221701 * 2 ^ 59
def prefixEnd_2221701 : Nat := 4983230072969 + 3 ^ 40 * 2221701 * 2
def baseEnd_2221701 : Nat := 1140800483574717318320089

theorem tailTrace_2221701 : CollatzResearch.WordTrace tailWord_2221701 prefixEnd_2221701 1140800483574717318320089 := by
  unfold tailWord_2221701
  simp only [CollatzResearch.WordTrace]
  refine ⟨81032092524164188167440957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54021395016109458778293971 81032092524164188167440957)
  ·
    refine ⟨30387034696561570562790359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 81032092524164188167440957 30387034696561570562790359)
    ·
      refine ⟨45580552044842355844185539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30387034696561570562790359 45580552044842355844185539)
      ·
        refine ⟨68370828067263533766278309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45580552044842355844185539 68370828067263533766278309)
        ·
          refine ⟨12819530262611912581177183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 68370828067263533766278309 12819530262611912581177183)
          ·
            refine ⟨19229295393917868871765775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12819530262611912581177183 19229295393917868871765775)
            ·
              refine ⟨28843943090876803307648663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19229295393917868871765775 28843943090876803307648663)
              ·
                refine ⟨43265914636315204961472995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28843943090876803307648663 43265914636315204961472995)
                ·
                  refine ⟨64898871954472807442209493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 43265914636315204961472995 64898871954472807442209493)
                  ·
                    refine ⟨1521067311432956424426785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 64898871954472807442209493 1521067311432956424426785)
                    ·
                      refine ⟨1140800483574717318320089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1521067311432956424426785 1140800483574717318320089)
                      ·
                        rfl

theorem cell23_2221701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 1, 1, 7, 2].length) (baseStart_2221701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2221701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2221701 prefixEnd_2221701 := by exact prefixLift 2221701
  have htrace : WordTrace (prefixWord ++ tailWord_2221701) baseStart_2221701 baseEnd_2221701 := by
    simpa [prefixWord, tailWord_2221701, baseEnd_2221701] using wordTrace_append hprefix tailTrace_2221701
  have hstable : (prefixWord ++ tailWord_2221701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2221701).length < 2 ^ (prefixWord ++ tailWord_2221701).sum := by decide
  have hdescent : baseEnd_2221701 < baseStart_2221701 := by decide
  rcases family_descends (prefixWord ++ tailWord_2221701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2221728 : List Nat := [2, 1, 1, 4, 3, 3, 1, 1, 2, 5]
def baseStart_2221728 : Nat := 118140960795 + 2221728 * 2 ^ 59
def prefixEnd_2221728 : Nat := 4983230072969 + 3 ^ 40 * 2221728 * 2
def baseEnd_2221728 : Nat := 380271449184129570894155

theorem tailTrace_2221728 : CollatzResearch.WordTrace tailWord_2221728 prefixEnd_2221728 380271449184129570894155 := by
  unfold tailWord_2221728
  simp only [CollatzResearch.WordTrace]
  refine ⟨40516538647533185889336919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54022051530044247852449225 40516538647533185889336919)
  ·
    refine ⟨60774807971299778834005379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40516538647533185889336919 60774807971299778834005379)
    ·
      refine ⟨91162211956949668251008069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60774807971299778834005379 91162211956949668251008069)
      ·
        refine ⟨17092914741928062797064013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 91162211956949668251008069 17092914741928062797064013)
        ·
          refine ⟨6409843028223023548899005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17092914741928062797064013 6409843028223023548899005)
          ·
            refine ⟨2403691135583633830837127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6409843028223023548899005 2403691135583633830837127)
            ·
              refine ⟨3605536703375450746255691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2403691135583633830837127 3605536703375450746255691)
              ·
                refine ⟨5408305055063176119383537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3605536703375450746255691 5408305055063176119383537)
                ·
                  refine ⟨4056228791297382089537653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5408305055063176119383537 4056228791297382089537653)
                  ·
                    refine ⟨380271449184129570894155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4056228791297382089537653 380271449184129570894155)
                    ·
                      rfl

theorem cell23_2221728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 3, 1, 1, 2, 5].length) (baseStart_2221728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2221728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2221728 prefixEnd_2221728 := by exact prefixLift 2221728
  have htrace : WordTrace (prefixWord ++ tailWord_2221728) baseStart_2221728 baseEnd_2221728 := by
    simpa [prefixWord, tailWord_2221728, baseEnd_2221728] using wordTrace_append hprefix tailTrace_2221728
  have hstable : (prefixWord ++ tailWord_2221728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2221728).length < 2 ^ (prefixWord ++ tailWord_2221728).sum := by decide
  have hdescent : baseEnd_2221728 < baseStart_2221728 := by decide
  rcases family_descends (prefixWord ++ tailWord_2221728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2221731 : List Nat := [1, 1, 1, 4, 1, 1, 3, 2, 1, 6, 2]
def baseStart_2221731 : Nat := 118140960795 + 2221731 * 2 ^ 59
def prefixEnd_2221731 : Nat := 4983230072969 + 3 ^ 40 * 2221731 * 2
def baseEnd_2221731 : Nat := 1140815887994352200944951

theorem tailTrace_2221731 : CollatzResearch.WordTrace tailWord_2221731 prefixEnd_2221731 1140815887994352200944951 := by
  unfold tailWord_2221731
  simp only [CollatzResearch.WordTrace]
  refine ⟨81033186714055503291033047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54022124476037002194022031 81033186714055503291033047)
  ·
    refine ⟨121549780071083254936549571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81033186714055503291033047 121549780071083254936549571)
    ·
      refine ⟨182324670106624882404824357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121549780071083254936549571 182324670106624882404824357)
      ·
        refine ⟨34185875644992165450904567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 182324670106624882404824357 34185875644992165450904567)
        ·
          refine ⟨51278813467488248176356851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34185875644992165450904567 51278813467488248176356851)
          ·
            refine ⟨76918220201232372264535277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51278813467488248176356851 76918220201232372264535277)
            ·
              refine ⟨28844332575462139599200729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 76918220201232372264535277 28844332575462139599200729)
              ·
                refine ⟨21633249431596604699400547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28844332575462139599200729 21633249431596604699400547)
                ·
                  refine ⟨32449874147394907049100821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21633249431596604699400547 32449874147394907049100821)
                  ·
                    refine ⟨1521087850659136267926601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 32449874147394907049100821 1521087850659136267926601)
                    ·
                      refine ⟨1140815887994352200944951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1521087850659136267926601 1140815887994352200944951)
                      ·
                        rfl

theorem cell23_2221731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 2, 1, 6, 2].length) (baseStart_2221731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2221731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2221731 prefixEnd_2221731 := by exact prefixLift 2221731
  have htrace : WordTrace (prefixWord ++ tailWord_2221731) baseStart_2221731 baseEnd_2221731 := by
    simpa [prefixWord, tailWord_2221731, baseEnd_2221731] using wordTrace_append hprefix tailTrace_2221731
  have hstable : (prefixWord ++ tailWord_2221731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2221731).length < 2 ^ (prefixWord ++ tailWord_2221731).sum := by decide
  have hdescent : baseEnd_2221731 < baseStart_2221731 := by decide
  rcases family_descends (prefixWord ++ tailWord_2221731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2221744 : List Nat := [2, 1, 1, 1, 2, 1, 5, 1, 2, 1, 6]
def baseStart_2221744 : Nat := 118140960795 + 2221744 * 2 ^ 59
def prefixEnd_2221744 : Nat := 4983230072969 + 3 ^ 40 * 2221744 * 2
def baseEnd_2221744 : Nat := 1140822563242860650082391

theorem tailTrace_2221744 : CollatzResearch.WordTrace tailWord_2221744 prefixEnd_2221744 1140822563242860650082391 := by
  unfold tailWord_2221744
  simp only [CollatzResearch.WordTrace]
  refine ⟨40516830431504203255628143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54022440575338937674170857 40516830431504203255628143)
  ·
    refine ⟨60775245647256304883442215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40516830431504203255628143 60775245647256304883442215)
    ·
      refine ⟨91162868470884457325163323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60775245647256304883442215 91162868470884457325163323)
      ·
        refine ⟨136744302706326685987744985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91162868470884457325163323 136744302706326685987744985)
        ·
          refine ⟨102558227029745014490808739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 136744302706326685987744985 102558227029745014490808739)
          ·
            refine ⟨153837340544617521736213109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 102558227029745014490808739 153837340544617521736213109)
            ·
              refine ⟨14422250676057892662769979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 153837340544617521736213109 14422250676057892662769979)
              ·
                refine ⟨21633376014086838994154969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14422250676057892662769979 21633376014086838994154969)
                ·
                  refine ⟨16225032010565129245616227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21633376014086838994154969 16225032010565129245616227)
                  ·
                    refine ⟨24337548015847693868424341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16225032010565129245616227 24337548015847693868424341)
                    ·
                      refine ⟨1140822563242860650082391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 24337548015847693868424341 1140822563242860650082391)
                      ·
                        rfl

theorem cell23_2221744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 5, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 5, 1, 2, 1, 6].length) (baseStart_2221744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2221744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2221744 prefixEnd_2221744 := by exact prefixLift 2221744
  have htrace : WordTrace (prefixWord ++ tailWord_2221744) baseStart_2221744 baseEnd_2221744 := by
    simpa [prefixWord, tailWord_2221744, baseEnd_2221744] using wordTrace_append hprefix tailTrace_2221744
  have hstable : (prefixWord ++ tailWord_2221744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2221744).length < 2 ^ (prefixWord ++ tailWord_2221744).sum := by decide
  have hdescent : baseEnd_2221744 < baseStart_2221744 := by decide
  rcases family_descends (prefixWord ++ tailWord_2221744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2221758 : List Nat := [4, 2, 1, 1, 2, 2, 1, 3, 3, 4]
def baseStart_2221758 : Nat := 118140960795 + 2221758 * 2 ^ 59
def prefixEnd_2221758 : Nat := 4983230072969 + 3 ^ 40 * 2221758 * 2
def baseEnd_2221758 : Nat := 380276583990674531769109

theorem tailTrace_2221758 : CollatzResearch.WordTrace tailWord_2221758 prefixEnd_2221758 380276583990674531769109 := by
  unfold tailWord_2221758
  simp only [CollatzResearch.WordTrace]
  refine ⟨10129271435619710862783241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 54022780989971791268177285 10129271435619710862783241)
  ·
    refine ⟨7596953576714783147087431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10129271435619710862783241 7596953576714783147087431)
    ·
      refine ⟨11395430365072174720631147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7596953576714783147087431 11395430365072174720631147)
      ·
        refine ⟨17093145547608262080946721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11395430365072174720631147 17093145547608262080946721)
        ·
          refine ⟨12819859160706196560710041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17093145547608262080946721 12819859160706196560710041)
          ·
            refine ⟨9614894370529647420532531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12819859160706196560710041 9614894370529647420532531)
            ·
              refine ⟨14422341555794471130798797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9614894370529647420532531 14422341555794471130798797)
              ·
                refine ⟨5408378083422926674049549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14422341555794471130798797 5408378083422926674049549)
                ·
                  refine ⟨2028141781283597502768581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5408378083422926674049549 2028141781283597502768581)
                  ·
                    refine ⟨380276583990674531769109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2028141781283597502768581 380276583990674531769109)
                    ·
                      rfl

theorem cell23_2221758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 1, 3, 3, 4].length) (baseStart_2221758 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2221758 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2221758 prefixEnd_2221758 := by exact prefixLift 2221758
  have htrace : WordTrace (prefixWord ++ tailWord_2221758) baseStart_2221758 baseEnd_2221758 := by
    simpa [prefixWord, tailWord_2221758, baseEnd_2221758] using wordTrace_append hprefix tailTrace_2221758
  have hstable : (prefixWord ++ tailWord_2221758).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2221758).length < 2 ^ (prefixWord ++ tailWord_2221758).sum := by decide
  have hdescent : baseEnd_2221758 < baseStart_2221758 := by decide
  rcases family_descends (prefixWord ++ tailWord_2221758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2221815 : List Nat := [1, 1, 3, 1, 1, 1, 4, 6, 1, 1, 3]
def baseStart_2221815 : Nat := 118140960795 + 2221815 * 2 ^ 59
def prefixEnd_2221815 : Nat := 4983230072969 + 3 ^ 40 * 2221815 * 2
def baseEnd_2221815 : Nat := 1140859020369329872294565

theorem tailTrace_2221815 : CollatzResearch.WordTrace tailWord_2221815 prefixEnd_2221815 1140859020369329872294565 := by
  unfold tailWord_2221815
  simp only [CollatzResearch.WordTrace]
  refine ⟨81036250445751185637090899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54024166963834123758060599 81036250445751185637090899)
  ·
    refine ⟨121554375668626778455636349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81036250445751185637090899 121554375668626778455636349)
    ·
      refine ⟨45582890875735041920863631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 121554375668626778455636349 45582890875735041920863631)
      ·
        refine ⟨68374336313602562881295447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45582890875735041920863631 68374336313602562881295447)
        ·
          refine ⟨102561504470403844321943171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68374336313602562881295447 102561504470403844321943171)
          ·
            refine ⟨153842256705605766482914757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 102561504470403844321943171 153842256705605766482914757)
            ·
              refine ⟨28845423132301081215546517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 153842256705605766482914757 28845423132301081215546517)
              ·
                refine ⟨1352129209326613181978743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 28845423132301081215546517 1352129209326613181978743)
                ·
                  refine ⟨2028193813989919772968115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1352129209326613181978743 2028193813989919772968115)
                  ·
                    refine ⟨3042290720984879659452173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2028193813989919772968115 3042290720984879659452173)
                    ·
                      refine ⟨1140859020369329872294565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3042290720984879659452173 1140859020369329872294565)
                      ·
                        rfl

theorem cell23_2221815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 6, 1, 1, 3].length) (baseStart_2221815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2221815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2221815 prefixEnd_2221815 := by exact prefixLift 2221815
  have htrace : WordTrace (prefixWord ++ tailWord_2221815) baseStart_2221815 baseEnd_2221815 := by
    simpa [prefixWord, tailWord_2221815, baseEnd_2221815] using wordTrace_append hprefix tailTrace_2221815
  have hstable : (prefixWord ++ tailWord_2221815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2221815).length < 2 ^ (prefixWord ++ tailWord_2221815).sum := by decide
  have hdescent : baseEnd_2221815 < baseStart_2221815 := by decide
  rcases family_descends (prefixWord ++ tailWord_2221815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2221822 : List Nat := [4, 2, 2, 1, 3, 2, 2, 1, 6]
def baseStart_2221822 : Nat := 118140960795 + 2221822 * 2 ^ 59
def prefixEnd_2221822 : Nat := 4983230072969 + 3 ^ 40 * 2221822 * 2
def baseEnd_2221822 : Nat := 126762512748212371656337

theorem tailTrace_2221822 : CollatzResearch.WordTrace tailWord_2221822 prefixEnd_2221822 126762512748212371656337 := by
  unfold tailWord_2221822
  simp only [CollatzResearch.WordTrace]
  refine ⟨10129563219590728229074465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 54024337171150550555063813 10129563219590728229074465)
  ·
    refine ⟨7597172414693046171805849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10129563219590728229074465 7597172414693046171805849)
    ·
      refine ⟨5697879311019784628854387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7597172414693046171805849 5697879311019784628854387)
      ·
        refine ⟨8546818966529676943281581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5697879311019784628854387 8546818966529676943281581)
        ·
          refine ⟨3205057112448628853730593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8546818966529676943281581 3205057112448628853730593)
          ·
            refine ⟨2403792834336471640297945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3205057112448628853730593 2403792834336471640297945)
            ·
              refine ⟨1802844625752353730223459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2403792834336471640297945 1802844625752353730223459)
              ·
                refine ⟨2704266938628530595335189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1802844625752353730223459 2704266938628530595335189)
                ·
                  refine ⟨126762512748212371656337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2704266938628530595335189 126762512748212371656337)
                  ·
                    rfl

theorem cell23_2221822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 2, 2, 1, 6].length) (baseStart_2221822 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2221822 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2221822 prefixEnd_2221822 := by exact prefixLift 2221822
  have htrace : WordTrace (prefixWord ++ tailWord_2221822) baseStart_2221822 baseEnd_2221822 := by
    simpa [prefixWord, tailWord_2221822, baseEnd_2221822] using wordTrace_append hprefix tailTrace_2221822
  have hstable : (prefixWord ++ tailWord_2221822).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2221822).length < 2 ^ (prefixWord ++ tailWord_2221822).sum := by decide
  have hdescent : baseEnd_2221822 < baseStart_2221822 := by decide
  rcases family_descends (prefixWord ++ tailWord_2221822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2221838 : List Nat := [4, 1, 1, 2, 1, 1, 2, 1, 2, 6, 2]
def baseStart_2221838 : Nat := 118140960795 + 2221838 * 2 ^ 59
def prefixEnd_2221838 : Nat := 4983230072969 + 3 ^ 40 * 2221838 * 2
def baseEnd_2221838 : Nat := 1140870830424383282306959

theorem tailTrace_2221838 : CollatzResearch.WordTrace tailWord_2221838 prefixEnd_2221838 1140870830424383282306959 := by
  unfold tailWord_2221838
  simp only [CollatzResearch.WordTrace]
  refine ⟨10129636165583482570647271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 54024726216445240376785445 10129636165583482570647271)
  ·
    refine ⟨15194454248375223855970907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10129636165583482570647271 15194454248375223855970907)
    ·
      refine ⟨22791681372562835783956361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15194454248375223855970907 22791681372562835783956361)
      ·
        refine ⟨17093761029422126837967271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22791681372562835783956361 17093761029422126837967271)
        ·
          refine ⟨25640641544133190256950907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17093761029422126837967271 25640641544133190256950907)
          ·
            refine ⟨38460962316199785385426361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25640641544133190256950907 38460962316199785385426361)
            ·
              refine ⟨28845721737149839039069771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38460962316199785385426361 28845721737149839039069771)
              ·
                refine ⟨43268582605724758558604657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28845721737149839039069771 43268582605724758558604657)
                ·
                  refine ⟨32451436954293568918953493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 43268582605724758558604657 32451436954293568918953493)
                  ·
                    refine ⟨1521161107232511043075945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 32451436954293568918953493 1521161107232511043075945)
                    ·
                      refine ⟨1140870830424383282306959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1521161107232511043075945 1140870830424383282306959)
                      ·
                        rfl

theorem cell23_2221838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 1, 2, 6, 2].length) (baseStart_2221838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2221838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2221838 prefixEnd_2221838 := by exact prefixLift 2221838
  have htrace : WordTrace (prefixWord ++ tailWord_2221838) baseStart_2221838 baseEnd_2221838 := by
    simpa [prefixWord, tailWord_2221838, baseEnd_2221838] using wordTrace_append hprefix tailTrace_2221838
  have hstable : (prefixWord ++ tailWord_2221838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2221838).length < 2 ^ (prefixWord ++ tailWord_2221838).sum := by decide
  have hdescent : baseEnd_2221838 < baseStart_2221838 := by decide
  rcases family_descends (prefixWord ++ tailWord_2221838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2221842 : List Nat := [3, 2, 4, 1, 1, 1, 1, 3, 2, 3, 2]
def baseStart_2221842 : Nat := 118140960795 + 2221842 * 2 ^ 59
def prefixEnd_2221842 : Nat := 4983230072969 + 3 ^ 40 * 2221842 * 2
def baseEnd_2221842 : Nat := 1140872884347001266656941

theorem tailTrace_2221842 : CollatzResearch.WordTrace tailWord_2221842 prefixEnd_2221842 1140872884347001266656941 := by
  unfold tailWord_2221842
  simp only [CollatzResearch.WordTrace]
  refine ⟨20259308804163342312080945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54024823477768912832215853 20259308804163342312080945)
  ·
    refine ⟨15194481603122506734060709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20259308804163342312080945 15194481603122506734060709)
    ·
      refine ⟨2848965300585470012636383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15194481603122506734060709 2848965300585470012636383)
      ·
        refine ⟨4273447950878205018954575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2848965300585470012636383 4273447950878205018954575)
        ·
          refine ⟨6410171926317307528431863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4273447950878205018954575 6410171926317307528431863)
          ·
            refine ⟨9615257889475961292647795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6410171926317307528431863 9615257889475961292647795)
            ·
              refine ⟨14422886834213941938971693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9615257889475961292647795 14422886834213941938971693)
              ·
                refine ⟨5408582562830228227114385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14422886834213941938971693 5408582562830228227114385)
                ·
                  refine ⟨4056436922122671170335789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5408582562830228227114385 4056436922122671170335789)
                  ·
                    refine ⟨1521163845796001688875921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4056436922122671170335789 1521163845796001688875921)
                    ·
                      refine ⟨1140872884347001266656941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1521163845796001688875921 1140872884347001266656941)
                      ·
                        rfl

theorem cell23_2221842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 1, 3, 2, 3, 2].length) (baseStart_2221842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2221842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2221842 prefixEnd_2221842 := by exact prefixLift 2221842
  have htrace : WordTrace (prefixWord ++ tailWord_2221842) baseStart_2221842 baseEnd_2221842 := by
    simpa [prefixWord, tailWord_2221842, baseEnd_2221842] using wordTrace_append hprefix tailTrace_2221842
  have hstable : (prefixWord ++ tailWord_2221842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2221842).length < 2 ^ (prefixWord ++ tailWord_2221842).sum := by decide
  have hdescent : baseEnd_2221842 < baseStart_2221842 := by decide
  rcases family_descends (prefixWord ++ tailWord_2221842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2221851 : List Nat := [1, 1, 1, 1, 1, 1, 4, 6, 1, 2, 4]
def baseStart_2221851 : Nat := 118140960795 + 2221851 * 2 ^ 59
def prefixEnd_2221851 : Nat := 4983230072969 + 3 ^ 40 * 2221851 * 2
def baseEnd_2221851 : Nat := 1140877505672891731444399

theorem tailTrace_2221851 : CollatzResearch.WordTrace tailWord_2221851 prefixEnd_2221851 1140877505672891731444399 := by
  unfold tailWord_2221851
  simp only [CollatzResearch.WordTrace]
  refine ⟨81037563473620763785401407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54025042315747175856934271 81037563473620763785401407)
  ·
    refine ⟨121556345210431145678102111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81037563473620763785401407 121556345210431145678102111)
    ·
      refine ⟨182334517815646718517153167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121556345210431145678102111 182334517815646718517153167)
      ·
        refine ⟨273501776723470077775729751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 182334517815646718517153167 273501776723470077775729751)
        ·
          refine ⟨410252665085205116663594627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 273501776723470077775729751 410252665085205116663594627)
          ·
            refine ⟨615378997627807674995391941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 410252665085205116663594627 615378997627807674995391941)
            ·
              refine ⟨115383562055213939061635989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 615378997627807674995391941 115383562055213939061635989)
              ·
                refine ⟨5408604471338153393514187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 115383562055213939061635989 5408604471338153393514187)
                ·
                  refine ⟨8112906707007230090271281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5408604471338153393514187 8112906707007230090271281)
                  ·
                    refine ⟨6084680030255422567703461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8112906707007230090271281 6084680030255422567703461)
                    ·
                      refine ⟨1140877505672891731444399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6084680030255422567703461 1140877505672891731444399)
                      ·
                        rfl

theorem cell23_2221851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 6, 1, 2, 4].length) (baseStart_2221851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2221851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2221851 prefixEnd_2221851 := by exact prefixLift 2221851
  have htrace : WordTrace (prefixWord ++ tailWord_2221851) baseStart_2221851 baseEnd_2221851 := by
    simpa [prefixWord, tailWord_2221851, baseEnd_2221851] using wordTrace_append hprefix tailTrace_2221851
  have hstable : (prefixWord ++ tailWord_2221851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2221851).length < 2 ^ (prefixWord ++ tailWord_2221851).sum := by decide
  have hdescent : baseEnd_2221851 < baseStart_2221851 := by decide
  rcases family_descends (prefixWord ++ tailWord_2221851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2221855 : List Nat := [1, 1, 2, 4, 2, 1, 5, 1, 1, 1, 4]
def baseStart_2221855 : Nat := 118140960795 + 2221855 * 2 ^ 59
def prefixEnd_2221855 : Nat := 4983230072969 + 3 ^ 40 * 2221855 * 2
def baseEnd_2221855 : Nat := 1140879559595509715794381

theorem tailTrace_2221855 : CollatzResearch.WordTrace tailWord_2221855 prefixEnd_2221855 1140879559595509715794381 := by
  unfold tailWord_2221855
  simp only [CollatzResearch.WordTrace]
  refine ⟨81037709365606272468547019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54025139577070848312364679 81037709365606272468547019)
  ·
    refine ⟨121556564048409408702820529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81037709365606272468547019 121556564048409408702820529)
    ·
      refine ⟨91167423036307056527115397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 121556564048409408702820529 91167423036307056527115397)
      ·
        refine ⟨17093891819307573098834137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 91167423036307056527115397 17093891819307573098834137)
        ·
          refine ⟨12820418864480679824125603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17093891819307573098834137 12820418864480679824125603)
          ·
            refine ⟨19230628296721019736188405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12820418864480679824125603 19230628296721019736188405)
            ·
              refine ⟨1802871402817595600267663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 19230628296721019736188405 1802871402817595600267663)
              ·
                refine ⟨2704307104226393400401495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1802871402817595600267663 2704307104226393400401495)
                ·
                  refine ⟨4056460656339590100602243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2704307104226393400401495 4056460656339590100602243)
                  ·
                    refine ⟨6084690984509385150903365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4056460656339590100602243 6084690984509385150903365)
                    ·
                      refine ⟨1140879559595509715794381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6084690984509385150903365 1140879559595509715794381)
                      ·
                        rfl

theorem cell23_2221855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 5, 1, 1, 1, 4].length) (baseStart_2221855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2221855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2221855 prefixEnd_2221855 := by exact prefixLift 2221855
  have htrace : WordTrace (prefixWord ++ tailWord_2221855) baseStart_2221855 baseEnd_2221855 := by
    simpa [prefixWord, tailWord_2221855, baseEnd_2221855] using wordTrace_append hprefix tailTrace_2221855
  have hstable : (prefixWord ++ tailWord_2221855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2221855).length < 2 ^ (prefixWord ++ tailWord_2221855).sum := by decide
  have hdescent : baseEnd_2221855 < baseStart_2221855 := by decide
  rcases family_descends (prefixWord ++ tailWord_2221855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2221885 : List Nat := [1, 4, 1, 4, 1, 2, 2, 1, 1, 2, 4]
def baseStart_2221885 : Nat := 118140960795 + 2221885 * 2 ^ 59
def prefixEnd_2221885 : Nat := 4983230072969 + 3 ^ 40 * 2221885 * 2
def baseEnd_2221885 : Nat := 1140894964015144598419243

theorem tailTrace_2221885 : CollatzResearch.WordTrace tailWord_2221885 prefixEnd_2221885 1140894964015144598419243 := by
  unfold tailWord_2221885
  simp only [CollatzResearch.WordTrace]
  refine ⟨81038803555497587592139109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54025869036998391728092739 81038803555497587592139109)
  ·
    refine ⟨15194775666655797673526083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 81038803555497587592139109 15194775666655797673526083)
    ·
      refine ⟨22792163499983696510289125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15194775666655797673526083 22792163499983696510289125)
      ·
        refine ⟨4273530656246943095679211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22792163499983696510289125 4273530656246943095679211)
        ·
          refine ⟨6410295984370414643518817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4273530656246943095679211 6410295984370414643518817)
          ·
            refine ⟨4807721988277810982639113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6410295984370414643518817 4807721988277810982639113)
            ·
              refine ⟨3605791491208358236979335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4807721988277810982639113 3605791491208358236979335)
              ·
                refine ⟨5408687236812537355469003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3605791491208358236979335 5408687236812537355469003)
                ·
                  refine ⟨8113030855218806033203505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5408687236812537355469003 8113030855218806033203505)
                  ·
                    refine ⟨6084773141414104524902629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8113030855218806033203505 6084773141414104524902629)
                    ·
                      refine ⟨1140894964015144598419243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6084773141414104524902629 1140894964015144598419243)
                      ·
                        rfl

theorem cell23_2221885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 2, 1, 1, 2, 4].length) (baseStart_2221885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2221885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2221885 prefixEnd_2221885 := by exact prefixLift 2221885
  have htrace : WordTrace (prefixWord ++ tailWord_2221885) baseStart_2221885 baseEnd_2221885 := by
    simpa [prefixWord, tailWord_2221885, baseEnd_2221885] using wordTrace_append hprefix tailTrace_2221885
  have hstable : (prefixWord ++ tailWord_2221885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2221885).length < 2 ^ (prefixWord ++ tailWord_2221885).sum := by decide
  have hdescent : baseEnd_2221885 < baseStart_2221885 := by decide
  rcases family_descends (prefixWord ++ tailWord_2221885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2221888 : List Nat := [2, 1, 1, 2, 2, 1, 1, 1, 8, 1, 3]
def baseStart_2221888 : Nat := 118140960795 + 2221888 * 2 ^ 59
def prefixEnd_2221888 : Nat := 4983230072969 + 3 ^ 40 * 2221888 * 2
def baseEnd_2221888 : Nat := 1140896504457108086681729

theorem tailTrace_2221888 : CollatzResearch.WordTrace tailWord_2221888 prefixEnd_2221888 1140896504457108086681729 := by
  unfold tailWord_2221888
  simp only [CollatzResearch.WordTrace]
  refine ⟨40519456487243359552249159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54025941982991146069665545 40519456487243359552249159)
  ·
    refine ⟨60779184730865039328373739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40519456487243359552249159 60779184730865039328373739)
    ·
      refine ⟨91168777096297558992560609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60779184730865039328373739 91168777096297558992560609)
      ·
        refine ⟨68376582822223169244420457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 91168777096297558992560609 68376582822223169244420457)
        ·
          refine ⟨51282437116667376933315343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 68376582822223169244420457 51282437116667376933315343)
          ·
            refine ⟨76923655675001065399973015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51282437116667376933315343 76923655675001065399973015)
            ·
              refine ⟨115385483512501598099959523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 76923655675001065399973015 115385483512501598099959523)
              ·
                refine ⟨173078225268752397149939285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 115385483512501598099959523 173078225268752397149939285)
                ·
                  refine ⟨2028260452368192154100851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 173078225268752397149939285 2028260452368192154100851)
                  ·
                    refine ⟨3042390678552288231151277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2028260452368192154100851 3042390678552288231151277)
                    ·
                      refine ⟨1140896504457108086681729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3042390678552288231151277 1140896504457108086681729)
                      ·
                        rfl

theorem cell23_2221888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 1, 8, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 1, 8, 1, 3].length) (baseStart_2221888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2221888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2221888 prefixEnd_2221888 := by exact prefixLift 2221888
  have htrace : WordTrace (prefixWord ++ tailWord_2221888) baseStart_2221888 baseEnd_2221888 := by
    simpa [prefixWord, tailWord_2221888, baseEnd_2221888] using wordTrace_append hprefix tailTrace_2221888
  have hstable : (prefixWord ++ tailWord_2221888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2221888).length < 2 ^ (prefixWord ++ tailWord_2221888).sum := by decide
  have hdescent : baseEnd_2221888 < baseStart_2221888 := by decide
  rcases family_descends (prefixWord ++ tailWord_2221888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2221921 : List Nat := [1, 2, 3, 1, 1, 1, 3, 1, 4, 6]
def baseStart_2221921 : Nat := 118140960795 + 2221921 * 2 ^ 59
def prefixEnd_2221921 : Nat := 4983230072969 + 3 ^ 40 * 2221921 * 2
def baseEnd_2221921 : Nat := 380304483106235485856359

theorem tailTrace_2221921 : CollatzResearch.WordTrace tailWord_2221921 prefixEnd_2221921 380304483106235485856359 := by
  unfold tailWord_2221921
  simp only [CollatzResearch.WordTrace]
  refine ⟨81040116583367165740449617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54026744388911443826966411 81040116583367165740449617)
  ·
    refine ⟨60780087437525374305337213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81040116583367165740449617 60780087437525374305337213)
    ·
      refine ⟨22792532789072015364501455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 60780087437525374305337213 22792532789072015364501455)
      ·
        refine ⟨34188799183608023046752183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22792532789072015364501455 34188799183608023046752183)
        ·
          refine ⟨51283198775412034570128275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34188799183608023046752183 51283198775412034570128275)
          ·
            refine ⟨76924798163118051855192413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51283198775412034570128275 76924798163118051855192413)
            ·
              refine ⟨28846799311169269445697155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 76924798163118051855192413 28846799311169269445697155)
              ·
                refine ⟨43270198966753904168545733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28846799311169269445697155 43270198966753904168545733)
                ·
                  refine ⟨8113162306266357031602325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 43270198966753904168545733 8113162306266357031602325)
                  ·
                    refine ⟨380304483106235485856359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8113162306266357031602325 380304483106235485856359)
                    ·
                      rfl

theorem cell23_2221921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 1, 4, 6].length) (baseStart_2221921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2221921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2221921 prefixEnd_2221921 := by exact prefixLift 2221921
  have htrace : WordTrace (prefixWord ++ tailWord_2221921) baseStart_2221921 baseEnd_2221921 := by
    simpa [prefixWord, tailWord_2221921, baseEnd_2221921] using wordTrace_append hprefix tailTrace_2221921
  have hstable : (prefixWord ++ tailWord_2221921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2221921).length < 2 ^ (prefixWord ++ tailWord_2221921).sum := by decide
  have hdescent : baseEnd_2221921 < baseStart_2221921 := by decide
  rcases family_descends (prefixWord ++ tailWord_2221921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2221922 : List Nat := [3, 3, 2, 1, 2, 2, 1, 1, 4, 1, 3]
def baseStart_2221922 : Nat := 118140960795 + 2221922 * 2 ^ 59
def prefixEnd_2221922 : Nat := 4983230072969 + 3 ^ 40 * 2221922 * 2
def baseEnd_2221922 : Nat := 1140913962799360953656573

theorem tailTrace_2221922 : CollatzResearch.WordTrace tailWord_2221922 prefixEnd_2221922 1140913962799360953656573 := by
  unfold tailWord_2221922
  simp only [CollatzResearch.WordTrace]
  refine ⟨20260038264090885727809005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54026768704242361940824013 20260038264090885727809005)
  ·
    refine ⟨7597514349034082147928377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20260038264090885727809005 7597514349034082147928377)
    ·
      refine ⟨5698135761775561610946283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7597514349034082147928377 5698135761775561610946283)
      ·
        refine ⟨8547203642663342416419425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5698135761775561610946283 8547203642663342416419425)
        ·
          refine ⟨6410402731997506812314569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8547203642663342416419425 6410402731997506812314569)
          ·
            refine ⟨4807802048998130109235927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6410402731997506812314569 4807802048998130109235927)
            ·
              refine ⟨7211703073497195163853891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4807802048998130109235927 7211703073497195163853891)
              ·
                refine ⟨10817554610245792745780837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7211703073497195163853891 10817554610245792745780837)
                ·
                  refine ⟨2028291489421086139833907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10817554610245792745780837 2028291489421086139833907)
                  ·
                    refine ⟨3042437234131629209750861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2028291489421086139833907 3042437234131629209750861)
                    ·
                      refine ⟨1140913962799360953656573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3042437234131629209750861 1140913962799360953656573)
                      ·
                        rfl

theorem cell23_2221922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 1, 1, 4, 1, 3].length) (baseStart_2221922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2221922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2221922 prefixEnd_2221922 := by exact prefixLift 2221922
  have htrace : WordTrace (prefixWord ++ tailWord_2221922) baseStart_2221922 baseEnd_2221922 := by
    simpa [prefixWord, tailWord_2221922, baseEnd_2221922] using wordTrace_append hprefix tailTrace_2221922
  have hstable : (prefixWord ++ tailWord_2221922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2221922).length < 2 ^ (prefixWord ++ tailWord_2221922).sum := by decide
  have hdescent : baseEnd_2221922 < baseStart_2221922 := by decide
  rcases family_descends (prefixWord ++ tailWord_2221922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2221931 : List Nat := [1, 1, 1, 1, 2, 2, 3, 2, 4, 1, 5]
def baseStart_2221931 : Nat := 118140960795 + 2221931 * 2 ^ 59
def prefixEnd_2221931 : Nat := 4983230072969 + 3 ^ 40 * 2221931 * 2
def baseEnd_2221931 : Nat := 1140918584125251418444031

theorem tailTrace_2221931 : CollatzResearch.WordTrace tailWord_2221931 prefixEnd_2221931 1140918584125251418444031 := by
  unfold tailWord_2221931
  simp only [CollatzResearch.WordTrace]
  refine ⟨81040481313330937448313647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54026987542220624965542431 81040481313330937448313647)
  ·
    refine ⟨121560721969996406172470471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81040481313330937448313647 121560721969996406172470471)
    ·
      refine ⟨182341082954994609258705707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121560721969996406172470471 182341082954994609258705707)
      ·
        refine ⟨273511624432491913888058561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 182341082954994609258705707 273511624432491913888058561)
        ·
          refine ⟨205133718324368935416043921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 273511624432491913888058561 205133718324368935416043921)
          ·
            refine ⟨153850288743276701562032941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 205133718324368935416043921 153850288743276701562032941)
            ·
              refine ⟨57693858278728763085762353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 153850288743276701562032941 57693858278728763085762353)
              ·
                refine ⟨43270393709046572314321765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 57693858278728763085762353 43270393709046572314321765)
                ·
                  refine ⟨8113198820446232308935331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 43270393709046572314321765 8113198820446232308935331)
                  ·
                    refine ⟨12169798230669348463402997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8113198820446232308935331 12169798230669348463402997)
                    ·
                      refine ⟨1140918584125251418444031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12169798230669348463402997 1140918584125251418444031)
                      ·
                        rfl

theorem cell23_2221931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 2, 4, 1, 5].length) (baseStart_2221931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2221931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2221931 prefixEnd_2221931 := by exact prefixLift 2221931
  have htrace : WordTrace (prefixWord ++ tailWord_2221931) baseStart_2221931 baseEnd_2221931 := by
    simpa [prefixWord, tailWord_2221931, baseEnd_2221931] using wordTrace_append hprefix tailTrace_2221931
  have hstable : (prefixWord ++ tailWord_2221931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2221931).length < 2 ^ (prefixWord ++ tailWord_2221931).sum := by decide
  have hdescent : baseEnd_2221931 < baseStart_2221931 := by decide
  rcases family_descends (prefixWord ++ tailWord_2221931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2222011 : List Nat := [1, 1, 1, 1, 1, 2, 2, 3, 1, 10]
def baseStart_2222011 : Nat := 118140960795 + 2222011 * 2 ^ 59
def prefixEnd_2222011 : Nat := 4983230072969 + 3 ^ 40 * 2222011 * 2
def baseEnd_2222011 : Nat := 380319887525870368481221

theorem tailTrace_2222011 : CollatzResearch.WordTrace tailWord_2222011 prefixEnd_2222011 380319887525870368481221 := by
  unfold tailWord_2222011
  simp only [CollatzResearch.WordTrace]
  refine ⟨81043399153041111111225887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54028932768694074074150591 81043399153041111111225887)
  ·
    refine ⟨121565098729561666666838831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81043399153041111111225887 121565098729561666666838831)
    ·
      refine ⟨182347648094342500000258247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121565098729561666666838831 182347648094342500000258247)
      ·
        refine ⟨273521472141513750000387371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 182347648094342500000258247 273521472141513750000387371)
        ·
          refine ⟨410282208212270625000581057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 273521472141513750000387371 410282208212270625000581057)
          ·
            refine ⟨307711656159202968750435793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 410282208212270625000581057 307711656159202968750435793)
            ·
              refine ⟨230783742119402226562826845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 307711656159202968750435793 230783742119402226562826845)
              ·
                refine ⟨86543903294775834961060067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 230783742119402226562826845 86543903294775834961060067)
                ·
                  refine ⟨129815854942163752441590101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 86543903294775834961060067 129815854942163752441590101)
                  ·
                    refine ⟨380319887525870368481221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 129815854942163752441590101 380319887525870368481221)
                    ·
                      rfl

theorem cell23_2222011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 1, 10].length) (baseStart_2222011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2222011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2222011 prefixEnd_2222011 := by exact prefixLift 2222011
  have htrace : WordTrace (prefixWord ++ tailWord_2222011) baseStart_2222011 baseEnd_2222011 := by
    simpa [prefixWord, tailWord_2222011, baseEnd_2222011] using wordTrace_append hprefix tailTrace_2222011
  have hstable : (prefixWord ++ tailWord_2222011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2222011).length < 2 ^ (prefixWord ++ tailWord_2222011).sum := by decide
  have hdescent : baseEnd_2222011 < baseStart_2222011 := by decide
  rcases family_descends (prefixWord ++ tailWord_2222011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2222062 : List Nat := [4, 1, 2, 1, 3, 2, 1, 2, 3, 4]
def baseStart_2222062 : Nat := 118140960795 + 2222062 * 2 ^ 59
def prefixEnd_2222062 : Nat := 4983230072969 + 3 ^ 40 * 2222062 * 2
def baseEnd_2222062 : Nat := 380328616696996801968643

theorem tailTrace_2222062 : CollatzResearch.WordTrace tailWord_2222062 prefixEnd_2222062 380328616696996801968643 := by
  unfold tailWord_2222062
  simp only [CollatzResearch.WordTrace]
  refine ⟨10130657409482043352666555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 54030172850570897880888293 10130657409482043352666555)
  ·
    refine ⟨15195986114223065028999833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10130657409482043352666555 15195986114223065028999833)
    ·
      refine ⟨11396989585667298771749875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15195986114223065028999833 11396989585667298771749875)
      ·
        refine ⟨17095484378500948157624813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11396989585667298771749875 17095484378500948157624813)
        ·
          refine ⟨6410806641937855559109305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17095484378500948157624813 6410806641937855559109305)
          ·
            refine ⟨4808104981453391669331979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6410806641937855559109305 4808104981453391669331979)
            ·
              refine ⟨7212157472180087503997969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4808104981453391669331979 7212157472180087503997969)
              ·
                refine ⟨5409118104135065627998477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7212157472180087503997969 5409118104135065627998477)
                ·
                  refine ⟨2028419289050649610499429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5409118104135065627998477 2028419289050649610499429)
                  ·
                    refine ⟨380328616696996801968643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2028419289050649610499429 380328616696996801968643)
                    ·
                      rfl

theorem cell23_2222062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 1, 2, 3, 4].length) (baseStart_2222062 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2222062 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2222062 prefixEnd_2222062 := by exact prefixLift 2222062
  have htrace : WordTrace (prefixWord ++ tailWord_2222062) baseStart_2222062 baseEnd_2222062 := by
    simpa [prefixWord, tailWord_2222062, baseEnd_2222062] using wordTrace_append hprefix tailTrace_2222062
  have hstable : (prefixWord ++ tailWord_2222062).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2222062).length < 2 ^ (prefixWord ++ tailWord_2222062).sum := by decide
  have hdescent : baseEnd_2222062 < baseStart_2222062 := by decide
  rcases family_descends (prefixWord ++ tailWord_2222062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2222122 : List Nat := [3, 1, 4, 1, 2, 1, 1, 4, 1, 5]
def baseStart_2222122 : Nat := 118140960795 + 2222122 * 2 ^ 59
def prefixEnd_2222122 : Nat := 4983230072969 + 3 ^ 40 * 2222122 * 2
def baseEnd_2222122 : Nat := 380338886310086723718551

theorem tailTrace_2222122 : CollatzResearch.WordTrace tailWord_2222122 prefixEnd_2222122 380338886310086723718551 := by
  unfold tailWord_2222122
  simp only [CollatzResearch.WordTrace]
  refine ⟨20261861913909744267129155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54031631770425984712344413 20261861913909744267129155)
  ·
    refine ⟨30392792870864616400693733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20261861913909744267129155 30392792870864616400693733)
    ·
      refine ⟨5698648663287115575130075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 30392792870864616400693733 5698648663287115575130075)
      ·
        refine ⟨8547972994930673362695113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5698648663287115575130075 8547972994930673362695113)
        ·
          refine ⟨6410979746198005022021335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8547972994930673362695113 6410979746198005022021335)
          ·
            refine ⟨9616469619297007533032003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6410979746198005022021335 9616469619297007533032003)
            ·
              refine ⟨14424704428945511299548005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9616469619297007533032003 14424704428945511299548005)
              ·
                refine ⟨2704632080427283368665251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14424704428945511299548005 2704632080427283368665251)
                ·
                  refine ⟨4056948120640925052997877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2704632080427283368665251 4056948120640925052997877)
                  ·
                    refine ⟨380338886310086723718551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4056948120640925052997877 380338886310086723718551)
                    ·
                      rfl

theorem cell23_2222122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 1, 4, 1, 5].length) (baseStart_2222122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2222122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2222122 prefixEnd_2222122 := by exact prefixLift 2222122
  have htrace : WordTrace (prefixWord ++ tailWord_2222122) baseStart_2222122 baseEnd_2222122 := by
    simpa [prefixWord, tailWord_2222122, baseEnd_2222122] using wordTrace_append hprefix tailTrace_2222122
  have hstable : (prefixWord ++ tailWord_2222122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2222122).length < 2 ^ (prefixWord ++ tailWord_2222122).sum := by decide
  have hdescent : baseEnd_2222122 < baseStart_2222122 := by decide
  rcases family_descends (prefixWord ++ tailWord_2222122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2222135 : List Nat := [1, 1, 3, 1, 2, 2, 3, 2, 4, 4]
def baseStart_2222135 : Nat := 118140960795 + 2222135 * 2 ^ 59
def prefixEnd_2222135 : Nat := 4983230072969 + 3 ^ 40 * 2222135 * 2
def baseEnd_2222135 : Nat := 380341111392922873431031

theorem tailTrace_2222135 : CollatzResearch.WordTrace tailWord_2222135 prefixEnd_2222135 380341111392922873431031 := by
  unfold tailWord_2222135
  simp only [CollatzResearch.WordTrace]
  refine ⟨81047921804591880288739859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54031947869727920192493239 81047921804591880288739859)
  ·
    refine ⟨121571882706887820433109789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81047921804591880288739859 121571882706887820433109789)
    ·
      refine ⟨45589456015082932662416171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 121571882706887820433109789 45589456015082932662416171)
      ·
        refine ⟨68384184022624398993624257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45589456015082932662416171 68384184022624398993624257)
        ·
          refine ⟨51288138016968299245218193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 68384184022624398993624257 51288138016968299245218193)
          ·
            refine ⟨38466103512726224433913645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51288138016968299245218193 38466103512726224433913645)
            ·
              refine ⟨14424788817272334162717617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38466103512726224433913645 14424788817272334162717617)
              ·
                refine ⟨10818591612954250622038213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14424788817272334162717617 10818591612954250622038213)
                ·
                  refine ⟨2028485927428921991632165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10818591612954250622038213 2028485927428921991632165)
                  ·
                    refine ⟨380341111392922873431031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2028485927428921991632165 380341111392922873431031)
                    ·
                      rfl

theorem cell23_2222135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 3, 2, 4, 4].length) (baseStart_2222135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2222135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2222135 prefixEnd_2222135 := by exact prefixLift 2222135
  have htrace : WordTrace (prefixWord ++ tailWord_2222135) baseStart_2222135 baseEnd_2222135 := by
    simpa [prefixWord, tailWord_2222135, baseEnd_2222135] using wordTrace_append hprefix tailTrace_2222135
  have hstable : (prefixWord ++ tailWord_2222135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2222135).length < 2 ^ (prefixWord ++ tailWord_2222135).sum := by decide
  have hdescent : baseEnd_2222135 < baseStart_2222135 := by decide
  rcases family_descends (prefixWord ++ tailWord_2222135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2222165 : List Nat := [1, 3, 2, 2, 1, 4, 2, 8]
def baseStart_2222165 : Nat := 118140960795 + 2222165 * 2 ^ 59
def prefixEnd_2222165 : Nat := 4983230072969 + 3 ^ 40 * 2222165 * 2
def baseEnd_2222165 : Nat := 42260694022163092700665

theorem tailTrace_2222165 : CollatzResearch.WordTrace tailWord_2222165 prefixEnd_2222165 42260694022163092700665 := by
  unfold tailWord_2222165
  simp only [CollatzResearch.WordTrace]
  refine ⟨81049015994483195412331949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54032677329655463608221299 81049015994483195412331949)
  ·
    refine ⟨30393380997931198279624481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 81049015994483195412331949 30393380997931198279624481)
    ·
      refine ⟨22795035748448398709718361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30393380997931198279624481 22795035748448398709718361)
      ·
        refine ⟨17096276811336299032288771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22795035748448398709718361 17096276811336299032288771)
        ·
          refine ⟨25644415217004448548433157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17096276811336299032288771 25644415217004448548433157)
          ·
            refine ⟨4808327853188334102831217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25644415217004448548433157 4808327853188334102831217)
            ·
              refine ⟨3606245889891250577123413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4808327853188334102831217 3606245889891250577123413)
              ·
                refine ⟨42260694022163092700665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3606245889891250577123413 42260694022163092700665)
                ·
                  rfl

theorem cell23_2222165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 2, 8].length) (baseStart_2222165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2222165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2222165 prefixEnd_2222165 := by exact prefixLift 2222165
  have htrace : WordTrace (prefixWord ++ tailWord_2222165) baseStart_2222165 baseEnd_2222165 := by
    simpa [prefixWord, tailWord_2222165, baseEnd_2222165] using wordTrace_append hprefix tailTrace_2222165
  have hstable : (prefixWord ++ tailWord_2222165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2222165).length < 2 ^ (prefixWord ++ tailWord_2222165).sum := by decide
  have hdescent : baseEnd_2222165 < baseStart_2222165 := by decide
  rcases family_descends (prefixWord ++ tailWord_2222165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2222192 : List Nat := [2, 1, 1, 1, 5, 3, 1, 2, 1, 3, 3]
def baseStart_2222192 : Nat := 118140960795 + 2222192 * 2 ^ 59
def prefixEnd_2222192 : Nat := 4983230072969 + 3 ^ 40 * 2222192 * 2
def baseEnd_2222192 : Nat := 1141052602576074897280331

theorem tailTrace_2222192 : CollatzResearch.WordTrace tailWord_2222192 prefixEnd_2222192 1141052602576074897280331 := by
  unfold tailWord_2222192
  simp only [CollatzResearch.WordTrace]
  refine ⟨40525000382692689511782415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54033333843590252682376553 40525000382692689511782415)
  ·
    refine ⟨60787500574039034267673623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40525000382692689511782415 60787500574039034267673623)
    ·
      refine ⟨91181250861058551401510435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60787500574039034267673623 91181250861058551401510435)
      ·
        refine ⟨136771876291587827102265653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91181250861058551401510435 136771876291587827102265653)
        ·
          refine ⟨12822363402336358790837405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 136771876291587827102265653 12822363402336358790837405)
          ·
            refine ⟨4808386275876134546564027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12822363402336358790837405 4808386275876134546564027)
            ·
              refine ⟨7212579413814201819846041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4808386275876134546564027 7212579413814201819846041)
              ·
                refine ⟨5409434560360651364884531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7212579413814201819846041 5409434560360651364884531)
                ·
                  refine ⟨8114151840540977047326797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5409434560360651364884531 8114151840540977047326797)
                  ·
                    refine ⟨3042806940202866392747549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8114151840540977047326797 3042806940202866392747549)
                    ·
                      refine ⟨1141052602576074897280331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3042806940202866392747549 1141052602576074897280331)
                      ·
                        rfl

theorem cell23_2222192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 1, 2, 1, 3, 3].length) (baseStart_2222192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2222192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2222192 prefixEnd_2222192 := by exact prefixLift 2222192
  have htrace : WordTrace (prefixWord ++ tailWord_2222192) baseStart_2222192 baseEnd_2222192 := by
    simpa [prefixWord, tailWord_2222192, baseEnd_2222192] using wordTrace_append hprefix tailTrace_2222192
  have hstable : (prefixWord ++ tailWord_2222192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2222192).length < 2 ^ (prefixWord ++ tailWord_2222192).sum := by decide
  have hdescent : baseEnd_2222192 < baseStart_2222192 := by decide
  rcases family_descends (prefixWord ++ tailWord_2222192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2222215 : List Nat := [1, 1, 4, 2, 1, 1, 3, 1, 2, 3, 4]
def baseStart_2222215 : Nat := 118140960795 + 2222215 * 2 ^ 59
def prefixEnd_2222215 : Nat := 4983230072969 + 3 ^ 40 * 2222215 * 2
def baseEnd_2222215 : Nat := 1141064412631128307292725

theorem tailTrace_2222215 : CollatzResearch.WordTrace tailWord_2222215 prefixEnd_2222215 1141064412631128307292725 := by
  unfold tailWord_2222215
  simp only [CollatzResearch.WordTrace]
  refine ⟨81050839644302053951652099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54033893096201369301101399 81050839644302053951652099)
  ·
    refine ⟨121576259466453080927478149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81050839644302053951652099 121576259466453080927478149)
    ·
      refine ⟨22795548649959952673902153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 121576259466453080927478149 22795548649959952673902153)
      ·
        refine ⟨17096661487469964505426615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22795548649959952673902153 17096661487469964505426615)
        ·
          refine ⟨25644992231204946758139923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17096661487469964505426615 25644992231204946758139923)
          ·
            refine ⟨38467488346807420137209885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25644992231204946758139923 38467488346807420137209885)
            ·
              refine ⟨14425308130052782551453707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38467488346807420137209885 14425308130052782551453707)
              ·
                refine ⟨21637962195079173827180561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14425308130052782551453707 21637962195079173827180561)
                ·
                  refine ⟨16228471646309380370385421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21637962195079173827180561 16228471646309380370385421)
                  ·
                    refine ⟨6085676867366017638894533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16228471646309380370385421 6085676867366017638894533)
                    ·
                      refine ⟨1141064412631128307292725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6085676867366017638894533 1141064412631128307292725)
                      ·
                        rfl

theorem cell23_2222215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 3, 1, 2, 3, 4].length) (baseStart_2222215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2222215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2222215 prefixEnd_2222215 := by exact prefixLift 2222215
  have htrace : WordTrace (prefixWord ++ tailWord_2222215) baseStart_2222215 baseEnd_2222215 := by
    simpa [prefixWord, tailWord_2222215, baseEnd_2222215] using wordTrace_append hprefix tailTrace_2222215
  have hstable : (prefixWord ++ tailWord_2222215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2222215).length < 2 ^ (prefixWord ++ tailWord_2222215).sum := by decide
  have hdescent : baseEnd_2222215 < baseStart_2222215 := by decide
  rcases family_descends (prefixWord ++ tailWord_2222215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2222235 : List Nat := [1, 1, 1, 1, 1, 1, 2, 6, 2, 4, 3]
def baseStart_2222235 : Nat := 118140960795 + 2222235 * 2 ^ 59
def prefixEnd_2222235 : Nat := 4983230072969 + 3 ^ 40 * 2222235 * 2
def baseEnd_2222235 : Nat := 1141074682244218229042633

theorem tailTrace_2222235 : CollatzResearch.WordTrace tailWord_2222235 prefixEnd_2222235 1141074682244218229042633 := by
  unfold tailWord_2222235
  simp only [CollatzResearch.WordTrace]
  refine ⟨81051569104229597367380159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54034379402819731578253439 81051569104229597367380159)
  ·
    refine ⟨121577353656344396051070239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81051569104229597367380159 121577353656344396051070239)
    ·
      refine ⟨182366030484516594076605359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121577353656344396051070239 182366030484516594076605359)
      ·
        refine ⟨273549045726774891114908039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 182366030484516594076605359 273549045726774891114908039)
        ·
          refine ⟨410323568590162336672362059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 273549045726774891114908039 410323568590162336672362059)
          ·
            refine ⟨615485352885243505008543089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 410323568590162336672362059 615485352885243505008543089)
            ·
              refine ⟨461614014663932628756407317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 615485352885243505008543089 461614014663932628756407317)
              ·
                refine ⟨21638156937371841972956593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 461614014663932628756407317 21638156937371841972956593)
                ·
                  refine ⟨16228617703028881479717445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21638156937371841972956593 16228617703028881479717445)
                  ·
                    refine ⟨3042865819317915277447021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16228617703028881479717445 3042865819317915277447021)
                    ·
                      refine ⟨1141074682244218229042633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3042865819317915277447021 1141074682244218229042633)
                      ·
                        rfl

theorem cell23_2222235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 6, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 6, 2, 4, 3].length) (baseStart_2222235 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2222235 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2222235 prefixEnd_2222235 := by exact prefixLift 2222235
  have htrace : WordTrace (prefixWord ++ tailWord_2222235) baseStart_2222235 baseEnd_2222235 := by
    simpa [prefixWord, tailWord_2222235, baseEnd_2222235] using wordTrace_append hprefix tailTrace_2222235
  have hstable : (prefixWord ++ tailWord_2222235).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2222235).length < 2 ^ (prefixWord ++ tailWord_2222235).sum := by decide
  have hdescent : baseEnd_2222235 < baseStart_2222235 := by decide
  rcases family_descends (prefixWord ++ tailWord_2222235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2222245 : List Nat := [1, 3, 1, 2, 1, 3, 1, 2, 1, 4, 4]
def baseStart_2222245 : Nat := 118140960795 + 2222245 * 2 ^ 59
def prefixEnd_2222245 : Nat := 4983230072969 + 3 ^ 40 * 2222245 * 2
def baseEnd_2222245 : Nat := 1141079817050763189917587

theorem tailTrace_2222245 : CollatzResearch.WordTrace tailWord_2222245 prefixEnd_2222245 1141079817050763189917587 := by
  unfold tailWord_2222245
  simp only [CollatzResearch.WordTrace]
  refine ⟨81051933834193369075244189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54034622556128912716829459 81051933834193369075244189)
  ·
    refine ⟨30394475187822513403216571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 81051933834193369075244189 30394475187822513403216571)
    ·
      refine ⟨45591712781733770104824857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30394475187822513403216571 45591712781733770104824857)
      ·
        refine ⟨34193784586300327578618643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45591712781733770104824857 34193784586300327578618643)
        ·
          refine ⟨51290676879450491367927965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34193784586300327578618643 51290676879450491367927965)
          ·
            refine ⟨19234003829793934262972987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 51290676879450491367927965 19234003829793934262972987)
            ·
              refine ⟨28851005744690901394459481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19234003829793934262972987 28851005744690901394459481)
              ·
                refine ⟨21638254308518176045844611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28851005744690901394459481 21638254308518176045844611)
                ·
                  refine ⟨32457381462777264068766917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21638254308518176045844611 32457381462777264068766917)
                  ·
                    refine ⟨6085759024270737012893797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 32457381462777264068766917 6085759024270737012893797)
                    ·
                      refine ⟨1141079817050763189917587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6085759024270737012893797 1141079817050763189917587)
                      ·
                        rfl

theorem cell23_2222245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 2, 1, 4, 4].length) (baseStart_2222245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2222245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2222245 prefixEnd_2222245 := by exact prefixLift 2222245
  have htrace : WordTrace (prefixWord ++ tailWord_2222245) baseStart_2222245 baseEnd_2222245 := by
    simpa [prefixWord, tailWord_2222245, baseEnd_2222245] using wordTrace_append hprefix tailTrace_2222245
  have hstable : (prefixWord ++ tailWord_2222245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2222245).length < 2 ^ (prefixWord ++ tailWord_2222245).sum := by decide
  have hdescent : baseEnd_2222245 < baseStart_2222245 := by decide
  rcases family_descends (prefixWord ++ tailWord_2222245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2222253 : List Nat := [1, 5, 2, 1, 2, 1, 4, 1, 1, 3, 2]
def baseStart_2222253 : Nat := 118140960795 + 2222253 * 2 ^ 59
def prefixEnd_2222253 : Nat := 4983230072969 + 3 ^ 40 * 2222253 * 2
def baseEnd_2222253 : Nat := 1141083924895999158617551

theorem tailTrace_2222253 : CollatzResearch.WordTrace tailWord_2222253 prefixEnd_2222253 1141083924895999158617551 := by
  unfold tailWord_2222253
  simp only [CollatzResearch.WordTrace]
  refine ⟨81052225618164386441535413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54034817078776257627690275 81052225618164386441535413)
  ·
    refine ⟨7598646151702911228893945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 81052225618164386441535413 7598646151702911228893945)
    ·
      refine ⟨5698984613777183421670459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7598646151702911228893945 5698984613777183421670459)
      ·
        refine ⟨8548476920665775132505689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5698984613777183421670459 8548476920665775132505689)
        ·
          refine ⟨6411357690499331349379267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8548476920665775132505689 6411357690499331349379267)
          ·
            refine ⟨9617036535748997024068901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6411357690499331349379267 9617036535748997024068901)
            ·
              refine ⟨1803194350452936942012919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9617036535748997024068901 1803194350452936942012919)
              ·
                refine ⟨2704791525679405413019379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1803194350452936942012919 2704791525679405413019379)
                ·
                  refine ⟨4057187288519108119529069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2704791525679405413019379 4057187288519108119529069)
                  ·
                    refine ⟨1521445233194665544823401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4057187288519108119529069 1521445233194665544823401)
                    ·
                      refine ⟨1141083924895999158617551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1521445233194665544823401 1141083924895999158617551)
                      ·
                        rfl

theorem cell23_2222253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 4, 1, 1, 3, 2].length) (baseStart_2222253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2222253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2222253 prefixEnd_2222253 := by exact prefixLift 2222253
  have htrace : WordTrace (prefixWord ++ tailWord_2222253) baseStart_2222253 baseEnd_2222253 := by
    simpa [prefixWord, tailWord_2222253, baseEnd_2222253] using wordTrace_append hprefix tailTrace_2222253
  have hstable : (prefixWord ++ tailWord_2222253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2222253).length < 2 ^ (prefixWord ++ tailWord_2222253).sum := by decide
  have hdescent : baseEnd_2222253 < baseStart_2222253 := by decide
  rcases family_descends (prefixWord ++ tailWord_2222253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2222260 : List Nat := [2, 5, 3, 1, 1, 1, 1, 1, 4, 1, 3]
def baseStart_2222260 : Nat := 118140960795 + 2222260 * 2 ^ 59
def prefixEnd_2222260 : Nat := 4983230072969 + 3 ^ 40 * 2222260 * 2
def baseEnd_2222260 : Nat := 1141087519260580631230019

theorem tailTrace_2222260 : CollatzResearch.WordTrace tailWord_2222260 prefixEnd_2222260 1141087519260580631230019 := by
  unfold tailWord_2222260
  simp only [CollatzResearch.WordTrace]
  refine ⟨40526240464569513318520117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54034987286092684424693489 40526240464569513318520117)
  ·
    refine ⟨3799335043553391873611261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 40526240464569513318520117 3799335043553391873611261)
    ·
      refine ⟨1424750641332521952604223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3799335043553391873611261 1424750641332521952604223)
      ·
        refine ⟨2137125961998782928906335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1424750641332521952604223 2137125961998782928906335)
        ·
          refine ⟨3205688942998174393359503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2137125961998782928906335 3205688942998174393359503)
          ·
            refine ⟨4808533414497261590039255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3205688942998174393359503 4808533414497261590039255)
            ·
              refine ⟨7212800121745892385058883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4808533414497261590039255 7212800121745892385058883)
              ·
                refine ⟨10819200182618838577588325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7212800121745892385058883 10819200182618838577588325)
                ·
                  refine ⟨2028600034241032233297811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10819200182618838577588325 2028600034241032233297811)
                  ·
                    refine ⟨3042900051361548349946717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2028600034241032233297811 3042900051361548349946717)
                    ·
                      refine ⟨1141087519260580631230019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3042900051361548349946717 1141087519260580631230019)
                      ·
                        rfl

theorem cell23_2222260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 1, 1, 4, 1, 3].length) (baseStart_2222260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2222260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2222260 prefixEnd_2222260 := by exact prefixLift 2222260
  have htrace : WordTrace (prefixWord ++ tailWord_2222260) baseStart_2222260 baseEnd_2222260 := by
    simpa [prefixWord, tailWord_2222260, baseEnd_2222260] using wordTrace_append hprefix tailTrace_2222260
  have hstable : (prefixWord ++ tailWord_2222260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2222260).length < 2 ^ (prefixWord ++ tailWord_2222260).sum := by decide
  have hdescent : baseEnd_2222260 < baseStart_2222260 := by decide
  rcases family_descends (prefixWord ++ tailWord_2222260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2222266 : List Nat := [3, 1, 1, 1, 2, 2, 5, 2, 2, 2, 2]
def baseStart_2222266 : Nat := 118140960795 + 2222266 * 2 ^ 59
def prefixEnd_2222266 : Nat := 4983230072969 + 3 ^ 40 * 2222266 * 2
def baseEnd_2222266 : Nat := 1141090600144507607754991

theorem tailTrace_2222266 : CollatzResearch.WordTrace tailWord_2222266 prefixEnd_2222266 1141090600144507607754991 := by
  unfold tailWord_2222266
  simp only [CollatzResearch.WordTrace]
  refine ⟨20263174941779322415439663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54035133178078193107839101 20263174941779322415439663)
  ·
    refine ⟨30394762412668983623159495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20263174941779322415439663 30394762412668983623159495)
    ·
      refine ⟨45592143619003475434739243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30394762412668983623159495 45592143619003475434739243)
      ·
        refine ⟨68388215428505213152108865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45592143619003475434739243 68388215428505213152108865)
        ·
          refine ⟨51291161571378909864081649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 68388215428505213152108865 51291161571378909864081649)
          ·
            refine ⟨38468371178534182398061237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51291161571378909864081649 38468371178534182398061237)
            ·
              refine ⟨3606409797987579599818241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 38468371178534182398061237 3606409797987579599818241)
              ·
                refine ⟨2704807348490684699863681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3606409797987579599818241 2704807348490684699863681)
                ·
                  refine ⟨2028605511368013524897761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2704807348490684699863681 2028605511368013524897761)
                  ·
                    refine ⟨1521454133526010143673321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2028605511368013524897761 1521454133526010143673321)
                    ·
                      refine ⟨1141090600144507607754991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1521454133526010143673321 1141090600144507607754991)
                      ·
                        rfl

theorem cell23_2222266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 5, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 5, 2, 2, 2, 2].length) (baseStart_2222266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2222266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2222266 prefixEnd_2222266 := by exact prefixLift 2222266
  have htrace : WordTrace (prefixWord ++ tailWord_2222266) baseStart_2222266 baseEnd_2222266 := by
    simpa [prefixWord, tailWord_2222266, baseEnd_2222266] using wordTrace_append hprefix tailTrace_2222266
  have hstable : (prefixWord ++ tailWord_2222266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2222266).length < 2 ^ (prefixWord ++ tailWord_2222266).sum := by decide
  have hdescent : baseEnd_2222266 < baseStart_2222266 := by decide
  rcases family_descends (prefixWord ++ tailWord_2222266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2222272 : List Nat := [2, 1, 1, 2, 5, 2, 2, 1, 7]
def baseStart_2222272 : Nat := 118140960795 + 2222272 * 2 ^ 59
def prefixEnd_2222272 : Nat := 4983230072969 + 3 ^ 40 * 2222272 * 2
def baseEnd_2222272 : Nat := 126788186780937176031107

theorem tailTrace_2222272 : CollatzResearch.WordTrace tailWord_2222272 prefixEnd_2222272 126788186780937176031107 := by
  unfold tailWord_2222272
  simp only [CollatzResearch.WordTrace]
  refine ⟨40526459302547776343238535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54035279070063701790984713 40526459302547776343238535)
  ·
    refine ⟨60789688953821664514857803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40526459302547776343238535 60789688953821664514857803)
    ·
      refine ⟨91184533430732496772286705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60789688953821664514857803 91184533430732496772286705)
      ·
        refine ⟨68388400073049372579215029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 91184533430732496772286705 68388400073049372579215029)
        ·
          refine ⟨6411412506848378679301409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 68388400073049372579215029 6411412506848378679301409)
          ·
            refine ⟨4808559380136284009476057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6411412506848378679301409 4808559380136284009476057)
            ·
              refine ⟨3606419535102213007107043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4808559380136284009476057 3606419535102213007107043)
              ·
                refine ⟨5409629302653319510660565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3606419535102213007107043 5409629302653319510660565)
                ·
                  refine ⟨126788186780937176031107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5409629302653319510660565 126788186780937176031107)
                  ·
                    rfl

theorem cell23_2222272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 2, 1, 7].length) (baseStart_2222272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2222272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2222272 prefixEnd_2222272 := by exact prefixLift 2222272
  have htrace : WordTrace (prefixWord ++ tailWord_2222272) baseStart_2222272 baseEnd_2222272 := by
    simpa [prefixWord, tailWord_2222272, baseEnd_2222272] using wordTrace_append hprefix tailTrace_2222272
  have hstable : (prefixWord ++ tailWord_2222272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2222272).length < 2 ^ (prefixWord ++ tailWord_2222272).sum := by decide
  have hdescent : baseEnd_2222272 < baseStart_2222272 := by decide
  rcases family_descends (prefixWord ++ tailWord_2222272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2222282 : List Nat := [3, 1, 2, 1, 3, 1, 1, 3, 2, 3, 3]
def baseStart_2222282 : Nat := 118140960795 + 2222282 * 2 ^ 59
def prefixEnd_2222282 : Nat := 4983230072969 + 3 ^ 40 * 2222282 * 2
def baseEnd_2222282 : Nat := 1141098815834979545154917

theorem tailTrace_2222282 : CollatzResearch.WordTrace tailWord_2222282 prefixEnd_2222282 1141098815834979545154917 := by
  unfold tailWord_2222282
  simp only [CollatzResearch.WordTrace]
  refine ⟨20263320833764831098585275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54035522223372882929560733 20263320833764831098585275)
  ·
    refine ⟨30394981250647246647877913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20263320833764831098585275 30394981250647246647877913)
    ·
      refine ⟨22796235937985434985908435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30394981250647246647877913 22796235937985434985908435)
      ·
        refine ⟨34194353906978152478862653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22796235937985434985908435 34194353906978152478862653)
        ·
          refine ⟨12822882715116807179573495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34194353906978152478862653 12822882715116807179573495)
          ·
            refine ⟨19234324072675210769360243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12822882715116807179573495 19234324072675210769360243)
            ·
              refine ⟨28851486109012816154040365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19234324072675210769360243 28851486109012816154040365)
              ·
                refine ⟨10819307290879806057765137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28851486109012816154040365 10819307290879806057765137)
                ·
                  refine ⟨8114480468159854543323853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10819307290879806057765137 8114480468159854543323853)
                  ·
                    refine ⟨3042930175559945453746445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8114480468159854543323853 3042930175559945453746445)
                    ·
                      refine ⟨1141098815834979545154917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3042930175559945453746445 1141098815834979545154917)
                      ·
                        rfl

theorem cell23_2222282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 3, 2, 3, 3].length) (baseStart_2222282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2222282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2222282 prefixEnd_2222282 := by exact prefixLift 2222282
  have htrace : WordTrace (prefixWord ++ tailWord_2222282) baseStart_2222282 baseEnd_2222282 := by
    simpa [prefixWord, tailWord_2222282, baseEnd_2222282] using wordTrace_append hprefix tailTrace_2222282
  have hstable : (prefixWord ++ tailWord_2222282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2222282).length < 2 ^ (prefixWord ++ tailWord_2222282).sum := by decide
  have hdescent : baseEnd_2222282 < baseStart_2222282 := by decide
  rcases family_descends (prefixWord ++ tailWord_2222282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2222295 : List Nat := [1, 1, 3, 2, 1, 2, 1, 2, 3, 2, 5]
def baseStart_2222295 : Nat := 118140960795 + 2222295 * 2 ^ 59
def prefixEnd_2222295 : Nat := 4983230072969 + 3 ^ 40 * 2222295 * 2
def baseEnd_2222295 : Nat := 1141105491083487994292357

theorem tailTrace_2222295 : CollatzResearch.WordTrace tailWord_2222295 prefixEnd_2222295 1141105491083487994292357 := by
  unfold tailWord_2222295
  simp only [CollatzResearch.WordTrace]
  refine ⟨81053757484012227614564339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54035838322674818409709559 81053757484012227614564339)
  ·
    refine ⟨121580636226018341421846509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81053757484012227614564339 121580636226018341421846509)
    ·
      refine ⟨45592738584756878033192441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 121580636226018341421846509 45592738584756878033192441)
      ·
        refine ⟨34194553938567658524894331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45592738584756878033192441 34194553938567658524894331)
        ·
          refine ⟨51291830907851487787341497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34194553938567658524894331 51291830907851487787341497)
          ·
            refine ⟨38468873180888615840506123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51291830907851487787341497 38468873180888615840506123)
            ·
              refine ⟨57703309771332923760759185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38468873180888615840506123 57703309771332923760759185)
              ·
                refine ⟨43277482328499692820569389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 57703309771332923760759185 43277482328499692820569389)
                ·
                  refine ⟨16229055873187384807713521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 43277482328499692820569389 16229055873187384807713521)
                  ·
                    refine ⟨12171791904890538605785141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16229055873187384807713521 12171791904890538605785141)
                    ·
                      refine ⟨1141105491083487994292357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12171791904890538605785141 1141105491083487994292357)
                      ·
                        rfl

theorem cell23_2222295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 2, 3, 2, 5].length) (baseStart_2222295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2222295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2222295 prefixEnd_2222295 := by exact prefixLift 2222295
  have htrace : WordTrace (prefixWord ++ tailWord_2222295) baseStart_2222295 baseEnd_2222295 := by
    simpa [prefixWord, tailWord_2222295, baseEnd_2222295] using wordTrace_append hprefix tailTrace_2222295
  have hstable : (prefixWord ++ tailWord_2222295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2222295).length < 2 ^ (prefixWord ++ tailWord_2222295).sum := by decide
  have hdescent : baseEnd_2222295 < baseStart_2222295 := by decide
  rcases family_descends (prefixWord ++ tailWord_2222295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2222359 : List Nat := [1, 1, 3, 4, 1, 2, 1, 3, 2, 2, 3]
def baseStart_2222359 : Nat := 118140960795 + 2222359 * 2 ^ 59
def prefixEnd_2222359 : Nat := 4983230072969 + 3 ^ 40 * 2222359 * 2
def baseEnd_2222359 : Nat := 1141138353845375743892063

theorem tailTrace_2222359 : CollatzResearch.WordTrace tailWord_2222359 prefixEnd_2222359 1141138353845375743892063 := by
  unfold tailWord_2222359
  simp only [CollatzResearch.WordTrace]
  refine ⟨81056091755780366544894131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54037394503853577696596087 81056091755780366544894131)
  ·
    refine ⟨121584137633670549817341197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81056091755780366544894131 121584137633670549817341197)
    ·
      refine ⟨45594051612626456181502949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 121584137633670549817341197 45594051612626456181502949)
      ·
        refine ⟨8548884677367460534031803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 45594051612626456181502949 8548884677367460534031803)
        ·
          refine ⟨12823327016051190801047705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8548884677367460534031803 12823327016051190801047705)
          ·
            refine ⟨9617495262038393100785779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12823327016051190801047705 9617495262038393100785779)
            ·
              refine ⟨14426242893057589651178669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9617495262038393100785779 14426242893057589651178669)
              ·
                refine ⟨5409841084896596119192001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14426242893057589651178669 5409841084896596119192001)
                ·
                  refine ⟨4057380813672447089394001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5409841084896596119192001 4057380813672447089394001)
                  ·
                    refine ⟨3043035610254335317045501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4057380813672447089394001 3043035610254335317045501)
                    ·
                      refine ⟨1141138353845375743892063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3043035610254335317045501 1141138353845375743892063)
                      ·
                        rfl

theorem cell23_2222359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 1, 3, 2, 2, 3].length) (baseStart_2222359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2222359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2222359 prefixEnd_2222359 := by exact prefixLift 2222359
  have htrace : WordTrace (prefixWord ++ tailWord_2222359) baseStart_2222359 baseEnd_2222359 := by
    simpa [prefixWord, tailWord_2222359, baseEnd_2222359] using wordTrace_append hprefix tailTrace_2222359
  have hstable : (prefixWord ++ tailWord_2222359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2222359).length < 2 ^ (prefixWord ++ tailWord_2222359).sum := by decide
  have hdescent : baseEnd_2222359 < baseStart_2222359 := by decide
  rcases family_descends (prefixWord ++ tailWord_2222359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2222392 : List Nat := [2, 1, 2, 1, 3, 1, 3, 2, 3, 5]
def baseStart_2222392 : Nat := 118140960795 + 2222392 * 2 ^ 59
def prefixEnd_2222392 : Nat := 4983230072969 + 3 ^ 40 * 2222392 * 2
def baseEnd_2222392 : Nat := 380385099568991371593137

theorem tailTrace_2222392 : CollatzResearch.WordTrace tailWord_2222392 prefixEnd_2222392 380385099568991371593137 := by
  unfold tailWord_2222392
  simp only [CollatzResearch.WordTrace]
  refine ⟨40528647682330406590422715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54038196909773875453896953 40528647682330406590422715)
  ·
    refine ⟨60792971523495609885634073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40528647682330406590422715 60792971523495609885634073)
    ·
      refine ⟨45594728642621707414225555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60792971523495609885634073 45594728642621707414225555)
      ·
        refine ⟨68392092963932561121338333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45594728642621707414225555 68392092963932561121338333)
        ·
          refine ⟨25647034861474710420501875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 68392092963932561121338333 25647034861474710420501875)
          ·
            refine ⟨38470552292212065630752813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25647034861474710420501875 38470552292212065630752813)
            ·
              refine ⟨14426457109579524611532305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38470552292212065630752813 14426457109579524611532305)
              ·
                refine ⟨10819842832184643458649229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14426457109579524611532305 10819842832184643458649229)
                ·
                  refine ⟨4057441062069241296993461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10819842832184643458649229 4057441062069241296993461)
                  ·
                    refine ⟨380385099568991371593137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4057441062069241296993461 380385099568991371593137)
                    ·
                      rfl

theorem cell23_2222392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 3, 2, 3, 5].length) (baseStart_2222392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2222392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2222392 prefixEnd_2222392 := by exact prefixLift 2222392
  have htrace : WordTrace (prefixWord ++ tailWord_2222392) baseStart_2222392 baseEnd_2222392 := by
    simpa [prefixWord, tailWord_2222392, baseEnd_2222392] using wordTrace_append hprefix tailTrace_2222392
  have hstable : (prefixWord ++ tailWord_2222392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2222392).length < 2 ^ (prefixWord ++ tailWord_2222392).sum := by decide
  have hdescent : baseEnd_2222392 < baseStart_2222392 := by decide
  rcases family_descends (prefixWord ++ tailWord_2222392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2222399 : List Nat := [1, 1, 2, 2, 4, 1, 2, 2, 1, 5, 2]
def baseStart_2222399 : Nat := 118140960795 + 2222399 * 2 ^ 59
def prefixEnd_2222399 : Nat := 4983230072969 + 3 ^ 40 * 2222399 * 2
def baseEnd_2222399 : Nat := 1141158893071555587391879

theorem tailTrace_2222399 : CollatzResearch.WordTrace tailWord_2222399 prefixEnd_2222399 1141158893071555587391879 := by
  unfold tailWord_2222399
  simp only [CollatzResearch.WordTrace]
  refine ⟨81057550675635453376350251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54038367117090302250900167 81057550675635453376350251)
  ·
    refine ⟨121586326013453180064525377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81057550675635453376350251 121586326013453180064525377)
    ·
      refine ⟨91189744510089885048394033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 121586326013453180064525377 91189744510089885048394033)
      ·
        refine ⟨68392308382567413786295525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 91189744510089885048394033 68392308382567413786295525)
        ·
          refine ⟨12823557821731390084930411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 68392308382567413786295525 12823557821731390084930411)
          ·
            refine ⟨19235336732597085127395617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12823557821731390084930411 19235336732597085127395617)
            ·
              refine ⟨14426502549447813845546713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19235336732597085127395617 14426502549447813845546713)
              ·
                refine ⟨10819876912085860384160035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14426502549447813845546713 10819876912085860384160035)
                ·
                  refine ⟨16229815368128790576240053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10819876912085860384160035 16229815368128790576240053)
                  ·
                    refine ⟨1521545190762074116522505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 16229815368128790576240053 1521545190762074116522505)
                    ·
                      refine ⟨1141158893071555587391879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1521545190762074116522505 1141158893071555587391879)
                      ·
                        rfl

theorem cell23_2222399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 2, 2, 1, 5, 2].length) (baseStart_2222399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2222399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2222399 prefixEnd_2222399 := by exact prefixLift 2222399
  have htrace : WordTrace (prefixWord ++ tailWord_2222399) baseStart_2222399 baseEnd_2222399 := by
    simpa [prefixWord, tailWord_2222399, baseEnd_2222399] using wordTrace_append hprefix tailTrace_2222399
  have hstable : (prefixWord ++ tailWord_2222399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2222399).length < 2 ^ (prefixWord ++ tailWord_2222399).sum := by decide
  have hdescent : baseEnd_2222399 < baseStart_2222399 := by decide
  rcases family_descends (prefixWord ++ tailWord_2222399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2222416 : List Nat := [2, 1, 1, 1, 1, 6, 3, 1, 2, 3, 2]
def baseStart_2222416 : Nat := 118140960795 + 2222416 * 2 ^ 59
def prefixEnd_2222416 : Nat := 4983230072969 + 3 ^ 40 * 2222416 * 2
def baseEnd_2222416 : Nat := 1141167622242682020879301

theorem tailTrace_2222416 : CollatzResearch.WordTrace tailWord_2222416 prefixEnd_2222416 1141167622242682020879301 := by
  unfold tailWord_2222416
  simp only [CollatzResearch.WordTrace]
  refine ⟨40529085358286932639859551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54038780477715910186479401 40529085358286932639859551)
  ·
    refine ⟨60793628037430398959789327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40529085358286932639859551 60793628037430398959789327)
    ·
      refine ⟨91190442056145598439683991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60793628037430398959789327 91190442056145598439683991)
      ·
        refine ⟨136785663084218397659525987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91190442056145598439683991 136785663084218397659525987)
        ·
          refine ⟨205178494626327596489288981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 136785663084218397659525987 205178494626327596489288981)
          ·
            refine ⟨9617741935609106085435421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 205178494626327596489288981 9617741935609106085435421)
            ·
              refine ⟨3606653225853414782038283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9617741935609106085435421 3606653225853414782038283)
              ·
                refine ⟨5409979838780122173057425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3606653225853414782038283 5409979838780122173057425)
                ·
                  refine ⟨4057484879085091629793069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5409979838780122173057425 4057484879085091629793069)
                  ·
                    refine ⟨1521556829656909361172401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4057484879085091629793069 1521556829656909361172401)
                    ·
                      refine ⟨1141167622242682020879301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1521556829656909361172401 1141167622242682020879301)
                      ·
                        rfl

theorem cell23_2222416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 3, 1, 2, 3, 2].length) (baseStart_2222416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2222416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2222416 prefixEnd_2222416 := by exact prefixLift 2222416
  have htrace : WordTrace (prefixWord ++ tailWord_2222416) baseStart_2222416 baseEnd_2222416 := by
    simpa [prefixWord, tailWord_2222416, baseEnd_2222416] using wordTrace_append hprefix tailTrace_2222416
  have hstable : (prefixWord ++ tailWord_2222416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2222416).length < 2 ^ (prefixWord ++ tailWord_2222416).sum := by decide
  have hdescent : baseEnd_2222416 < baseStart_2222416 := by decide
  rcases family_descends (prefixWord ++ tailWord_2222416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2222423 : List Nat := [1, 1, 3, 2, 3, 1, 4, 3, 1, 1, 3]
def baseStart_2222423 : Nat := 118140960795 + 2222423 * 2 ^ 59
def prefixEnd_2222423 : Nat := 4983230072969 + 3 ^ 40 * 2222423 * 2
def baseEnd_2222423 : Nat := 1141171216607263493491769

theorem tailTrace_2222423 : CollatzResearch.WordTrace tailWord_2222423 prefixEnd_2222423 1141171216607263493491769 := by
  unfold tailWord_2222423
  simp only [CollatzResearch.WordTrace]
  refine ⟨81058426027548505475223923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54038950685032336983482615 81058426027548505475223923)
  ·
    refine ⟨121587639041322758212835885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81058426027548505475223923 121587639041322758212835885)
    ·
      refine ⟨45595364640496034329813457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 121587639041322758212835885 45595364640496034329813457)
      ·
        refine ⟨34196523480372025747360093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45595364640496034329813457 34196523480372025747360093)
        ·
          refine ⟨12823696305139509655260035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34196523480372025747360093 12823696305139509655260035)
          ·
            refine ⟨19235544457709264482890053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12823696305139509655260035 19235544457709264482890053)
            ·
              refine ⟨3606664585820487090541885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19235544457709264482890053 3606664585820487090541885)
              ·
                refine ⟨1352499219682682658953207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3606664585820487090541885 1352499219682682658953207)
                ·
                  refine ⟨2028748829524023988429811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1352499219682682658953207 2028748829524023988429811)
                  ·
                    refine ⟨3043123244286035982644717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2028748829524023988429811 3043123244286035982644717)
                    ·
                      refine ⟨1141171216607263493491769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3043123244286035982644717 1141171216607263493491769)
                      ·
                        rfl

theorem cell23_2222423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 4, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 4, 3, 1, 1, 3].length) (baseStart_2222423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2222423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2222423 prefixEnd_2222423 := by exact prefixLift 2222423
  have htrace : WordTrace (prefixWord ++ tailWord_2222423) baseStart_2222423 baseEnd_2222423 := by
    simpa [prefixWord, tailWord_2222423, baseEnd_2222423] using wordTrace_append hprefix tailTrace_2222423
  have hstable : (prefixWord ++ tailWord_2222423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2222423).length < 2 ^ (prefixWord ++ tailWord_2222423).sum := by decide
  have hdescent : baseEnd_2222423 < baseStart_2222423 := by decide
  rcases family_descends (prefixWord ++ tailWord_2222423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2222430 : List Nat := [4, 4, 2, 1, 1, 1, 1, 1, 8]
def baseStart_2222430 : Nat := 118140960795 + 2222430 * 2 ^ 59
def prefixEnd_2222430 : Nat := 4983230072969 + 3 ^ 40 * 2222430 * 2
def baseEnd_2222430 : Nat := 126797201219093885122693

theorem tailTrace_2222430 : CollatzResearch.WordTrace tailWord_2222430 prefixEnd_2222430 126797201219093885122693 := by
  unfold tailWord_2222430
  simp only [CollatzResearch.WordTrace]
  refine ⟨10132335167315393208841093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 54039120892348763780485829 10132335167315393208841093)
  ·
    refine ⟨1899812843871636226657705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10132335167315393208841093 1899812843871636226657705)
    ·
      refine ⟨1424859632903727169993279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1899812843871636226657705 1424859632903727169993279)
      ·
        refine ⟨2137289449355590754989919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1424859632903727169993279 2137289449355590754989919)
        ·
          refine ⟨3205934174033386132484879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2137289449355590754989919 3205934174033386132484879)
          ·
            refine ⟨4808901261050079198727319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3205934174033386132484879 4808901261050079198727319)
            ·
              refine ⟨7213351891575118798090979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4808901261050079198727319 7213351891575118798090979)
              ·
                refine ⟨10820027837362678197136469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7213351891575118798090979 10820027837362678197136469)
                ·
                  refine ⟨126797201219093885122693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 10820027837362678197136469 126797201219093885122693)
                  ·
                    rfl

theorem cell23_2222430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 1, 1, 8].length) (baseStart_2222430 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2222430 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2222430 prefixEnd_2222430 := by exact prefixLift 2222430
  have htrace : WordTrace (prefixWord ++ tailWord_2222430) baseStart_2222430 baseEnd_2222430 := by
    simpa [prefixWord, tailWord_2222430, baseEnd_2222430] using wordTrace_append hprefix tailTrace_2222430
  have hstable : (prefixWord ++ tailWord_2222430).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2222430).length < 2 ^ (prefixWord ++ tailWord_2222430).sum := by decide
  have hdescent : baseEnd_2222430 < baseStart_2222430 := by decide
  rcases family_descends (prefixWord ++ tailWord_2222430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2222459 : List Nat := [1, 1, 1, 1, 1, 7, 3, 1, 1, 2, 4]
def baseStart_2222459 : Nat := 118140960795 + 2222459 * 2 ^ 59
def prefixEnd_2222459 : Nat := 4983230072969 + 3 ^ 40 * 2222459 * 2
def baseEnd_2222459 : Nat := 1141189701910825352641603

theorem tailTrace_2222459 : CollatzResearch.WordTrace tailWord_2222459 prefixEnd_2222459 1141189701910825352641603 := by
  unfold tailWord_2222459
  simp only [CollatzResearch.WordTrace]
  refine ⟨81059739055418083623534431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54039826036945389082356287 81059739055418083623534431)
  ·
    refine ⟨121589608583127125435301647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81059739055418083623534431 121589608583127125435301647)
    ·
      refine ⟨182384412874690688152952471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121589608583127125435301647 182384412874690688152952471)
      ·
        refine ⟨273576619312036032229428707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 182384412874690688152952471 273576619312036032229428707)
        ·
          refine ⟨410364928968054048344143061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 273576619312036032229428707 410364928968054048344143061)
          ·
            refine ⟨9617928022688766758065853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 410364928968054048344143061 9617928022688766758065853)
            ·
              refine ⟨3606723008508287534274695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9617928022688766758065853 3606723008508287534274695)
              ·
                refine ⟨5410084512762431301412043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3606723008508287534274695 5410084512762431301412043)
                ·
                  refine ⟨8115126769143646952118065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5410084512762431301412043 8115126769143646952118065)
                  ·
                    refine ⟨6086345076857735214088549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8115126769143646952118065 6086345076857735214088549)
                    ·
                      refine ⟨1141189701910825352641603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6086345076857735214088549 1141189701910825352641603)
                      ·
                        rfl

theorem cell23_2222459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 3, 1, 1, 2, 4].length) (baseStart_2222459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2222459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2222459 prefixEnd_2222459 := by exact prefixLift 2222459
  have htrace : WordTrace (prefixWord ++ tailWord_2222459) baseStart_2222459 baseEnd_2222459 := by
    simpa [prefixWord, tailWord_2222459, baseEnd_2222459] using wordTrace_append hprefix tailTrace_2222459
  have hstable : (prefixWord ++ tailWord_2222459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2222459).length < 2 ^ (prefixWord ++ tailWord_2222459).sum := by decide
  have hdescent : baseEnd_2222459 < baseStart_2222459 := by decide
  rcases family_descends (prefixWord ++ tailWord_2222459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2222474 : List Nat := [3, 1, 2, 5, 2, 1, 1, 3, 1, 1, 3]
def baseStart_2222474 : Nat := 118140960795 + 2222474 * 2 ^ 59
def prefixEnd_2222474 : Nat := 4983230072969 + 3 ^ 40 * 2222474 * 2
def baseEnd_2222474 : Nat := 1141197404120642793954035

theorem tailTrace_2222474 : CollatzResearch.WordTrace tailWord_2222474 prefixEnd_2222474 1141197404120642793954035 := by
  unfold tailWord_2222474
  simp only [CollatzResearch.WordTrace]
  refine ⟨20265071537590935296332619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54040190766909160790220317 20265071537590935296332619)
  ·
    refine ⟨30397607306386402944498929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20265071537590935296332619 30397607306386402944498929)
    ·
      refine ⟨22798205479789802208374197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30397607306386402944498929 22798205479789802208374197)
      ·
        refine ⟨2137331763730293957035081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 22798205479789802208374197 2137331763730293957035081)
        ·
          refine ⟨1602998822797720467776311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2137331763730293957035081 1602998822797720467776311)
          ·
            refine ⟨2404498234196580701664467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1602998822797720467776311 2404498234196580701664467)
            ·
              refine ⟨3606747351294871052496701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2404498234196580701664467 3606747351294871052496701)
              ·
                refine ⟨1352530256735576644686263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3606747351294871052496701 1352530256735576644686263)
                ·
                  refine ⟨2028795385103364967029395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1352530256735576644686263 2028795385103364967029395)
                  ·
                    refine ⟨3043193077655047450544093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2028795385103364967029395 3043193077655047450544093)
                    ·
                      refine ⟨1141197404120642793954035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3043193077655047450544093 1141197404120642793954035)
                      ·
                        rfl

theorem cell23_2222474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 2, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 2, 1, 1, 3, 1, 1, 3].length) (baseStart_2222474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2222474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2222474 prefixEnd_2222474 := by exact prefixLift 2222474
  have htrace : WordTrace (prefixWord ++ tailWord_2222474) baseStart_2222474 baseEnd_2222474 := by
    simpa [prefixWord, tailWord_2222474, baseEnd_2222474] using wordTrace_append hprefix tailTrace_2222474
  have hstable : (prefixWord ++ tailWord_2222474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2222474).length < 2 ^ (prefixWord ++ tailWord_2222474).sum := by decide
  have hdescent : baseEnd_2222474 < baseStart_2222474 := by decide
  rcases family_descends (prefixWord ++ tailWord_2222474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2222496 : List Nat := [2, 1, 1, 4, 1, 3, 2, 1, 4, 1, 3]
def baseStart_2222496 : Nat := 118140960795 + 2222496 * 2 ^ 59
def prefixEnd_2222496 : Nat := 4983230072969 + 3 ^ 40 * 2222496 * 2
def baseEnd_2222496 : Nat := 1141208700695041707878933

theorem tailTrace_2222496 : CollatzResearch.WordTrace tailWord_2222496 prefixEnd_2222496 1141208700695041707878933 := by
  unfold tailWord_2222496
  simp only [CollatzResearch.WordTrace]
  refine ⟨40530544278142019471315671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54040725704189359295087561 40530544278142019471315671)
  ·
    refine ⟨60795816417213029206973507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40530544278142019471315671 60795816417213029206973507)
    ·
      refine ⟨91193724625819543810460261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60795816417213029206973507 91193724625819543810460261)
      ·
        refine ⟨17098823367341164464461299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 91193724625819543810460261 17098823367341164464461299)
        ·
          refine ⟨25648235051011746696691949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17098823367341164464461299 25648235051011746696691949)
          ·
            refine ⟨9618088144129405011259481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25648235051011746696691949 9618088144129405011259481)
            ·
              refine ⟨7213566108097053758444611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9618088144129405011259481 7213566108097053758444611)
              ·
                refine ⟨10820349162145580637666917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7213566108097053758444611 10820349162145580637666917)
                ·
                  refine ⟨2028815467902296369562547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10820349162145580637666917 2028815467902296369562547)
                  ·
                    refine ⟨3043223201853444554343821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2028815467902296369562547 3043223201853444554343821)
                    ·
                      refine ⟨1141208700695041707878933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3043223201853444554343821 1141208700695041707878933)
                      ·
                        rfl

theorem cell23_2222496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 2, 1, 4, 1, 3].length) (baseStart_2222496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2222496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2222496 prefixEnd_2222496 := by exact prefixLift 2222496
  have htrace : WordTrace (prefixWord ++ tailWord_2222496) baseStart_2222496 baseEnd_2222496 := by
    simpa [prefixWord, tailWord_2222496, baseEnd_2222496] using wordTrace_append hprefix tailTrace_2222496
  have hstable : (prefixWord ++ tailWord_2222496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2222496).length < 2 ^ (prefixWord ++ tailWord_2222496).sum := by decide
  have hdescent : baseEnd_2222496 < baseStart_2222496 := by decide
  rcases family_descends (prefixWord ++ tailWord_2222496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2222497 : List Nat := [1, 2, 3, 5, 1, 2, 1, 1, 3, 2, 2]
def baseStart_2222497 : Nat := 118140960795 + 2222497 * 2 ^ 59
def prefixEnd_2222497 : Nat := 4983230072969 + 3 ^ 40 * 2222497 * 2
def baseEnd_2222497 : Nat := 1141209214175696203966429

theorem tailTrace_2222497 : CollatzResearch.WordTrace tailWord_2222497 prefixEnd_2222497 1141209214175696203966429 := by
  unfold tailWord_2222497
  simp only [CollatzResearch.WordTrace]
  refine ⟨81061125029280416113417745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54040750019520277408945163 81061125029280416113417745)
  ·
    refine ⟨60795843771960312085063309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81061125029280416113417745 60795843771960312085063309)
    ·
      refine ⟨22798441414485117031898741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 60795843771960312085063309 22798441414485117031898741)
      ·
        refine ⟨2137353882607979721740507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 22798441414485117031898741 2137353882607979721740507)
        ·
          refine ⟨3206030823911969582610761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2137353882607979721740507 3206030823911969582610761)
          ·
            refine ⟨2404523117933977186958071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3206030823911969582610761 2404523117933977186958071)
            ·
              refine ⟨3606784676900965780437107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2404523117933977186958071 3606784676900965780437107)
              ·
                refine ⟨5410177015351448670655661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3606784676900965780437107 5410177015351448670655661)
                ·
                  refine ⟨2028816380756793251495873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5410177015351448670655661 2028816380756793251495873)
                  ·
                    refine ⟨1521612285567594938621905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2028816380756793251495873 1521612285567594938621905)
                    ·
                      refine ⟨1141209214175696203966429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1521612285567594938621905 1141209214175696203966429)
                      ·
                        rfl

theorem cell23_2222497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 2, 1, 1, 3, 2, 2].length) (baseStart_2222497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2222497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2222497 prefixEnd_2222497 := by exact prefixLift 2222497
  have htrace : WordTrace (prefixWord ++ tailWord_2222497) baseStart_2222497 baseEnd_2222497 := by
    simpa [prefixWord, tailWord_2222497, baseEnd_2222497] using wordTrace_append hprefix tailTrace_2222497
  have hstable : (prefixWord ++ tailWord_2222497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2222497).length < 2 ^ (prefixWord ++ tailWord_2222497).sum := by decide
  have hdescent : baseEnd_2222497 < baseStart_2222497 := by decide
  rcases family_descends (prefixWord ++ tailWord_2222497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2222512 : List Nat := [2, 1, 1, 1, 2, 1, 1, 2, 6, 6]
def baseStart_2222512 : Nat := 118140960795 + 2222512 * 2 ^ 59
def prefixEnd_2222512 : Nat := 4983230072969 + 3 ^ 40 * 2222512 * 2
def baseEnd_2222512 : Nat := 380405638795171215092953

theorem tailTrace_2222512 : CollatzResearch.WordTrace tailWord_2222512 prefixEnd_2222512 380405638795171215092953 := by
  unfold tailWord_2222512
  simp only [CollatzResearch.WordTrace]
  refine ⟨40530836062113036837606895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54041114749484049116809193 40530836062113036837606895)
  ·
    refine ⟨60796254093169555256410343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40530836062113036837606895 60796254093169555256410343)
    ·
      refine ⟨91194381139754332884615515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60796254093169555256410343 91194381139754332884615515)
      ·
        refine ⟨136791571709631499326923273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91194381139754332884615515 136791571709631499326923273)
        ·
          refine ⟨102593678782223624495192455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 136791571709631499326923273 102593678782223624495192455)
          ·
            refine ⟨153890518173335436742788683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 102593678782223624495192455 153890518173335436742788683)
            ·
              refine ⟨230835777260003155114183025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 153890518173335436742788683 230835777260003155114183025)
              ·
                refine ⟨173126832945002366335637269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 230835777260003155114183025 173126832945002366335637269)
                ·
                  refine ⟨8115320294296985921982997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 173126832945002366335637269 8115320294296985921982997)
                  ·
                    refine ⟨380405638795171215092953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8115320294296985921982997 380405638795171215092953)
                    ·
                      rfl

theorem cell23_2222512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 2, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 2, 6, 6].length) (baseStart_2222512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2222512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2222512 prefixEnd_2222512 := by exact prefixLift 2222512
  have htrace : WordTrace (prefixWord ++ tailWord_2222512) baseStart_2222512 baseEnd_2222512 := by
    simpa [prefixWord, tailWord_2222512, baseEnd_2222512] using wordTrace_append hprefix tailTrace_2222512
  have hstable : (prefixWord ++ tailWord_2222512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2222512).length < 2 ^ (prefixWord ++ tailWord_2222512).sum := by decide
  have hdescent : baseEnd_2222512 < baseStart_2222512 := by decide
  rcases family_descends (prefixWord ++ tailWord_2222512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2222513 : List Nat := [1, 2, 2, 4, 1, 3, 1, 3, 2, 1, 3]
def baseStart_2222513 : Nat := 118140960795 + 2222513 * 2 ^ 59
def prefixEnd_2222513 : Nat := 4983230072969 + 3 ^ 40 * 2222513 * 2
def baseEnd_2222513 : Nat := 1141217429866168141366355

theorem tailTrace_2222513 : CollatzResearch.WordTrace tailWord_2222513 prefixEnd_2222513 1141217429866168141366355 := by
  unfold tailWord_2222513
  simp only [CollatzResearch.WordTrace]
  refine ⟨81061708597222450846000193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54041139064814967230666795 81061708597222450846000193)
  ·
    refine ⟨60796281447916838134500145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81061708597222450846000193 60796281447916838134500145)
    ·
      refine ⟨45597211085937628600875109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60796281447916838134500145 45597211085937628600875109)
      ·
        refine ⟨8549477078613305362664083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 45597211085937628600875109 8549477078613305362664083)
        ·
          refine ⟨12824215617919958043996125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8549477078613305362664083 12824215617919958043996125)
          ·
            refine ⟨4809080856719984266498547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12824215617919958043996125 4809080856719984266498547)
            ·
              refine ⟨7213621285079976399747821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4809080856719984266498547 7213621285079976399747821)
              ·
                refine ⟨2705107981904991149905433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7213621285079976399747821 2705107981904991149905433)
                ·
                  refine ⟨2028830986428743362429075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2705107981904991149905433 2028830986428743362429075)
                  ·
                    refine ⟨3043246479643115043643613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2028830986428743362429075 3043246479643115043643613)
                    ·
                      refine ⟨1141217429866168141366355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3043246479643115043643613 1141217429866168141366355)
                      ·
                        rfl

theorem cell23_2222513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 1, 3, 2, 1, 3].length) (baseStart_2222513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2222513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2222513 prefixEnd_2222513 := by exact prefixLift 2222513
  have htrace : WordTrace (prefixWord ++ tailWord_2222513) baseStart_2222513 baseEnd_2222513 := by
    simpa [prefixWord, tailWord_2222513, baseEnd_2222513] using wordTrace_append hprefix tailTrace_2222513
  have hstable : (prefixWord ++ tailWord_2222513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2222513).length < 2 ^ (prefixWord ++ tailWord_2222513).sum := by decide
  have hdescent : baseEnd_2222513 < baseStart_2222513 := by decide
  rcases family_descends (prefixWord ++ tailWord_2222513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2222536 : List Nat := [2, 1, 3, 1, 3, 2, 1, 1, 3, 4, 2]
def baseStart_2222536 : Nat := 118140960795 + 2222536 * 2 ^ 59
def prefixEnd_2222536 : Nat := 4983230072969 + 3 ^ 40 * 2222536 * 2
def baseEnd_2222536 : Nat := 1141229239921221551378749

theorem tailTrace_2222536 : CollatzResearch.WordTrace tailWord_2222536 prefixEnd_2222536 1141229239921221551378749 := by
  unfold tailWord_2222536
  simp only [CollatzResearch.WordTrace]
  refine ⟨40531273738069562887043731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54041698317426083849391641 40531273738069562887043731)
  ·
    refine ⟨60796910607104344330565597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40531273738069562887043731 60796910607104344330565597)
    ·
      refine ⟨22798841477664129123962099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 60796910607104344330565597 22798841477664129123962099)
      ·
        refine ⟨34198262216496193685943149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22798841477664129123962099 34198262216496193685943149)
        ·
          refine ⟨12824348331186072632228681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34198262216496193685943149 12824348331186072632228681)
          ·
            refine ⟨9618261248389554474171511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12824348331186072632228681 9618261248389554474171511)
            ·
              refine ⟨14427391872584331711257267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9618261248389554474171511 14427391872584331711257267)
              ·
                refine ⟨21641087808876497566885901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14427391872584331711257267 21641087808876497566885901)
                ·
                  refine ⟨8115407928328686587582213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21641087808876497566885901 8115407928328686587582213)
                  ·
                    refine ⟨1521638986561628735171665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8115407928328686587582213 1521638986561628735171665)
                    ·
                      refine ⟨1141229239921221551378749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1521638986561628735171665 1141229239921221551378749)
                      ·
                        rfl

theorem cell23_2222536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 1, 1, 3, 4, 2].length) (baseStart_2222536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2222536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2222536 prefixEnd_2222536 := by exact prefixLift 2222536
  have htrace : WordTrace (prefixWord ++ tailWord_2222536) baseStart_2222536 baseEnd_2222536 := by
    simpa [prefixWord, tailWord_2222536, baseEnd_2222536] using wordTrace_append hprefix tailTrace_2222536
  have hstable : (prefixWord ++ tailWord_2222536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2222536).length < 2 ^ (prefixWord ++ tailWord_2222536).sum := by decide
  have hdescent : baseEnd_2222536 < baseStart_2222536 := by decide
  rcases family_descends (prefixWord ++ tailWord_2222536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2222570 : List Nat := [3, 1, 3, 1, 3, 1, 2, 3, 2, 2, 2]
def baseStart_2222570 : Nat := 118140960795 + 2222570 * 2 ^ 59
def prefixEnd_2222570 : Nat := 4983230072969 + 3 ^ 40 * 2222570 * 2
def baseEnd_2222570 : Nat := 1141246698263474418353593

theorem tailTrace_2222570 : CollatzResearch.WordTrace tailWord_2222570 prefixEnd_2222570 1141246698263474418353593 := by
  unfold tailWord_2222570
  simp only [CollatzResearch.WordTrace]
  refine ⟨20265946889503987395206291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54042525038677299720550109 20265946889503987395206291)
  ·
    refine ⟨30398920334255981092809437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20265946889503987395206291 30398920334255981092809437)
    ·
      refine ⟨11399595125345992909803539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30398920334255981092809437 11399595125345992909803539)
      ·
        refine ⟨17099392688018989364705309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11399595125345992909803539 17099392688018989364705309)
        ·
          refine ⟨6412272258007121011764491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17099392688018989364705309 6412272258007121011764491)
          ·
            refine ⟨9618408387010681517646737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6412272258007121011764491 9618408387010681517646737)
            ·
              refine ⟨7213806290258011138235053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9618408387010681517646737 7213806290258011138235053)
              ·
                refine ⟨2705177358846754176838145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7213806290258011138235053 2705177358846754176838145)
                ·
                  refine ⟨2028883019135065632628609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2705177358846754176838145 2028883019135065632628609)
                  ·
                    refine ⟨1521662264351299224471457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2028883019135065632628609 1521662264351299224471457)
                    ·
                      refine ⟨1141246698263474418353593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1521662264351299224471457 1141246698263474418353593)
                      ·
                        rfl

theorem cell23_2222570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 2, 3, 2, 2, 2].length) (baseStart_2222570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2222570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2222570 prefixEnd_2222570 := by exact prefixLift 2222570
  have htrace : WordTrace (prefixWord ++ tailWord_2222570) baseStart_2222570 baseEnd_2222570 := by
    simpa [prefixWord, tailWord_2222570, baseEnd_2222570] using wordTrace_append hprefix tailTrace_2222570
  have hstable : (prefixWord ++ tailWord_2222570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2222570).length < 2 ^ (prefixWord ++ tailWord_2222570).sum := by decide
  have hdescent : baseEnd_2222570 < baseStart_2222570 := by decide
  rcases family_descends (prefixWord ++ tailWord_2222570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2222589 : List Nat := [1, 4, 1, 1, 1, 3, 3, 1, 1, 7]
def baseStart_2222589 : Nat := 118140960795 + 2222589 * 2 ^ 59
def prefixEnd_2222589 : Nat := 4983230072969 + 3 ^ 40 * 2222589 * 2
def baseEnd_2222589 : Nat := 380418818131969948005335

theorem tailTrace_2222589 : CollatzResearch.WordTrace tailWord_2222589 prefixEnd_2222589 380418818131969948005335 := by
  unfold tailWord_2222589
  simp only [CollatzResearch.WordTrace]
  refine ⟨81064480544947115825766821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54042987029964743883844547 81064480544947115825766821)
  ·
    refine ⟨15199590102177584217331279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 81064480544947115825766821 15199590102177584217331279)
    ·
      refine ⟨22799385153266376325996919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15199590102177584217331279 22799385153266376325996919)
      ·
        refine ⟨34199077729899564488995379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22799385153266376325996919 34199077729899564488995379)
        ·
          refine ⟨51298616594849346733493069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34199077729899564488995379 51298616594849346733493069)
          ·
            refine ⟨19236981223068505025059901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 51298616594849346733493069 19236981223068505025059901)
            ·
              refine ⟨7213867958650689384397463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19236981223068505025059901 7213867958650689384397463)
              ·
                refine ⟨10820801937976034076596195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7213867958650689384397463 10820801937976034076596195)
                ·
                  refine ⟨16231202906964051114894293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10820801937976034076596195 16231202906964051114894293)
                  ·
                    refine ⟨380418818131969948005335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 16231202906964051114894293 380418818131969948005335)
                    ·
                      rfl

theorem cell23_2222589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 3, 1, 1, 7].length) (baseStart_2222589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2222589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2222589 prefixEnd_2222589 := by exact prefixLift 2222589
  have htrace : WordTrace (prefixWord ++ tailWord_2222589) baseStart_2222589 baseEnd_2222589 := by
    simpa [prefixWord, tailWord_2222589, baseEnd_2222589] using wordTrace_append hprefix tailTrace_2222589
  have hstable : (prefixWord ++ tailWord_2222589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2222589).length < 2 ^ (prefixWord ++ tailWord_2222589).sum := by decide
  have hdescent : baseEnd_2222589 < baseStart_2222589 := by decide
  rcases family_descends (prefixWord ++ tailWord_2222589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2222593 : List Nat := [1, 2, 4, 1, 3, 2, 2, 3, 5]
def baseStart_2222593 : Nat := 118140960795 + 2222593 * 2 ^ 59
def prefixEnd_2222593 : Nat := 4983230072969 + 3 ^ 40 * 2222593 * 2
def baseEnd_2222593 : Nat := 126806500924280869818443

theorem tailTrace_2222593 : CollatzResearch.WordTrace tailWord_2222593 prefixEnd_2222593 126806500924280869818443 := by
  unfold tailWord_2222593
  simp only [CollatzResearch.WordTrace]
  refine ⟨81064626436932624508912433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54043084291288416339274955 81064626436932624508912433)
  ·
    refine ⟨60798469827699468381684325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81064626436932624508912433 60798469827699468381684325)
    ·
      refine ⟨11399713092693650321565811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 60798469827699468381684325 11399713092693650321565811)
      ·
        refine ⟨17099569639040475482348717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11399713092693650321565811 17099569639040475482348717)
        ·
          refine ⟨6412338614640178305880769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17099569639040475482348717 6412338614640178305880769)
          ·
            refine ⟨4809253960980133729410577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6412338614640178305880769 4809253960980133729410577)
            ·
              refine ⟨3606940470735100297057933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4809253960980133729410577 3606940470735100297057933)
              ·
                refine ⟨1352602676525662611396725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3606940470735100297057933 1352602676525662611396725)
                ·
                  refine ⟨126806500924280869818443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1352602676525662611396725 126806500924280869818443)
                  ·
                    rfl

theorem cell23_2222593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 2, 3, 5].length) (baseStart_2222593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2222593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2222593 prefixEnd_2222593 := by exact prefixLift 2222593
  have htrace : WordTrace (prefixWord ++ tailWord_2222593) baseStart_2222593 baseEnd_2222593 := by
    simpa [prefixWord, tailWord_2222593, baseEnd_2222593] using wordTrace_append hprefix tailTrace_2222593
  have hstable : (prefixWord ++ tailWord_2222593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2222593).length < 2 ^ (prefixWord ++ tailWord_2222593).sum := by decide
  have hdescent : baseEnd_2222593 < baseStart_2222593 := by decide
  rcases family_descends (prefixWord ++ tailWord_2222593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2222644 : List Nat := [2, 5, 1, 3, 2, 1, 1, 3, 5]
def baseStart_2222644 : Nat := 118140960795 + 2222644 * 2 ^ 59
def prefixEnd_2222644 : Nat := 4983230072969 + 3 ^ 40 * 2222644 * 2
def baseEnd_2222644 : Nat := 126809410647989680980917

theorem tailTrace_2222644 : CollatzResearch.WordTrace tailWord_2222644 prefixEnd_2222644 126809410647989680980917 := by
  unfold tailWord_2222644
  simp only [CollatzResearch.WordTrace]
  refine ⟨40533243279873930109509493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54044324373165240146012657 40533243279873930109509493)
  ·
    refine ⟨3799991557488180947766515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 40533243279873930109509493 3799991557488180947766515)
    ·
      refine ⟨5699987336232271421649773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3799991557488180947766515 5699987336232271421649773)
      ·
        refine ⟨2137495251087101783118665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5699987336232271421649773 2137495251087101783118665)
        ·
          refine ⟨1603121438315326337338999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2137495251087101783118665 1603121438315326337338999)
          ·
            refine ⟨2404682157472989506008499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1603121438315326337338999 2404682157472989506008499)
            ·
              refine ⟨3607023236209484259012749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2404682157472989506008499 3607023236209484259012749)
              ·
                refine ⟨1352633713578556597129781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3607023236209484259012749 1352633713578556597129781)
                ·
                  refine ⟨126809410647989680980917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1352633713578556597129781 126809410647989680980917)
                  ·
                    rfl

theorem cell23_2222644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 2, 1, 1, 3, 5].length) (baseStart_2222644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2222644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2222644 prefixEnd_2222644 := by exact prefixLift 2222644
  have htrace : WordTrace (prefixWord ++ tailWord_2222644) baseStart_2222644 baseEnd_2222644 := by
    simpa [prefixWord, tailWord_2222644, baseEnd_2222644] using wordTrace_append hprefix tailTrace_2222644
  have hstable : (prefixWord ++ tailWord_2222644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2222644).length < 2 ^ (prefixWord ++ tailWord_2222644).sum := by decide
  have hdescent : baseEnd_2222644 < baseStart_2222644 := by decide
  rcases family_descends (prefixWord ++ tailWord_2222644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2222649 : List Nat := [1, 2, 1, 5, 1, 1, 1, 1, 10]
def baseStart_2222649 : Nat := 118140960795 + 2222649 * 2 ^ 59
def prefixEnd_2222649 : Nat := 4983230072969 + 3 ^ 40 * 2222649 * 2
def baseEnd_2222649 : Nat := 126809695915019956585081

theorem tailTrace_2222649 : CollatzResearch.WordTrace tailWord_2222649 prefixEnd_2222649 126809695915019956585081 := by
  unfold tailWord_2222649
  simp only [CollatzResearch.WordTrace]
  refine ⟨81066668924729746072951001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54044445949819830715300667 81066668924729746072951001)
  ·
    refine ⟨60800001693547309554713251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81066668924729746072951001 60800001693547309554713251)
    ·
      refine ⟨91200002540320964332069877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60800001693547309554713251 91200002540320964332069877)
      ·
        refine ⟨8550000238155090406131551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 91200002540320964332069877 8550000238155090406131551)
        ·
          refine ⟨12825000357232635609197327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8550000238155090406131551 12825000357232635609197327)
          ·
            refine ⟨19237500535848953413795991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12825000357232635609197327 19237500535848953413795991)
            ·
              refine ⟨28856250803773430120693987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19237500535848953413795991 28856250803773430120693987)
              ·
                refine ⟨43284376205660145181040981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28856250803773430120693987 43284376205660145181040981)
                ·
                  refine ⟨126809695915019956585081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 43284376205660145181040981 126809695915019956585081)
                  ·
                    rfl

theorem cell23_2222649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 1, 10].length) (baseStart_2222649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2222649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2222649 prefixEnd_2222649 := by exact prefixLift 2222649
  have htrace : WordTrace (prefixWord ++ tailWord_2222649) baseStart_2222649 baseEnd_2222649 := by
    simpa [prefixWord, tailWord_2222649, baseEnd_2222649] using wordTrace_append hprefix tailTrace_2222649
  have hstable : (prefixWord ++ tailWord_2222649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2222649).length < 2 ^ (prefixWord ++ tailWord_2222649).sum := by decide
  have hdescent : baseEnd_2222649 < baseStart_2222649 := by decide
  rcases family_descends (prefixWord ++ tailWord_2222649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2222663 : List Nat := [1, 1, 4, 1, 4, 2, 1, 2, 2, 2, 3]
def baseStart_2222663 : Nat := 118140960795 + 2222663 * 2 ^ 59
def prefixEnd_2222663 : Nat := 4983230072969 + 3 ^ 40 * 2222663 * 2
def baseEnd_2222663 : Nat := 1141294451964342554490665

theorem tailTrace_2222663 : CollatzResearch.WordTrace tailWord_2222663 prefixEnd_2222663 1141294451964342554490665 := by
  unfold tailWord_2222663
  simp only [CollatzResearch.WordTrace]
  refine ⟨81067179546679026463960643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54044786364452684309307095 81067179546679026463960643)
  ·
    refine ⟨121600769320018539695940965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81067179546679026463960643 121600769320018539695940965)
    ·
      refine ⟨22800144247503476192988931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 121600769320018539695940965 22800144247503476192988931)
      ·
        refine ⟨34200216371255214289483397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22800144247503476192988931 34200216371255214289483397)
        ·
          refine ⟨6412540569610352679278137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 34200216371255214289483397 6412540569610352679278137)
          ·
            refine ⟨4809405427207764509458603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6412540569610352679278137 4809405427207764509458603)
            ·
              refine ⟨7214108140811646764187905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4809405427207764509458603 7214108140811646764187905)
              ·
                refine ⟨5410581105608735073140929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7214108140811646764187905 5410581105608735073140929)
                ·
                  refine ⟨4057935829206551304855697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5410581105608735073140929 4057935829206551304855697)
                  ·
                    refine ⟨3043451871904913478641773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4057935829206551304855697 3043451871904913478641773)
                    ·
                      refine ⟨1141294451964342554490665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3043451871904913478641773 1141294451964342554490665)
                      ·
                        rfl

theorem cell23_2222663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 1, 2, 2, 2, 3].length) (baseStart_2222663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2222663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2222663 prefixEnd_2222663 := by exact prefixLift 2222663
  have htrace : WordTrace (prefixWord ++ tailWord_2222663) baseStart_2222663 baseEnd_2222663 := by
    simpa [prefixWord, tailWord_2222663, baseEnd_2222663] using wordTrace_append hprefix tailTrace_2222663
  have hstable : (prefixWord ++ tailWord_2222663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2222663).length < 2 ^ (prefixWord ++ tailWord_2222663).sum := by decide
  have hdescent : baseEnd_2222663 < baseStart_2222663 := by decide
  rcases family_descends (prefixWord ++ tailWord_2222663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2222703 : List Nat := [1, 1, 2, 1, 3, 2, 3, 3, 2, 3, 2]
def baseStart_2222703 : Nat := 118140960795 + 2222703 * 2 ^ 59
def prefixEnd_2222703 : Nat := 4983230072969 + 3 ^ 40 * 2222703 * 2
def baseEnd_2222703 : Nat := 1141314991190522397990481

theorem tailTrace_2222703 : CollatzResearch.WordTrace tailWord_2222703 prefixEnd_2222703 1141314991190522397990481 := by
  unfold tailWord_2222703
  simp only [CollatzResearch.WordTrace]
  refine ⟨81068638466534113295416763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54045758977689408863611175 81068638466534113295416763)
  ·
    refine ⟨121602957699801169943125145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81068638466534113295416763 121602957699801169943125145)
    ·
      refine ⟨91202218274850877457343859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 121602957699801169943125145 91202218274850877457343859)
      ·
        refine ⟨136803327412276316186015789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91202218274850877457343859 136803327412276316186015789)
        ·
          refine ⟨51301247779603618569755921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 136803327412276316186015789 51301247779603618569755921)
          ·
            refine ⟨38475935834702713927316941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51301247779603618569755921 38475935834702713927316941)
            ·
              refine ⟨14428475938013517722743853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38475935834702713927316941 14428475938013517722743853)
              ·
                refine ⟨5410678476755069146028945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14428475938013517722743853 5410678476755069146028945)
                ·
                  refine ⟨4058008857566301859521709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5410678476755069146028945 4058008857566301859521709)
                  ·
                    refine ⟨1521753321587363197320641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4058008857566301859521709 1521753321587363197320641)
                    ·
                      refine ⟨1141314991190522397990481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1521753321587363197320641 1141314991190522397990481)
                      ·
                        rfl

theorem cell23_2222703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 3, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 3, 3, 2, 3, 2].length) (baseStart_2222703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2222703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2222703 prefixEnd_2222703 := by exact prefixLift 2222703
  have htrace : WordTrace (prefixWord ++ tailWord_2222703) baseStart_2222703 baseEnd_2222703 := by
    simpa [prefixWord, tailWord_2222703, baseEnd_2222703] using wordTrace_append hprefix tailTrace_2222703
  have hstable : (prefixWord ++ tailWord_2222703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2222703).length < 2 ^ (prefixWord ++ tailWord_2222703).sum := by decide
  have hdescent : baseEnd_2222703 < baseStart_2222703 := by decide
  rcases family_descends (prefixWord ++ tailWord_2222703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2222743 : List Nat := [1, 1, 3, 3, 2, 1, 1, 5, 2, 4]
def baseStart_2222743 : Nat := 118140960795 + 2222743 * 2 ^ 59
def prefixEnd_2222743 : Nat := 4983230072969 + 3 ^ 40 * 2222743 * 2
def baseEnd_2222743 : Nat := 380445176805567413830099

theorem tailTrace_2222743 : CollatzResearch.WordTrace tailWord_2222743 prefixEnd_2222743 380445176805567413830099 := by
  unfold tailWord_2222743
  simp only [CollatzResearch.WordTrace]
  refine ⟨81070097386389200126872883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54046731590926133417915255 81070097386389200126872883)
  ·
    refine ⟨121605146079583800190309325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81070097386389200126872883 121605146079583800190309325)
    ·
      refine ⟨45601929779843925071365997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 121605146079583800190309325 45601929779843925071365997)
      ·
        refine ⟨17100723667441471901762249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45601929779843925071365997 17100723667441471901762249)
        ·
          refine ⟨12825542750581103926321687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17100723667441471901762249 12825542750581103926321687)
          ·
            refine ⟨19238314125871655889482531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12825542750581103926321687 19238314125871655889482531)
            ·
              refine ⟨28857471188807483834223797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19238314125871655889482531 28857471188807483834223797)
              ·
                refine ⟨2705387923950701609458481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 28857471188807483834223797 2705387923950701609458481)
                ·
                  refine ⟨2029040942963026207093861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2705387923950701609458481 2029040942963026207093861)
                  ·
                    refine ⟨380445176805567413830099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2029040942963026207093861 380445176805567413830099)
                    ·
                      rfl

theorem cell23_2222743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 5, 2, 4].length) (baseStart_2222743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2222743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2222743 prefixEnd_2222743 := by exact prefixLift 2222743
  have htrace : WordTrace (prefixWord ++ tailWord_2222743) baseStart_2222743 baseEnd_2222743 := by
    simpa [prefixWord, tailWord_2222743, baseEnd_2222743] using wordTrace_append hprefix tailTrace_2222743
  have hstable : (prefixWord ++ tailWord_2222743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2222743).length < 2 ^ (prefixWord ++ tailWord_2222743).sum := by decide
  have hdescent : baseEnd_2222743 < baseStart_2222743 := by decide
  rcases family_descends (prefixWord ++ tailWord_2222743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2222750 : List Nat := [4, 3, 1, 1, 1, 1, 2, 4, 1, 1, 4]
def baseStart_2222750 : Nat := 118140960795 + 2222750 * 2 ^ 59
def prefixEnd_2222750 : Nat := 4983230072969 + 3 ^ 40 * 2222750 * 2
def baseEnd_2222750 : Nat := 1141339124781283714102765

theorem tailTrace_2222750 : CollatzResearch.WordTrace tailWord_2222750 prefixEnd_2222750 1141339124781283714102765 := by
  unfold tailWord_2222750
  simp only [CollatzResearch.WordTrace]
  refine ⟨10133794087170480040297213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 54046901798242560214918469 10133794087170480040297213)
  ·
    refine ⟨3800172782688930015111455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10133794087170480040297213 3800172782688930015111455)
    ·
      refine ⟨5700259174033395022667183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3800172782688930015111455 5700259174033395022667183)
      ·
        refine ⟨8550388761050092534000775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5700259174033395022667183 8550388761050092534000775)
        ·
          refine ⟨12825583141575138801001163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8550388761050092534000775 12825583141575138801001163)
          ·
            refine ⟨19238374712362708201501745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12825583141575138801001163 19238374712362708201501745)
            ·
              refine ⟨14428781034272031151126309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19238374712362708201501745 14428781034272031151126309)
              ·
                refine ⟨2705396443926005840836183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14428781034272031151126309 2705396443926005840836183)
                ·
                  refine ⟨4058094665889008761254275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2705396443926005840836183 4058094665889008761254275)
                  ·
                    refine ⟨6087141998833513141881413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4058094665889008761254275 6087141998833513141881413)
                    ·
                      refine ⟨1141339124781283714102765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6087141998833513141881413 1141339124781283714102765)
                      ·
                        rfl

theorem cell23_2222750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 2, 4, 1, 1, 4].length) (baseStart_2222750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2222750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2222750 prefixEnd_2222750 := by exact prefixLift 2222750
  have htrace : WordTrace (prefixWord ++ tailWord_2222750) baseStart_2222750 baseEnd_2222750 := by
    simpa [prefixWord, tailWord_2222750, baseEnd_2222750] using wordTrace_append hprefix tailTrace_2222750
  have hstable : (prefixWord ++ tailWord_2222750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2222750).length < 2 ^ (prefixWord ++ tailWord_2222750).sum := by decide
  have hdescent : baseEnd_2222750 < baseStart_2222750 := by decide
  rcases family_descends (prefixWord ++ tailWord_2222750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2222767 : List Nat := [1, 1, 2, 1, 2, 5, 1, 5, 1, 2, 2]
def baseStart_2222767 : Nat := 118140960795 + 2222767 * 2 ^ 59
def prefixEnd_2222767 : Nat := 4983230072969 + 3 ^ 40 * 2222767 * 2
def baseEnd_2222767 : Nat := 1141347853952410147590187

theorem tailTrace_2222767 : CollatzResearch.WordTrace tailWord_2222767 prefixEnd_2222767 1141347853952410147590187 := by
  unfold tailWord_2222767
  simp only [CollatzResearch.WordTrace]
  refine ⟨81070972738302252225746555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54047315158868168150497703 81070972738302252225746555)
  ·
    refine ⟨121606459107453378338619833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81070972738302252225746555 121606459107453378338619833)
    ·
      refine ⟨91204844330590033753964875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 121606459107453378338619833 91204844330590033753964875)
      ·
        refine ⟨136807266495885050630947313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91204844330590033753964875 136807266495885050630947313)
        ·
          refine ⟨102605449871913787973210485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 136807266495885050630947313 102605449871913787973210485)
          ·
            refine ⟨9619260925491917622488483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 102605449871913787973210485 9619260925491917622488483)
            ·
              refine ⟨14428891388237876433732725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9619260925491917622488483 14428891388237876433732725)
              ·
                refine ⟨1352708567647300915662443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 14428891388237876433732725 1352708567647300915662443)
                ·
                  refine ⟨2029062851470951373493665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1352708567647300915662443 2029062851470951373493665)
                  ·
                    refine ⟨1521797138603213530120249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2029062851470951373493665 1521797138603213530120249)
                    ·
                      refine ⟨1141347853952410147590187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1521797138603213530120249 1141347853952410147590187)
                      ·
                        rfl

theorem cell23_2222767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 1, 5, 1, 2, 2].length) (baseStart_2222767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2222767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2222767 prefixEnd_2222767 := by exact prefixLift 2222767
  have htrace : WordTrace (prefixWord ++ tailWord_2222767) baseStart_2222767 baseEnd_2222767 := by
    simpa [prefixWord, tailWord_2222767, baseEnd_2222767] using wordTrace_append hprefix tailTrace_2222767
  have hstable : (prefixWord ++ tailWord_2222767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2222767).length < 2 ^ (prefixWord ++ tailWord_2222767).sum := by decide
  have hdescent : baseEnd_2222767 < baseStart_2222767 := by decide
  rcases family_descends (prefixWord ++ tailWord_2222767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2222840 : List Nat := [2, 1, 2, 1, 1, 2, 3, 3, 4, 2, 2]
def baseStart_2222840 : Nat := 118140960795 + 2222840 * 2 ^ 59
def prefixEnd_2222840 : Nat := 4983230072969 + 3 ^ 40 * 2222840 * 2
def baseEnd_2222840 : Nat := 1141385338040188361977351

theorem tailTrace_2222840 : CollatzResearch.WordTrace tailWord_2222840 prefixEnd_2222840 1141385338040188361977351 := by
  unfold tailWord_2222840
  simp only [CollatzResearch.WordTrace]
  refine ⟨40536817633518892846576987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54049090178025190462102649 40536817633518892846576987)
  ·
    refine ⟨60805226450278339269865481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40536817633518892846576987 60805226450278339269865481)
    ·
      refine ⟨45603919837708754452399111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60805226450278339269865481 45603919837708754452399111)
      ·
        refine ⟨68405879756563131678598667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45603919837708754452399111 68405879756563131678598667)
        ·
          refine ⟨102608819634844697517898001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68405879756563131678598667 102608819634844697517898001)
          ·
            refine ⟨76956614726133523138423501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 102608819634844697517898001 76956614726133523138423501)
            ·
              refine ⟨28858730522300071176908813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 76956614726133523138423501 28858730522300071176908813)
              ·
                refine ⟨10822023945862526691340805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28858730522300071176908813 10822023945862526691340805)
                ·
                  refine ⟨2029129489849223754626401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10822023945862526691340805 2029129489849223754626401)
                  ·
                    refine ⟨1521847117386917815969801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2029129489849223754626401 1521847117386917815969801)
                    ·
                      refine ⟨1141385338040188361977351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1521847117386917815969801 1141385338040188361977351)
                      ·
                        rfl

theorem cell23_2222840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 3, 4, 2, 2].length) (baseStart_2222840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2222840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2222840 prefixEnd_2222840 := by exact prefixLift 2222840
  have htrace : WordTrace (prefixWord ++ tailWord_2222840) baseStart_2222840 baseEnd_2222840 := by
    simpa [prefixWord, tailWord_2222840, baseEnd_2222840] using wordTrace_append hprefix tailTrace_2222840
  have hstable : (prefixWord ++ tailWord_2222840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2222840).length < 2 ^ (prefixWord ++ tailWord_2222840).sum := by decide
  have hdescent : baseEnd_2222840 < baseStart_2222840 := by decide
  rcases family_descends (prefixWord ++ tailWord_2222840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2222930 : List Nat := [3, 2, 2, 1, 1, 2, 1, 2, 1, 6, 2]
def baseStart_2222930 : Nat := 118140960795 + 2222930 * 2 ^ 59
def prefixEnd_2222930 : Nat := 4983230072969 + 3 ^ 40 * 2222930 * 2
def baseEnd_2222930 : Nat := 1141431551299093009851937

theorem tailTrace_2222930 : CollatzResearch.WordTrace tailWord_2222930 prefixEnd_2222930 1141431551299093009851937 := by
  unfold tailWord_2222930
  simp only [CollatzResearch.WordTrace]
  refine ⟨20269229459177932765982561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54051278557807820709286829 20269229459177932765982561)
  ·
    refine ⟨15201922094383449574486921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20269229459177932765982561 15201922094383449574486921)
    ·
      refine ⟨11401441570787587180865191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15201922094383449574486921 11401441570787587180865191)
      ·
        refine ⟨17102162356181380771297787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11401441570787587180865191 17102162356181380771297787)
        ·
          refine ⟨25653243534272071156946681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17102162356181380771297787 25653243534272071156946681)
          ·
            refine ⟨19239932650704053367710011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25653243534272071156946681 19239932650704053367710011)
            ·
              refine ⟨28859898976056080051565017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19239932650704053367710011 28859898976056080051565017)
              ·
                refine ⟨21644924232042060038673763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28859898976056080051565017 21644924232042060038673763)
                ·
                  refine ⟨32467386348063090058010645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21644924232042060038673763 32467386348063090058010645)
                  ·
                    refine ⟨1521908735065457346469249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 32467386348063090058010645 1521908735065457346469249)
                    ·
                      refine ⟨1141431551299093009851937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1521908735065457346469249 1141431551299093009851937)
                      ·
                        rfl

theorem cell23_2222930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 2, 1, 6, 2].length) (baseStart_2222930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2222930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2222930 prefixEnd_2222930 := by exact prefixLift 2222930
  have htrace : WordTrace (prefixWord ++ tailWord_2222930) baseStart_2222930 baseEnd_2222930 := by
    simpa [prefixWord, tailWord_2222930, baseEnd_2222930] using wordTrace_append hprefix tailTrace_2222930
  have hstable : (prefixWord ++ tailWord_2222930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2222930).length < 2 ^ (prefixWord ++ tailWord_2222930).sum := by decide
  have hdescent : baseEnd_2222930 < baseStart_2222930 := by decide
  rcases family_descends (prefixWord ++ tailWord_2222930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2223007 : List Nat := [1, 1, 2, 5, 2, 1, 1, 1, 4, 3, 2]
def baseStart_2223007 : Nat := 118140960795 + 2223007 * 2 ^ 59
def prefixEnd_2223007 : Nat := 4983230072969 + 3 ^ 40 * 2223007 * 2
def baseEnd_2223007 : Nat := 1141471089309489208589083

theorem tailTrace_2223007 : CollatzResearch.WordTrace tailWord_2223007 prefixEnd_2223007 1141471089309489208589083 := by
  unfold tailWord_2223007
  simp only [CollatzResearch.WordTrace]
  refine ⟨81079726257432773214483275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54053150838288515476322183 81079726257432773214483275)
  ·
    refine ⟨121619589386149159821724913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81079726257432773214483275 121619589386149159821724913)
    ·
      refine ⟨91214692039611869866293685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 121619589386149159821724913 91214692039611869866293685)
      ·
        refine ⟨8551377378713612799965033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 91214692039611869866293685 8551377378713612799965033)
        ·
          refine ⟨6413533034035209599973775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8551377378713612799965033 6413533034035209599973775)
          ·
            refine ⟨9620299551052814399960663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6413533034035209599973775 9620299551052814399960663)
            ·
              refine ⟨14430449326579221599940995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9620299551052814399960663 14430449326579221599940995)
              ·
                refine ⟨21645673989868832399911493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14430449326579221599940995 21645673989868832399911493)
                ·
                  refine ⟨4058563873100406074983405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21645673989868832399911493 4058563873100406074983405)
                  ·
                    refine ⟨1521961452412652278118777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4058563873100406074983405 1521961452412652278118777)
                    ·
                      refine ⟨1141471089309489208589083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1521961452412652278118777 1141471089309489208589083)
                      ·
                        rfl

theorem cell23_2223007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 1, 1, 4, 3, 2].length) (baseStart_2223007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2223007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2223007 prefixEnd_2223007 := by exact prefixLift 2223007
  have htrace : WordTrace (prefixWord ++ tailWord_2223007) baseStart_2223007 baseEnd_2223007 := by
    simpa [prefixWord, tailWord_2223007, baseEnd_2223007] using wordTrace_append hprefix tailTrace_2223007
  have hstable : (prefixWord ++ tailWord_2223007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2223007).length < 2 ^ (prefixWord ++ tailWord_2223007).sum := by decide
  have hdescent : baseEnd_2223007 < baseStart_2223007 := by decide
  rcases family_descends (prefixWord ++ tailWord_2223007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2223021 : List Nat := [1, 5, 2, 3, 1, 2, 2, 1, 6]
def baseStart_2223021 : Nat := 118140960795 + 2223021 * 2 ^ 59
def prefixEnd_2223021 : Nat := 4983230072969 + 3 ^ 40 * 2223021 * 2
def baseEnd_2223021 : Nat := 126830919782072461534891

theorem tailTrace_2223021 : CollatzResearch.WordTrace tailWord_2223021 prefixEnd_2223021 126830919782072461534891 := by
  unfold tailWord_2223021
  simp only [CollatzResearch.WordTrace]
  refine ⟨81080236879382053605492917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54053491252921369070328611 81080236879382053605492917)
  ·
    refine ⟨7601272207442067525514961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 81080236879382053605492917 7601272207442067525514961)
    ·
      refine ⟨5700954155581550644136221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7601272207442067525514961 5700954155581550644136221)
      ·
        refine ⟨2137857808343081491551083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5700954155581550644136221 2137857808343081491551083)
        ·
          refine ⟨3206786712514622237326625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2137857808343081491551083 3206786712514622237326625)
          ·
            refine ⟨2405090034385966677994969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3206786712514622237326625 2405090034385966677994969)
            ·
              refine ⟨1803817525789475008496227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2405090034385966677994969 1803817525789475008496227)
              ·
                refine ⟨2705726288684212512744341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1803817525789475008496227 2705726288684212512744341)
                ·
                  refine ⟨126830919782072461534891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2705726288684212512744341 126830919782072461534891)
                  ·
                    rfl

theorem cell23_2223021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 2, 2, 1, 6].length) (baseStart_2223021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2223021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2223021 prefixEnd_2223021 := by exact prefixLift 2223021
  have htrace : WordTrace (prefixWord ++ tailWord_2223021) baseStart_2223021 baseEnd_2223021 := by
    simpa [prefixWord, tailWord_2223021, baseEnd_2223021] using wordTrace_append hprefix tailTrace_2223021
  have hstable : (prefixWord ++ tailWord_2223021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2223021).length < 2 ^ (prefixWord ++ tailWord_2223021).sum := by decide
  have hdescent : baseEnd_2223021 < baseStart_2223021 := by decide
  rcases family_descends (prefixWord ++ tailWord_2223021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2223023 : List Nat := [1, 1, 2, 1, 2, 2, 2, 3, 3, 1, 5]
def baseStart_2223023 : Nat := 118140960795 + 2223023 * 2 ^ 59
def prefixEnd_2223023 : Nat := 4983230072969 + 3 ^ 40 * 2223023 * 2
def baseEnd_2223023 : Nat := 1141479304999961145989009

theorem tailTrace_2223023 : CollatzResearch.WordTrace tailWord_2223023 prefixEnd_2223023 1141479304999961145989009 := by
  unfold tailWord_2223023
  simp only [CollatzResearch.WordTrace]
  refine ⟨81080309825374807947065723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54053539883583205298043815 81080309825374807947065723)
  ·
    refine ⟨121620464738062211920598585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81080309825374807947065723 121620464738062211920598585)
    ·
      refine ⟨91215348553546658940448939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 121620464738062211920598585 91215348553546658940448939)
      ·
        refine ⟨136823022830319988410673409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91215348553546658940448939 136823022830319988410673409)
        ·
          refine ⟨102617267122739991308005057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 136823022830319988410673409 102617267122739991308005057)
          ·
            refine ⟨76962950342054993481003793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 102617267122739991308005057 76962950342054993481003793)
            ·
              refine ⟨57722212756541245110752845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 76962950342054993481003793 57722212756541245110752845)
              ·
                refine ⟨21645829783702966916532317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 57722212756541245110752845 21645829783702966916532317)
                ·
                  refine ⟨8117186168888612593699619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21645829783702966916532317 8117186168888612593699619)
                  ·
                    refine ⟨12175779253332918890549429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8117186168888612593699619 12175779253332918890549429)
                    ·
                      refine ⟨1141479304999961145989009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12175779253332918890549429 1141479304999961145989009)
                      ·
                        rfl

theorem cell23_2223023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 3, 3, 1, 5].length) (baseStart_2223023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2223023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2223023 prefixEnd_2223023 := by exact prefixLift 2223023
  have htrace : WordTrace (prefixWord ++ tailWord_2223023) baseStart_2223023 baseEnd_2223023 := by
    simpa [prefixWord, tailWord_2223023, baseEnd_2223023] using wordTrace_append hprefix tailTrace_2223023
  have hstable : (prefixWord ++ tailWord_2223023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2223023).length < 2 ^ (prefixWord ++ tailWord_2223023).sum := by decide
  have hdescent : baseEnd_2223023 < baseStart_2223023 := by decide
  rcases family_descends (prefixWord ++ tailWord_2223023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2223037 : List Nat := [1, 4, 1, 2, 4, 1, 1, 1, 3, 1, 4]
def baseStart_2223037 : Nat := 118140960795 + 2223037 * 2 ^ 59
def prefixEnd_2223037 : Nat := 4983230072969 + 3 ^ 40 * 2223037 * 2
def baseEnd_2223037 : Nat := 1141486493729124091213945

theorem tailTrace_2223037 : CollatzResearch.WordTrace tailWord_2223037 prefixEnd_2223037 1141486493729124091213945 := by
  unfold tailWord_2223037
  simp only [CollatzResearch.WordTrace]
  refine ⟨81080820447324088338075365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54053880298216058892050243 81080820447324088338075365)
  ·
    refine ⟨15202653833873266563389131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 81080820447324088338075365 15202653833873266563389131)
    ·
      refine ⟨22803980750809899845083697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15202653833873266563389131 22803980750809899845083697)
      ·
        refine ⟨17102985563107424883812773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22803980750809899845083697 17102985563107424883812773)
        ·
          refine ⟨3206809793082642165714895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17102985563107424883812773 3206809793082642165714895)
          ·
            refine ⟨4810214689623963248572343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3206809793082642165714895 4810214689623963248572343)
            ·
              refine ⟨7215322034435944872858515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4810214689623963248572343 7215322034435944872858515)
              ·
                refine ⟨10822983051653917309287773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7215322034435944872858515 10822983051653917309287773)
                ·
                  refine ⟨4058618644370218990982915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10822983051653917309287773 4058618644370218990982915)
                  ·
                    refine ⟨6087927966555328486474373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4058618644370218990982915 6087927966555328486474373)
                    ·
                      refine ⟨1141486493729124091213945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6087927966555328486474373 1141486493729124091213945)
                      ·
                        rfl

theorem cell23_2223037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 1, 1, 3, 1, 4].length) (baseStart_2223037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2223037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2223037 prefixEnd_2223037 := by exact prefixLift 2223037
  have htrace : WordTrace (prefixWord ++ tailWord_2223037) baseStart_2223037 baseEnd_2223037 := by
    simpa [prefixWord, tailWord_2223037, baseEnd_2223037] using wordTrace_append hprefix tailTrace_2223037
  have hstable : (prefixWord ++ tailWord_2223037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2223037).length < 2 ^ (prefixWord ++ tailWord_2223037).sum := by decide
  have hdescent : baseEnd_2223037 < baseStart_2223037 := by decide
  rcases family_descends (prefixWord ++ tailWord_2223037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2223054 : List Nat := [4, 1, 1, 1, 2, 4, 3, 1, 1, 1, 4]
def baseStart_2223054 : Nat := 118140960795 + 2223054 * 2 ^ 59
def prefixEnd_2223054 : Nat := 4983230072969 + 3 ^ 40 * 2223054 * 2
def baseEnd_2223054 : Nat := 1141495222900250524701367

theorem tailTrace_2223054 : CollatzResearch.WordTrace tailWord_2223054 prefixEnd_2223054 1141495222900250524701367 := by
  unfold tailWord_2223054
  simp only [CollatzResearch.WordTrace]
  refine ⟨10135180061032812530180527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 54054293658841666827629477 10135180061032812530180527)
  ·
    refine ⟨15202770091549218795270791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10135180061032812530180527 15202770091549218795270791)
    ·
      refine ⟨22804155137323828192906187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15202770091549218795270791 22804155137323828192906187)
      ·
        refine ⟨34206232705985742289359281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22804155137323828192906187 34206232705985742289359281)
        ·
          refine ⟨25654674529489306717019461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34206232705985742289359281 25654674529489306717019461)
          ·
            refine ⟨4810251474279245009441149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25654674529489306717019461 4810251474279245009441149)
            ·
              refine ⟨1803844302854716878540431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4810251474279245009441149 1803844302854716878540431)
              ·
                refine ⟨2705766454282075317810647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1803844302854716878540431 2705766454282075317810647)
                ·
                  refine ⟨4058649681423112976715971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2705766454282075317810647 4058649681423112976715971)
                  ·
                    refine ⟨6087974522134669465073957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4058649681423112976715971 6087974522134669465073957)
                    ·
                      refine ⟨1141495222900250524701367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6087974522134669465073957 1141495222900250524701367)
                      ·
                        rfl

theorem cell23_2223054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 3, 1, 1, 1, 4].length) (baseStart_2223054 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2223054 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2223054 prefixEnd_2223054 := by exact prefixLift 2223054
  have htrace : WordTrace (prefixWord ++ tailWord_2223054) baseStart_2223054 baseEnd_2223054 := by
    simpa [prefixWord, tailWord_2223054, baseEnd_2223054] using wordTrace_append hprefix tailTrace_2223054
  have hstable : (prefixWord ++ tailWord_2223054).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2223054).length < 2 ^ (prefixWord ++ tailWord_2223054).sum := by decide
  have hdescent : baseEnd_2223054 < baseStart_2223054 := by decide
  rcases family_descends (prefixWord ++ tailWord_2223054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2223063 : List Nat := [1, 1, 3, 2, 1, 1, 2, 2, 2, 2, 6]
def baseStart_2223063 : Nat := 118140960795 + 2223063 * 2 ^ 59
def prefixEnd_2223063 : Nat := 4983230072969 + 3 ^ 40 * 2223063 * 2
def baseEnd_2223063 : Nat := 1141499844226140989488825

theorem tailTrace_2223063 : CollatzResearch.WordTrace tailWord_2223063 prefixEnd_2223063 1141499844226140989488825 := by
  unfold tailWord_2223063
  simp only [CollatzResearch.WordTrace]
  refine ⟨81081768745229894778521843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54054512496819929852347895 81081768745229894778521843)
  ·
    refine ⟨121622653117844842167782765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81081768745229894778521843 121622653117844842167782765)
    ·
      refine ⟨45608494919191815812918537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 121622653117844842167782765 45608494919191815812918537)
      ·
        refine ⟨34206371189393861859688903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45608494919191815812918537 34206371189393861859688903)
        ·
          refine ⟨51309556784090792789533355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34206371189393861859688903 51309556784090792789533355)
          ·
            refine ⟨76964335176136189184300033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51309556784090792789533355 76964335176136189184300033)
            ·
              refine ⟨57723251382102141888225025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 76964335176136189184300033 57723251382102141888225025)
              ·
                refine ⟨43292438536576606416168769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 57723251382102141888225025 43292438536576606416168769)
                ·
                  refine ⟨32469328902432454812126577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 43292438536576606416168769 32469328902432454812126577)
                  ·
                    refine ⟨24351996676824341109094933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 32469328902432454812126577 24351996676824341109094933)
                    ·
                      refine ⟨1141499844226140989488825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 24351996676824341109094933 1141499844226140989488825)
                      ·
                        rfl

theorem cell23_2223063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 2, 2, 2, 6].length) (baseStart_2223063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2223063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2223063 prefixEnd_2223063 := by exact prefixLift 2223063
  have htrace : WordTrace (prefixWord ++ tailWord_2223063) baseStart_2223063 baseEnd_2223063 := by
    simpa [prefixWord, tailWord_2223063, baseEnd_2223063] using wordTrace_append hprefix tailTrace_2223063
  have hstable : (prefixWord ++ tailWord_2223063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2223063).length < 2 ^ (prefixWord ++ tailWord_2223063).sum := by decide
  have hdescent : baseEnd_2223063 < baseStart_2223063 := by decide
  rcases family_descends (prefixWord ++ tailWord_2223063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2223074 : List Nat := [3, 3, 3, 1, 1, 1, 1, 2, 3, 2, 3]
def baseStart_2223074 : Nat := 118140960795 + 2223074 * 2 ^ 59
def prefixEnd_2223074 : Nat := 4983230072969 + 3 ^ 40 * 2223074 * 2
def baseEnd_2223074 : Nat := 1141505492513340446451275

theorem tailTrace_2223074 : CollatzResearch.WordTrace tailWord_2223074 prefixEnd_2223074 1141505492513340446451275 := by
  unfold tailWord_2223074
  simp only [CollatzResearch.WordTrace]
  refine ⟨20270542487047510914293069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54054779965460029104781517 20270542487047510914293069)
  ·
    refine ⟨7601453432642816592859901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20270542487047510914293069 7601453432642816592859901)
    ·
      refine ⟨2850545037241056222322463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7601453432642816592859901 2850545037241056222322463)
      ·
        refine ⟨4275817555861584333483695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2850545037241056222322463 4275817555861584333483695)
        ·
          refine ⟨6413726333792376500225543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4275817555861584333483695 6413726333792376500225543)
          ·
            refine ⟨9620589500688564750338315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6413726333792376500225543 9620589500688564750338315)
            ·
              refine ⟨14430884251032847125507473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9620589500688564750338315 14430884251032847125507473)
              ·
                refine ⟨10823163188274635344130605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14430884251032847125507473 10823163188274635344130605)
                ·
                  refine ⟨4058686195602988254048977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10823163188274635344130605 4058686195602988254048977)
                  ·
                    refine ⟨3044014646702241190536733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4058686195602988254048977 3044014646702241190536733)
                    ·
                      refine ⟨1141505492513340446451275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3044014646702241190536733 1141505492513340446451275)
                      ·
                        rfl

theorem cell23_2223074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 1, 2, 3, 2, 3].length) (baseStart_2223074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2223074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2223074 prefixEnd_2223074 := by exact prefixLift 2223074
  have htrace : WordTrace (prefixWord ++ tailWord_2223074) baseStart_2223074 baseEnd_2223074 := by
    simpa [prefixWord, tailWord_2223074, baseEnd_2223074] using wordTrace_append hprefix tailTrace_2223074
  have hstable : (prefixWord ++ tailWord_2223074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2223074).length < 2 ^ (prefixWord ++ tailWord_2223074).sum := by decide
  have hdescent : baseEnd_2223074 < baseStart_2223074 := by decide
  rcases family_descends (prefixWord ++ tailWord_2223074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2223083 : List Nat := [1, 1, 1, 1, 2, 3, 1, 1, 3, 4, 5]
def baseStart_2223083 : Nat := 118140960795 + 2223083 * 2 ^ 59
def prefixEnd_2223083 : Nat := 4983230072969 + 3 ^ 40 * 2223083 * 2
def baseEnd_2223083 : Nat := 1141510113839230911238733

theorem tailTrace_2223083 : CollatzResearch.WordTrace tailWord_2223083 prefixEnd_2223083 1141510113839230911238733 := by
  unfold tailWord_2223083
  simp only [CollatzResearch.WordTrace]
  refine ⟨81082498205157438194249903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54054998803438292129499935 81082498205157438194249903)
  ·
    refine ⟨121623747307736157291374855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81082498205157438194249903 121623747307736157291374855)
    ·
      refine ⟨182435620961604235937062283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121623747307736157291374855 182435620961604235937062283)
      ·
        refine ⟨273653431442406353905593425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 182435620961604235937062283 273653431442406353905593425)
        ·
          refine ⟨205240073581804765429195069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 273653431442406353905593425 205240073581804765429195069)
          ·
            refine ⟨76965027593176787035948151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 205240073581804765429195069 76965027593176787035948151)
            ·
              refine ⟨115447541389765180553922227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 76965027593176787035948151 115447541389765180553922227)
              ·
                refine ⟨173171312084647770830883341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 115447541389765180553922227 173171312084647770830883341)
                ·
                  refine ⟨64939242031742914061581253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 173171312084647770830883341 64939242031742914061581253)
                  ·
                    refine ⟨12176107880951796386546485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 64939242031742914061581253 12176107880951796386546485)
                    ·
                      refine ⟨1141510113839230911238733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12176107880951796386546485 1141510113839230911238733)
                      ·
                        rfl

theorem cell23_2223083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 1, 3, 4, 5].length) (baseStart_2223083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2223083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2223083 prefixEnd_2223083 := by exact prefixLift 2223083
  have htrace : WordTrace (prefixWord ++ tailWord_2223083) baseStart_2223083 baseEnd_2223083 := by
    simpa [prefixWord, tailWord_2223083, baseEnd_2223083] using wordTrace_append hprefix tailTrace_2223083
  have hstable : (prefixWord ++ tailWord_2223083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2223083).length < 2 ^ (prefixWord ++ tailWord_2223083).sum := by decide
  have hdescent : baseEnd_2223083 < baseStart_2223083 := by decide
  rcases family_descends (prefixWord ++ tailWord_2223083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2223087 : List Nat := [1, 1, 2, 1, 4, 4, 2, 1, 1, 3, 3]
def baseStart_2223087 : Nat := 118140960795 + 2223087 * 2 ^ 59
def prefixEnd_2223087 : Nat := 4983230072969 + 3 ^ 40 * 2223087 * 2
def baseEnd_2223087 : Nat := 1141512167761848895588715

theorem tailTrace_2223087 : CollatzResearch.WordTrace tailWord_2223087 prefixEnd_2223087 1141512167761848895588715 := by
  unfold tailWord_2223087
  simp only [CollatzResearch.WordTrace]
  refine ⟨81082644097142946877395515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54055096064761964584930343 81082644097142946877395515)
  ·
    refine ⟨121623966145714420316093273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81082644097142946877395515 121623966145714420316093273)
    ·
      refine ⟨91217974609285815237069955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 121623966145714420316093273 91217974609285815237069955)
      ·
        refine ⟨136826961913928722855604933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91217974609285815237069955 136826961913928722855604933)
        ·
          refine ⟨25655055358861635535425925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 136826961913928722855604933 25655055358861635535425925)
          ·
            refine ⟨4810322879786556662892361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25655055358861635535425925 4810322879786556662892361)
            ·
              refine ⟨3607742159839917497169271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4810322879786556662892361 3607742159839917497169271)
              ·
                refine ⟨5411613239759876245753907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3607742159839917497169271 5411613239759876245753907)
                ·
                  refine ⟨8117419859639814368630861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5411613239759876245753907 8117419859639814368630861)
                  ·
                    refine ⟨3044032447364930388236573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8117419859639814368630861 3044032447364930388236573)
                    ·
                      refine ⟨1141512167761848895588715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3044032447364930388236573 1141512167761848895588715)
                      ·
                        rfl

theorem cell23_2223087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 2, 1, 1, 3, 3].length) (baseStart_2223087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2223087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2223087 prefixEnd_2223087 := by exact prefixLift 2223087
  have htrace : WordTrace (prefixWord ++ tailWord_2223087) baseStart_2223087 baseEnd_2223087 := by
    simpa [prefixWord, tailWord_2223087, baseEnd_2223087] using wordTrace_append hprefix tailTrace_2223087
  have hstable : (prefixWord ++ tailWord_2223087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2223087).length < 2 ^ (prefixWord ++ tailWord_2223087).sum := by decide
  have hdescent : baseEnd_2223087 < baseStart_2223087 := by decide
  rcases family_descends (prefixWord ++ tailWord_2223087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2223092 : List Nat := [2, 6, 2, 1, 1, 2, 1, 1, 2, 3, 2]
def baseStart_2223092 : Nat := 118140960795 + 2223092 * 2 ^ 59
def prefixEnd_2223092 : Nat := 4983230072969 + 3 ^ 40 * 2223092 * 2
def baseEnd_2223092 : Nat := 1141514735165121376026193

theorem tailTrace_2223092 : CollatzResearch.WordTrace tailWord_2223092 prefixEnd_2223092 1141514735165121376026193 := by
  unfold tailWord_2223092
  simp only [CollatzResearch.WordTrace]
  refine ⟨40541413231062416365663765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54055217641416555154218353 40541413231062416365663765)
  ·
    refine ⟨1900378745206050767140489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 40541413231062416365663765 1900378745206050767140489)
    ·
      refine ⟨1425284058904538075355367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1900378745206050767140489 1425284058904538075355367)
      ·
        refine ⟨2137926088356807113033051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1425284058904538075355367 2137926088356807113033051)
        ·
          refine ⟨3206889132535210669549577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2137926088356807113033051 3206889132535210669549577)
          ·
            refine ⟨2405166849401408002162183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3206889132535210669549577 2405166849401408002162183)
            ·
              refine ⟨3607750274102112003243275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2405166849401408002162183 3607750274102112003243275)
              ·
                refine ⟨5411625411153168004864913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3607750274102112003243275 5411625411153168004864913)
                ·
                  refine ⟨4058719058364876003648685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5411625411153168004864913 4058719058364876003648685)
                  ·
                    refine ⟨1522019646886828501368257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4058719058364876003648685 1522019646886828501368257)
                    ·
                      refine ⟨1141514735165121376026193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1522019646886828501368257 1141514735165121376026193)
                      ·
                        rfl

theorem cell23_2223092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 2, 1, 1, 2, 3, 2].length) (baseStart_2223092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2223092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2223092 prefixEnd_2223092 := by exact prefixLift 2223092
  have htrace : WordTrace (prefixWord ++ tailWord_2223092) baseStart_2223092 baseEnd_2223092 := by
    simpa [prefixWord, tailWord_2223092, baseEnd_2223092] using wordTrace_append hprefix tailTrace_2223092
  have hstable : (prefixWord ++ tailWord_2223092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2223092).length < 2 ^ (prefixWord ++ tailWord_2223092).sum := by decide
  have hdescent : baseEnd_2223092 < baseStart_2223092 := by decide
  rcases family_descends (prefixWord ++ tailWord_2223092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2223097 : List Nat := [1, 2, 1, 3, 1, 3, 1, 3, 3, 3, 2]
def baseStart_2223097 : Nat := 118140960795 + 2223097 * 2 ^ 59
def prefixEnd_2223097 : Nat := 4983230072969 + 3 ^ 40 * 2223097 * 2
def baseEnd_2223097 : Nat := 1141517302568393856463669

theorem tailTrace_2223097 : CollatzResearch.WordTrace tailWord_2223097 prefixEnd_2223097 1141517302568393856463669 := by
  unfold tailWord_2223097
  simp only [CollatzResearch.WordTrace]
  refine ⟨81083008827106718585259545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54055339218071145723506363 81083008827106718585259545)
  ·
    refine ⟨60812256620330038938944659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81083008827106718585259545 60812256620330038938944659)
    ·
      refine ⟨91218384930495058408416989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60812256620330038938944659 91218384930495058408416989)
      ·
        refine ⟨34206894348935646903156371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 91218384930495058408416989 34206894348935646903156371)
        ·
          refine ⟨51310341523403470354734557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34206894348935646903156371 51310341523403470354734557)
          ·
            refine ⟨19241378071276301383025459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 51310341523403470354734557 19241378071276301383025459)
            ·
              refine ⟨28862067106914452074538189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19241378071276301383025459 28862067106914452074538189)
              ·
                refine ⟨10823275165092919527951821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28862067106914452074538189 10823275165092919527951821)
                ·
                  refine ⟨4058728186909844822981933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10823275165092919527951821 4058728186909844822981933)
                  ·
                    refine ⟨1522023070091191808618225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4058728186909844822981933 1522023070091191808618225)
                    ·
                      refine ⟨1141517302568393856463669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1522023070091191808618225 1141517302568393856463669)
                      ·
                        rfl

theorem cell23_2223097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 3, 3, 3, 2].length) (baseStart_2223097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2223097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2223097 prefixEnd_2223097 := by exact prefixLift 2223097
  have htrace : WordTrace (prefixWord ++ tailWord_2223097) baseStart_2223097 baseEnd_2223097 := by
    simpa [prefixWord, tailWord_2223097, baseEnd_2223097] using wordTrace_append hprefix tailTrace_2223097
  have hstable : (prefixWord ++ tailWord_2223097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2223097).length < 2 ^ (prefixWord ++ tailWord_2223097).sum := by decide
  have hdescent : baseEnd_2223097 < baseStart_2223097 := by decide
  rcases family_descends (prefixWord ++ tailWord_2223097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2223214 : List Nat := [4, 1, 2, 2, 1, 3, 2, 1, 2, 5]
def baseStart_2223214 : Nat := 118140960795 + 2223214 * 2 ^ 59
def prefixEnd_2223214 : Nat := 4983230072969 + 3 ^ 40 * 2223214 * 2
def baseEnd_2223214 : Nat := 380525793268323299566877

theorem tailTrace_2223214 : CollatzResearch.WordTrace tailWord_2223214 prefixEnd_2223214 380525793268323299566877 := by
  unfold tailWord_2223214
  simp only [CollatzResearch.WordTrace]
  refine ⟨10135909520960355945908587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 54058184111788565044845797 10135909520960355945908587)
  ·
    refine ⟨15203864281440533918862881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10135909520960355945908587 15203864281440533918862881)
    ·
      refine ⟨11402898211080400439147161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15203864281440533918862881 11402898211080400439147161)
      ·
        refine ⟨8552173658310300329360371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11402898211080400439147161 8552173658310300329360371)
        ·
          refine ⟨12828260487465450494040557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8552173658310300329360371 12828260487465450494040557)
          ·
            refine ⟨4810597682799543935265209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12828260487465450494040557 4810597682799543935265209)
            ·
              refine ⟨3607948262099657951448907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4810597682799543935265209 3607948262099657951448907)
              ·
                refine ⟨5411922393149486927173361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3607948262099657951448907 5411922393149486927173361)
                ·
                  refine ⟨4058941794862115195380021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5411922393149486927173361 4058941794862115195380021)
                  ·
                    refine ⟨380525793268323299566877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4058941794862115195380021 380525793268323299566877)
                    ·
                      rfl

theorem cell23_2223214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 2, 1, 2, 5].length) (baseStart_2223214 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2223214 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2223214 prefixEnd_2223214 := by exact prefixLift 2223214
  have htrace : WordTrace (prefixWord ++ tailWord_2223214) baseStart_2223214 baseEnd_2223214 := by
    simpa [prefixWord, tailWord_2223214, baseEnd_2223214] using wordTrace_append hprefix tailTrace_2223214
  have hstable : (prefixWord ++ tailWord_2223214).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2223214).length < 2 ^ (prefixWord ++ tailWord_2223214).sum := by decide
  have hdescent : baseEnd_2223214 < baseStart_2223214 := by decide
  rcases family_descends (prefixWord ++ tailWord_2223214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
